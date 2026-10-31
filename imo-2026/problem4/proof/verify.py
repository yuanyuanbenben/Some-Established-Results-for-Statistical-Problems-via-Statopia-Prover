#!/usr/bin/env python3
"""Compile the supplied Lean sources using public dependencies and checked caches."""
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
from graphlib import TopologicalSorter
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import tempfile
import threading

if not __debug__:
    raise RuntimeError('Run verification without Python optimization')

HERE = Path(__file__).resolve().parent
ROOT = HERE if (HERE / 'build.json').exists() else HERE.parent
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}

def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()

def local_path(root, relative):
    p = PurePosixPath(relative)
    if p.is_absolute() or '..' in p.parts:
        raise ValueError('Unsafe relative path: ' + relative)
    result = root.joinpath(*p.parts)
    if result.is_symlink() or not result.resolve().is_relative_to(root.resolve()):
        raise ValueError('Unsafe local file: ' + relative)
    return result

def imports(text):
    text = re.sub(r'/-.*?-/', '', text, flags=re.S)
    text = re.sub(r'--[^\n]*', '', text)
    return [s for line in re.findall(r'^\s*(?:public\s+)?import\s+([^\n]+)', text, re.M) for s in line.split()]

def check_cache(root, manifest):
    records = [f for m in manifest['modules'] for f in m['files']]
    expected = {f['path']: f for f in records}
    assert len(expected) == len(records), 'Duplicate binary cache entry'
    actual = set()
    for path in root.rglob('*'):
        assert not path.is_symlink(), 'Cache symlinks are forbidden'
        if path.is_file():
            actual.add(path.relative_to(root).as_posix())
    assert actual == set(expected), 'Binary cache inventory mismatch'
    for name, record in expected.items():
        path = local_path(root, name)
        assert path.stat().st_size == record['bytes'] and digest(path) == record['sha256'], name
    return root / 'lib/lean'

def cases():
    if (ROOT / 'build.json').exists():
        cfg = json.loads((ROOT / 'build.json').read_text())
        yield ROOT, cfg, cfg['cache'], ROOT / 'cache'
    else:
        cfg = json.loads((ROOT / 'build-targets.json').read_text())
        cache = json.loads((ROOT / 'verification/binary-manifest.json').read_text())
        yield ROOT, cfg, cache, ROOT / 'verification/statlib-cache'
        for collection in ['papers', 'statistics-benchmark', 'imo-2026']:
            for p in sorted((ROOT / collection).glob('*/proof/build.json')):
                cfg = json.loads(p.read_text())
                yield p.parent, cfg, cfg['cache'], p.parent / 'cache'

def environment(project):
    env = json.loads(subprocess.check_output(['lake', 'env', 'python3', '-c',
        'import os,json;print(json.dumps(dict(os.environ)))'], cwd=project, text=True))
    lean = subprocess.check_output(['lake', 'env', 'which', 'lean'], cwd=project, text=True).strip()
    search = [p for p in env['LEAN_PATH'].split(os.pathsep) if '/.lake/packages/' in p or '/.elan/toolchains/' in p]
    assert search and not any((Path(p) / n).exists() for p in search
        for n in ['Statlib', 'Statlib.olean', 'StatAssist', 'StatAssist.olean', 'ProverJobs'])
    revision = next(p['rev'] for p in json.loads((project / 'lake-manifest.json').read_text())['packages'] if p['name'] == 'mathlib')
    return env, lean, search, revision

def compile_case(case, folder, cache, env, lean, search, output, slots):
    source = local_path(folder, case['source'])
    out = output / case['key']
    out.mkdir(parents=True)
    scoped = dict(env, LEAN_PATH=os.pathsep.join([str(out), str(cache), *search]))
    modules = {m: local_path(source, m.replace('.', '/') + '.lean') for m in case['modules']}
    graph = {m: {d for d in imports(p.read_text()) if d.startswith('ProverJobs.')} for m, p in modules.items()}
    assert all(d in modules for deps in graph.values() for d in deps), 'Missing Lean module'
    sorter = TopologicalSorter(graph)
    sorter.prepare()
    with ThreadPoolExecutor(max_workers=4) as pool:
        while sorter.is_active():
            ready = sorter.get_ready()
            futures = [pool.submit(compile_module, modules[m], source, out, m, lean, scoped, slots) for m in ready]
            for f in futures:
                f.result()
            sorter.done(*ready)
    for target in case['targets']:
        assert target['module'] in modules
        with slots:
            p = subprocess.run([lean, '--run', str(HERE / 'inspect_module.lean'), target['module'], target['declaration']],
                cwd=source, env=scoped, capture_output=True, text=True, timeout=120)
        assert p.returncode == 0, p.stdout + p.stderr
        declarations = [json.loads(line) for line in p.stdout.splitlines()]
        assert len(declarations) == 1 and declarations[0]['declaration'] == target['declaration'], 'Target mismatch'
        actual = set(declarations[0]['axioms']) - STANDARD
        assert 'sorryAx' not in actual and actual <= set(target['allowedAxioms']), 'Unexpected axioms: ' + str(actual)
        print('AXIOMS', target['declaration'], sorted(actual), flush=True)
    print('PASS', case['key'], len(modules), 'source modules', flush=True)

def compile_module(path, source, out, module, lean, env, slots):
    target = out / (module.replace('.', '/') + '.olean')
    target.parent.mkdir(parents=True, exist_ok=True)
    with slots:
        p = subprocess.run([lean, '-DmaxHeartbeats=2000000', '-o', str(target), str(path.relative_to(source))],
            cwd=source, env=env, capture_output=True, text=True, timeout=300)
    assert p.returncode == 0, str(path) + '\n' + p.stdout + p.stderr

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--mathlib-project', type=Path, default=ROOT)
    parser.add_argument('--workers', type=int, default=8)
    parser.add_argument('--only', action='append', default=[])
    args = parser.parse_args()
    assert 1 <= args.workers <= 12
    env, lean, search, revision = environment(args.mathlib_project)
    version = subprocess.check_output([lean, '--version'], text=True).strip()
    work = []
    for folder, config, manifest, cache in cases():
        assert config['leanVersion'] == version and config['mathlibRevision'] == revision
        selected = [c for c in config['cases'] if not args.only or c['key'] in args.only]
        if selected:
            checked = check_cache(cache, manifest)
            work.extend((c, folder, checked) for c in selected)
    assert work and (not args.only or set(args.only) == {c['key'] for c, _, _ in work}), 'Unknown or empty selection'
    slots = threading.BoundedSemaphore(args.workers)
    with tempfile.TemporaryDirectory(prefix='established-source-build-') as temporary:
        with ThreadPoolExecutor(max_workers=min(8, args.workers)) as pool:
            futures = [pool.submit(compile_case, c, p, cache, env, lean, search, Path(temporary), slots) for c, p, cache in work]
            for f in as_completed(futures):
                f.result()
    print('PASS:', len(work), 'case developments; isolated public dependencies; no saved run history.')

if __name__ == '__main__':
    main()
