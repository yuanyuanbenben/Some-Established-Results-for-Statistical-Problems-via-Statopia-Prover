#!/usr/bin/env python3
"""Clean-build derivatives using only bundled Statlib binaries and public dependencies."""
import argparse
import concurrent.futures
import hashlib
import json
import os
import subprocess
import tempfile
import threading
from graphlib import TopologicalSorter
from pathlib import Path
from case_index import jobs, imports
from cache_store import checked_cache

ROOT = Path(__file__).resolve().parents[1]


def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()


def target_for(job):
    if job['key'].startswith('statistics/'):
        return job['key'].split('/', 1)[1]
    if job['key'].startswith('imo/'):
        return json.loads((job['folder'].parent / 'metrics.json').read_text())['target']
    manifest = job['folder'].parent / 'manifest.json'
    return json.loads(manifest.read_text())['rootDeclaration'] if manifest.exists() else ''


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--mathlib-project', type=Path, default=ROOT)
    parser.add_argument('--workers', type=int, default=12)
    parser.add_argument('--resume', action='store_true')
    args = parser.parse_args()
    assert 1 <= args.workers <= 16
    manifest_path = ROOT / 'verification/binary-manifest.json'
    manifest_bytes = manifest_path.read_bytes()
    manifest = json.loads(manifest_bytes)
    manifest_digest = hashlib.sha256(manifest_bytes).hexdigest()
    cache = checked_cache(manifest)
    workspace = Path(tempfile.mkdtemp(prefix='established-clean-'))
    base = json.loads(subprocess.check_output(['lake', 'env', 'python3', '-c',
        'import os,json;print(json.dumps(dict(os.environ)))'], cwd=args.mathlib_project, text=True))
    lean = subprocess.check_output(['lake', 'env', 'which', 'lean'], cwd=args.mathlib_project, text=True).strip()
    assert manifest['lean_version'] == subprocess.check_output([lean, '--version'], text=True).strip()
    dependency_manifest = json.loads((args.mathlib_project / 'lake-manifest.json').read_text())
    assert next(p['rev'] for p in dependency_manifest['packages'] if p['name'] == 'mathlib') == manifest['mathlib_revision']
    # Retain only public Lake packages and the toolchain. Never retain the project's build dir.
    search = [p for p in base['LEAN_PATH'].split(os.pathsep)
              if '/.lake/packages/' in p or '/.elan/toolchains/' in p]
    assert search
    assert not any((Path(p) / name).exists() for p in search
                   for name in ['Statlib.olean', 'Statlib', 'StatAssist.olean', 'StatAssist', 'ProverJobs'])
    cache_path = cache / 'lib/lean'
    source_results = json.loads((ROOT / 'verification/minimization.json').read_text())
    work = {j['key']: j for j in jobs()}
    assert set(work) == {r['key'] for r in source_results}
    compile_slots = threading.BoundedSemaphore(args.workers)
    previous_by_key = {}
    report_path = ROOT / 'verification/clean-build.json'
    if args.resume and report_path.exists():
        previous = json.loads(report_path.read_text())
        resumed_from = dict(workspace=previous['workspace'], report_sha256=sha(report_path))
        assert previous['complete'] and previous['binary_manifest_sha256'] == manifest_digest
        previous_by_key = {r['key']: r for r in previous['results']}
        assert set(previous_by_key) == set(work)
        receipt = ROOT / 'verification/receipt-history' / (resumed_from['report_sha256'] + '.json')
        receipt.parent.mkdir(exist_ok=True)
        receipt.write_bytes(report_path.read_bytes())
        resumed_from['report'] = receipt.relative_to(ROOT).as_posix()

    def check_boundary(result, job):
        standard = {'propext', 'Classical.choice', 'Quot.sound'}
        external = {a for declaration in result['axioms'] for a in declaration['axioms']} - standard
        paper_manifest = job['folder'].parent / 'manifest.json'
        allowed = set()
        if paper_manifest.exists():
            allowed = {a.split(' (consumer ')[0] for a in
                json.loads(paper_manifest.read_text())['actualRetainedAssumptions']}
        result['retained_external_axioms'] = sorted(allowed)
        result['actual_external_axioms'] = sorted(external)
        result['retained_but_not_used'] = sorted(allowed - external)
        result['status'] = 'compiled' if external <= allowed else 'axiom-boundary-mismatch'
        return result

    def verify(record):
        job = work[record['key']]
        previous = previous_by_key.get(record['key'])
        if previous and previous['status'] in {'compiled', 'axiom-boundary-mismatch'}:
            old_sources = {m['module']: m for m in previous['modules']}
            assert set(old_sources) == {s['module'] for s in record['files']}
            assert all(old_sources[s['module']]['exit_code'] == 0 and
                sha(ROOT / s['derivative']) == old_sources[s['module']]['source_sha256'] == s['derivative_sha256']
                for s in record['files'])
            previous['resumed_compilation_receipt'] = True
            return check_boundary(previous, job)
        build = workspace / record['key']
        build.mkdir(parents=True)
        env = dict(base, LEAN_PATH=os.pathsep.join([str(build), str(cache_path), *search]))
        result = dict(key=record['key'], status='compiled', modules=[], axioms=[])
        source_root = ROOT / 'verification/minimal-sources' / job['folder'].relative_to(ROOT)
        def compile_module(source):
            path = ROOT / source['derivative']
            assert sha(path) == source['derivative_sha256']
            output = build / (source['module'].replace('.', '/') + '.olean')
            output.parent.mkdir(parents=True, exist_ok=True)
            with compile_slots:
                p = subprocess.run([lean, '-DmaxHeartbeats=2000000', '-o', str(output), str(path.relative_to(source_root))],
                                   cwd=source_root, env=env, capture_output=True, text=True, timeout=240)
            log = p.stdout + p.stderr
            output.with_suffix('.log').write_text(log)
            return dict(module=source['module'], exit_code=p.returncode, source_sha256=sha(path)), log

        sources = {s['module']: s for s in record['files']}
        graph = {m: {d for d in imports((ROOT / s['derivative']).read_text()) if d.startswith('ProverJobs.')}
                 for m, s in sources.items()}
        assert all(d in sources for ds in graph.values() for d in ds)
        sorter = TopologicalSorter(graph)
        sorter.prepare()
        with concurrent.futures.ThreadPoolExecutor(max_workers=4) as module_pool:
            while sorter.is_active():
                ready = sorter.get_ready()
                batch = list(module_pool.map(compile_module, [sources[m] for m in ready]))
                for module_result, log in batch:
                    result['modules'].append(module_result)
                    if module_result['exit_code']:
                        result.update(status='failed', error=log[-8000:])
                if result['status'] != 'compiled':
                    return result
                sorter.done(*ready)
        for entry in record.get('entries', [record['entry']]):
            with compile_slots:
                p = subprocess.run([lean, '--run', str(ROOT / 'scripts/inspect_module.lean'), entry, target_for(job)],
                                   cwd=source_root, env=env, capture_output=True, text=True, timeout=120)
            if p.returncode:
                result.update(status='axiom-inspection-failed', error=(p.stdout + p.stderr)[-8000:])
                return result
            axioms = [json.loads(line) for line in p.stdout.splitlines()]
            if any('sorryAx' in a['axioms'] for a in axioms):
                result['status'] = 'sorry-dependent'
            result['axioms'].extend(axioms)
        return check_boundary(result, job)

    results = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
        pending = {pool.submit(verify, r): r['key'] for r in source_results}
        for future in concurrent.futures.as_completed(pending):
            try:
                result = future.result()
            except Exception as error:
                result = dict(key=pending[future], status='failed', error=str(error))
            results.append(result)
            print(result['status'], result['key'], flush=True)
            assert sha(manifest_path) == manifest_digest, 'Binary manifest changed during verification'
            output = dict(workspace=str(workspace), binary_manifest_sha256=manifest_digest,
                          compiler_options=dict(maxHeartbeats=2000000),
                          dependency_search_paths=search, results=sorted(results, key=lambda r: r['key']),
                          expected_cases=len(work), complete=False)
            if previous_by_key:
                output['resumed_from'] = resumed_from
            (ROOT / 'verification/clean-build.json').write_text(json.dumps(output, indent=2) + '\n')
    assert all(r['status'] == 'compiled' for r in results), 'See verification/clean-build.json'
    neural_module = 'Statlib.Nonparametric.Approximation.ShallowReLUApproximation'
    env = dict(base, LEAN_PATH=os.pathsep.join([str(cache_path), *search]))
    neural = subprocess.run([lean, '--run', str(ROOT / 'scripts/inspect_module.lean'), neural_module,
        'holder_smooth_shallow_relu_neural_network_approximation'], cwd=workspace, env=env,
        capture_output=True, text=True, timeout=120)
    assert neural.returncode == 0, neural.stdout + neural.stderr
    report = [json.loads(line) for line in neural.stdout.splitlines()]
    assert report and all(set(r['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'} for r in report)
    output['neural'] = dict(status='interface-and-axioms-checked', module=neural_module, declarations=report)
    neural_source = ROOT / 'statlib-contributions/neural-network-approximation/AtResolution.lean'
    neural_build = workspace / 'neural'
    neural_build.mkdir()
    env['LEAN_PATH'] = str(neural_build) + os.pathsep + env['LEAN_PATH']
    wrapper = subprocess.run([lean, '-DmaxHeartbeats=2000000', '-o', str(neural_build / 'AtResolution.olean'), 'AtResolution.lean'],
        cwd=neural_source.parent, env=env, capture_output=True, text=True, timeout=120)
    assert wrapper.returncode == 0, wrapper.stdout + wrapper.stderr
    wrapper_report = subprocess.run([lean, '--run', str(ROOT / 'scripts/inspect_module.lean'), 'AtResolution',
        'established_holder_smooth_relu_at_resolution'], cwd=neural_build, env=env,
        capture_output=True, text=True, timeout=120)
    assert wrapper_report.returncode == 0, wrapper_report.stdout + wrapper_report.stderr
    declarations = [json.loads(line) for line in wrapper_report.stdout.splitlines()]
    assert declarations and all(set(r['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'} for r in declarations)
    output['neural']['wrapper'] = dict(status='compiled-and-axioms-checked', source_sha256=sha(neural_source),
        declarations=declarations, olean_sha256=sha(neural_build / 'AtResolution.olean'))
    output['complete'] = True
    (ROOT / 'verification/clean-build.json').write_text(json.dumps(output, indent=2) + '\n')
    mode = 'hash-matched compilation receipts' if previous_by_key else 'fresh case builds'
    print(f'PASS: {len(results)} {mode}; neural wrapper freshly compiled; no original Statlib/ProverJobs path.')


if __name__ == '__main__':
    main()
