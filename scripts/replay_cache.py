#!/usr/bin/env python3
"""Kernel-replay the supplied safe Statlib declarations over pinned public dependencies."""
import argparse
import json
import os
import subprocess
import tempfile
from pathlib import Path
from verify_minimal import sha
from cache_store import checked_cache

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--mathlib-project', type=Path, default=ROOT)
    args = parser.parse_args()
    manifest_path = ROOT / 'verification/binary-manifest.json'
    manifest = json.loads(manifest_path.read_text())
    cache = checked_cache(manifest)
    workspace = Path(tempfile.mkdtemp(prefix='established-replay-'))
    files = {f['path']: f for m in manifest['modules'] for f in m['files']}
    assert all(name.endswith('.olean') for name in files), 'This pinned cache uses whole .olean files'
    env = json.loads(subprocess.check_output(['lake', 'env', 'python3', '-c',
        'import os,json;print(json.dumps(dict(os.environ)))'], cwd=args.mathlib_project, text=True))
    lean = subprocess.check_output(['lake', 'env', 'which', 'lean'], cwd=args.mathlib_project, text=True).strip()
    assert subprocess.check_output([lean, '--version'], text=True).strip() == manifest['lean_version']
    packages = json.loads((args.mathlib_project / 'lake-manifest.json').read_text())['packages']
    assert next(p['rev'] for p in packages if p['name'] == 'mathlib') == manifest['mathlib_revision']
    search = [p for p in env['LEAN_PATH'].split(os.pathsep) if '/.lake/packages/' in p or '/.elan/toolchains/' in p]
    assert not any((Path(p) / n).exists() for p in search for n in ['Statlib', 'Statlib.olean', 'StatAssist', 'StatAssist.olean', 'ProverJobs'])
    env['LEAN_PATH'] = os.pathsep.join([str(cache / 'lib/lean'), *search])
    with (ROOT / 'verification/kernel-replay.log').open('w') as log:
        result = subprocess.run([lean, '--run', str(ROOT / 'scripts/replay_statlib.lean'),
            *[str(cache / p) for p in files]], cwd=workspace, env=env, stdout=log, stderr=subprocess.STDOUT, timeout=600)
    log_text = (ROOT / 'verification/kernel-replay.log').read_text()
    statistics = next((json.loads(line) for line in log_text.splitlines() if line.startswith('{')), None)
    report = dict(status='passed' if result.returncode == 0 else 'failed', exit_code=result.returncode,
        modules=len(files), binary_manifest_sha256=sha(manifest_path), checker_sha256=sha(ROOT / 'scripts/replay_statlib.lean'),
        statistics=statistics, scope='Eligible safe non-partial declarations checked over public Mathlib/Lean imports; axiom declarations admitted, public dependencies not replayed')
    (ROOT / 'verification/kernel-replay.json').write_text(json.dumps(report, indent=2) + '\n')
    assert result.returncode == 0, log_text[-4000:]
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
