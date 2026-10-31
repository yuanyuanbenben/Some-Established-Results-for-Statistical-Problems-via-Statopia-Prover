#!/usr/bin/env python3
"""Check the current source and binary inventory without stored run receipts."""
from pathlib import Path
import json
from verify import check_cache, digest, ROOT

lines = (ROOT / 'SHA256SUMS').read_text().splitlines()
expected = {}
for line in lines:
    value, name = line.split('  ', 1)
    assert name not in expected
    expected[name] = value
    path = ROOT / name
    assert path.is_file() and not path.is_symlink() and digest(path) == value, name
actual = {p.relative_to(ROOT).as_posix() for p in ROOT.rglob('*') if p.is_file()
    and not any(x in {'.git', '.lake', '__pycache__'} for x in p.relative_to(ROOT).parts)
    and p.name not in {'SHA256SUMS', '.git'}}
assert actual == set(expected), 'Published inventory differs from SHA256SUMS'
check_cache(ROOT / 'verification/statlib-cache', json.loads((ROOT / 'verification/binary-manifest.json').read_text()))
for collection in ['papers', 'statistics-benchmark', 'imo-2026']:
    for package in (ROOT / collection).iterdir():
        if not package.is_dir():
            continue
        assert {p.name for p in package.iterdir()} == {'README.md', 'input', 'proof'}, package
        cfg = json.loads((package / 'proof/build.json').read_text())
        check_cache(package / 'proof/cache', cfg['cache'])
        assert all(t['declaration'] for case in cfg['cases'] for t in case['targets'])
print('PASS:', len(expected), 'file hashes; task layouts and exact binary cache inventories.')
