"""Validate the unpacked, selected Statlib binary dependency directory."""
import hashlib
from pathlib import Path, PurePosixPath

ROOT = Path(__file__).resolve().parents[1]


def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()


def checked_cache(manifest):
    cache = ROOT / 'verification/statlib-cache'
    records = [f for module in manifest['modules'] for f in module['files']]
    expected = {f['path']: f for f in records}
    assert len(expected) == len(records), 'Duplicate binary paths'
    assert cache.is_dir() and not cache.is_symlink(), 'Missing unpacked binary cache'
    actual = set()
    for path in cache.rglob('*'):
        assert not path.is_symlink(), f'Cache symlink: {path}'
        if path.is_file():
            actual.add(path.relative_to(cache).as_posix())
        else:
            assert path.is_dir(), f'Unsupported cache entry: {path}'
    assert actual == set(expected), 'Binary cache inventory differs from binary-manifest.json'
    for name, record in expected.items():
        relative = PurePosixPath(name)
        assert not relative.is_absolute() and '..' not in relative.parts
        assert relative.parts[:2] == ('lib', 'lean')
        path = cache / name
        assert path.stat().st_size == record['bytes'] and sha(path) == record['sha256'], name
    return cache
