"""Enumerate proof cases and read imports for standalone verification."""
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
IMPORT = re.compile(r'^\s*(?:public\s+)?import\s+([^\n]+)', re.M)

def without_comments(text):
    # Explicit repairs are applied separately before the source preservation check.
    return re.sub(r'--[^\n]*', '', re.sub(r'/-.*?-/', '', text, flags=re.S))

def jobs():
    for p in sorted((ROOT / 'statistics-benchmark').glob('*/metrics.json')):
        m = json.loads(p.read_text())
        yield dict(key='statistics/' + m['case'], folder=p.parent / 'proof',
                   entry=('ProverJobs.' + m['job_id'] + '.Main') if m['mode'] == 'deep' else 'Main')
    for p in sorted((ROOT / 'imo-2026').glob('problem*/proof/closure.json')):
        yield dict(key='imo/' + p.parents[1].name, folder=p.parent, entry=json.loads(p.read_text())['entry'])
    for p in sorted((ROOT / 'papers').rglob('root-closure.json')):
        yield dict(key='papers/' + str(p.parent.relative_to(ROOT / 'papers')), folder=p.parent / 'integrated',
                   entry=json.loads(p.read_text())['entry'])
    for name in ['cqr', 'bh-fdr']:
        p = ROOT / 'papers' / name / 'proof'
        entries = [str(f.relative_to(p)).removesuffix('.lean').replace('/', '.')
                   for f in sorted(p.glob('ProverJobs/*/Main.lean'))]
        yield dict(key='papers/' + name, folder=p, entry=entries[-1], entries=entries)

def imports(text):
    return [x for m in IMPORT.finditer(without_comments(text)) for x in m.group(1).split()]
