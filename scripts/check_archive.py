#!/usr/bin/env python3
"""Validate the final archive without accessing original runs or invoking Lean."""
import hashlib,json
from pathlib import Path
from cache_store import checked_cache, sha
ROOT=Path(__file__).resolve().parents[1]
def load(p):return json.loads((ROOT/p).read_text())
def count(p):return len(p.read_text().splitlines())
manifest=ROOT/'SHA256SUMS'
checked=0
for line in manifest.read_text().splitlines():
    digest,name=line.split('  ',1);p=ROOT/name
    assert p.is_file(),name
    assert sha(p)==digest,name
    checked+=1
b=load('evaluation/statistics-benchmark.json');i=load('evaluation/imo-2026.json');p=load('evaluation/papers.json')
assert len(b)==len({r['case'] for r in b})==83
assert sum(r['mode']=='deep' for r in b)==42
for row in b:
    folder=ROOT/'statistics-benchmark'/row['case']/'proof'
    assert sum(count(x) for x in folder.rglob('*.lean'))==row['lean_lines']
for k,row in enumerate(i,1):
    folder=ROOT/'imo-2026'/f'problem{k}'
    assert sum(count(x) for x in (folder/'proof').rglob('*.lean'))==row['lean_lines']
    provenance=json.loads((folder/'actual-run-input/provenance.json').read_text())
    actual=folder/'actual-run-input'/Path(provenance['inputPath']).name
    assert hashlib.sha256(actual.read_bytes()).hexdigest()==provenance['inputHash']
paths={'gaussian':'gaussian','hmc_22':'hmc/theorem-2.2','hmc_v5':'hmc/theorem-5.14','data_thinning':'data-thinning','eills':'eills'}
for row in p:
    folder=ROOT/'papers'/paths[row['case']]
    assert sum(count(x) for x in (folder/'integrated').rglob('*.lean'))==row['lean_lines']
    closure=json.loads((folder/'root-closure.json').read_text())
    assert sum(x['lines'] for x in closure['files'])==row['root_closure_lean_lines']
assert sum(r['unknown_attempts'] for r in i)==17
assert abs(sum(r['unknown_reservation_usd'] for r in i)-2.32940275)<1e-9
assert sum(r['lean_lines'] for r in p)==25137
assert abs(sum(r['cost_usd'] for r in p)-116.629939)<1e-8
print(f'PASS: {checked} file hashes; 83 selected statistics problems, 6 IMO input hashes/line counts, 5 paper package and root-closure inventories. This script does not invoke Lean; see verification/clean-build.json for separate rebuild results.')

report=load('evaluation/report-metrics.json')
keys=('inputTokens','cacheReadTokens','cacheWriteTokens','outputTokens')
rates={'inputTokens':.15,'cacheReadTokens':.003,'cacheWriteTokens':.15,'outputTokens':.60}
assert report['usd_per_million_tokens']==rates
stats=load('evaluation/statistics-offpeak.json');imo=load('evaluation/imo-offpeak.json')
assert [x['case'] for x in stats]==[x['case'] for x in b]
for row in stats+imo:
    evidence=ROOT/row['offpeak_evidence']
    if evidence.name=='observed-usage-callbacks.json':
        events=json.loads(evidence.read_text())['records']
        usage={k:sum(e.get(k,0) for e in events) for k in keys}
        assert usage['inputTokens']==row['legacy_input_tokens']
        assert usage['outputTokens']==row['legacy_output_tokens']
    elif evidence.name=='usage-audit.json':
        recorded=json.loads(evidence.read_text())['totals']['completed']
        usage={k:recorded[k] for k in keys}
    else:
        receipts={}
        for line in evidence.read_text().splitlines():
            event=json.loads(line)
            assert event['kind']!='USAGE_CHECKPOINT'
            if event['kind']=='USAGE_COMPLETION':
                receipt=event['receipt'];key=receipt['requestAttemptId']
                if key in receipts:assert receipts[key]==receipt['usage']
                receipts[key]=receipt['usage']
        usage={k:sum(e.get(k,0) for e in receipts.values()) for k in keys}
    assert usage==row['tokens']
    assert usage['cacheWriteTokens']==0
    assert abs(row['offpeak_usd']-sum(usage[k]*rates[k] for k in keys)/1e6)<1e-9
for label,rows in [('combined',stats),('single_file',[x for x in stats if x['mode']=='single-file']),('deep',[x for x in stats if x['mode']=='deep']),('imo',imo)]:
    usd=sum(x['offpeak_usd'] for x in rows);lines=sum(x['lean_lines'] for x in rows)
    assert abs(report[label]['offpeak_usd']-usd)<1e-9
    assert abs(report[label]['usd_per_line']-usd/lines)<1e-12
sizes=load('evaluation/paper-code-sizes.json');assert len(sizes)==7
for row in sizes:
    folder=ROOT/'papers'/row['case']/'proof' if row['case'] in ('cqr','bh-fdr') else ROOT/'papers'/paths[row['case']]/'integrated'
    files=list(folder.rglob('*.lean'))
    assert len(files)==row['lean_files']
    assert sum(count(f) for f in files)==row['lean_lines']
mapping=load('evaluation/gaussian-structure/figure-mapping.json')
for key,filename,field in [('gaussian-main-dag','main-graph.json','nodes'),('gaussian-task-group','task-group.json','results')]:
    source=load('evaluation/gaussian-structure/'+filename)[field]
    expected=[]
    for node in mapping[key]['nodes']:
        actual=source[node['id']]
        assert node['dependencies']==actual['dependencies'] and node['phase']==actual['phase']
        expected.extend([[d,node['id']] for d in actual['dependencies']])
    assert sorted(expected)==sorted(mapping[key]['edges'])
print('PASS: normalized costs for 83 statistics and 6 IMO cases; seven paper package sizes; both Gaussian dependency projections.')

binary=load('verification/binary-manifest.json')
checked_cache(binary)
verification=load('verification/clean-build.json')
assert verification['complete'] and len(verification['results'])==96
assert verification['binary_manifest_sha256']==sha(ROOT/'verification/binary-manifest.json')
sources={r['key']:r for r in load('verification/minimization.json')}
assert set(sources)=={r['key'] for r in verification['results']}
for result in verification['results']:
    assert result['status']=='compiled'
    files={f['module']:f for f in sources[result['key']]['files']}
    assert set(files)=={m['module'] for m in result['modules']}
    for module in result['modules']:
        source=files[module['module']]
        assert module['exit_code']==0
        assert sha(ROOT/source['derivative'])==module['source_sha256']==source['derivative_sha256']
wrapper=verification['neural']['wrapper']
assert wrapper['status']=='compiled-and-axioms-checked'
assert sha(ROOT/'statlib-contributions/neural-network-approximation/AtResolution.lean')==wrapper['source_sha256']
replay=load('verification/kernel-replay.json')
assert replay['status']=='passed' and replay['binary_manifest_sha256']==verification['binary_manifest_sha256']
assert replay['checker_sha256']==sha(ROOT/'scripts/replay_statlib.lean')
assert all(p['type']=='git' for p in load('lake-manifest.json')['packages'])
assert not (ROOT/'statlib-contributions/neural-network-approximation/Statlib').exists()
assert not (ROOT/'statlib-contributions/neural-network-approximation/public-import-surface.lean').exists()
print('PASS: standalone project binary inventory, source/receipt bindings, replay bindings and private-source exclusions.')
