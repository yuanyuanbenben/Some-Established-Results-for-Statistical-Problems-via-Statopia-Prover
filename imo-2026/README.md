# IMO 2026 guided runs

These are supplied-guide formal proof experiments, not autonomous competition results. P3 is the approved `V_eq` target. All six selected problems preserve AxiomMath statement provenance and licenses with documented compiler-compatibility changes. P6 now selects the 2026-10-31 fresh run with our existing mathematical guide; its older input/result is retained in Git history. `actual-run-input/` preserves the exact selected run materials. `proof/closure.json` inventories final local imports.

| Task | Minutes | Files | Lines | Off-peak USD estimate | Historical UNKNOWN reservation USD |
| --- | ---: | ---: | ---: | ---: | ---: |
| [P1](problem1/metrics.json) | 37.63 | 12 | 720 | 0.8790 | 0.0000 |
| [P2](problem2/metrics.json) | 264.93 | 39 | 4406 | 12.9047 | 1.2141 |
| [P3](problem3/metrics.json) | 292.68 | 48 | 7680 | 10.8891 | 1.1153 |
| [P4](problem4/metrics.json) | 36.03 | 12 | 549 | 0.4090 | 0.0000 |
| [P5](problem5/metrics.json) | 23.61 | 11 | 402 | 0.2779 | 0.0000 |
| [P6](problem6/metrics.json) | 50.54 | 14 | 1215 | 0.8108 | 0.0000 |

Prices are normalized from observed tokens at the common off-peak tariff, not obtained by halving historical fee counters. Original fees remain in per-case `metrics.json`; see [repriced data](../evaluation/imo-offpeak.json). Estimated costs omit requests whose terminal usage is unknown. Reservations are not measured charges. Build against compatible historical dependencies; this collection did not rerun six proofs.

Updated publication [Table 3](../evaluation/imo-table3.md) and [LaTeX fragment](../evaluation/imo-table3.tex). P6 replacement provenance and independent validation are in [problem6/README.md](problem6/README.md).
