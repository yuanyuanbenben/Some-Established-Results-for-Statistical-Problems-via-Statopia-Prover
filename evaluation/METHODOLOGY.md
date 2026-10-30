# Measurement definitions

## Statistics benchmark

Selection was confirmed by the user: take the 83 distinct native records in `benchmark_run/analysis/over_one_hour_20261017T080835Z/all_cases.json`, replacing the 42 matching cases with the completed `deep_benchmark42_3p_2k5_20261017T100521Z` run. The 42 were selected by historical native time greater than one hour, not by best current runtime. All case IDs are unique. No Archon results are mixed into the Statopia table.

Historical native `metrics.time` / `totalAttemptMs` is the timing source for the remaining 41 cases. Deep uses the audited per-case wrapper interval from the comparison CSV (rounded to seconds there). These are historical measurements with different versions and resource configurations. The combined average is descriptive, not a matched controlled comparison. The archived model for these runs is DeepSeek-V4-Flash.

The legacy 41 records retain `metricsComplete=false`: the old dispatch-versus-callback reconciliation did not certify complete provider accounting. However, their raw `proof_log.jsonl` contains 1,243 valid `track_b_usage_callback` events. Summed callback input/output matches every selected case's saved metrics exactly; cache-read counters are also present. Filtered callbacks and original log hashes are now archived under each case's `evidence/observed-usage-callbacks.json`. They support an **observed-usage estimate**, not an assertion of complete billing. No dispatch counters are added on top of these callbacks. Totals: 21,804,825 uncached input, 11,564,032 cache-read, 9,505,435 output, zero cache-write tokens.

Deep cost comes from the checkpoint-aware audited usage journal aggregate. A journal checkpoint contains cumulative completed usage; summing only visible completion events loses that prefix, and summing the prefix plus duplicated events would overcount. The preserved audit records retain the checkpoint totals and pending attempts. The recorded completed cost is $75.832149966. Four unresolved requests have $2.0837925 in reservations. Reservations are not charges and are not guaranteed upper bounds. The original `aggregate.json` preserves this first-version recorded-cost scope (42 cases). The revised paper instead uses `report-metrics.json` and the `*-offpeak.csv/json` files, with observed-usage estimates for all 83 cases; do not substitute the historical aggregate for these normalized figures.

## Common off-peak pricing and hardware

The revised report normalizes observed tokens using the official DeepSeek USD off-peak tariff accessed on 2026-10-30: $0.15 / million uncached input, $0.003 / million cache-read input, and $0.60 / million output tokens. Source: https://api-docs.deepseek.com/quick_start/pricing/ . All selected records use the model identifier `deepseek-v4-flash`; the identifier does not independently pin an immutable underlying model revision. Cache-write tokens are zero in all repriced cases. Input tokens here are uncached input, so cache-read tokens are charged separately, not subtracted twice.

The one-time repricing step read per-case legacy callbacks, checkpoint-aware Deep audits, and deduplicated IMO completion receipts. It preserved old recorded fees and added normalized estimates in separate outputs. A change in tariff means normalization is **not** equivalent to dividing every historical fee by two: the IMO historical fee counters used a different rate. Report totals are $46.924751616 for the 83 statistics cases and $25.658736720 for six IMO cases. Unknown requests have no measured token use and are excluded; reservations remain historical budget data, not normalized charges. Ratios are pooled fee / pooled lines, never the unweighted average of case ratios.

The CPU of the current local evaluation host, read from `lscpu`, is Intel Xeon Platinum 8368 CPU @ 2.40 GHz. The historical manifests do not record CPU models; pending user confirmation, the paper explicitly describes the **current host**, not verified hardware provenance for every archived run.

The Archon comparison uses exactly the 35 records selected by `archon_in_35_timing_comparison=True` in the existing audited comparison CSV. `archon-time-comparison.json` preserves paired times, cohort identity and source hash. Mean Deep/Archon elapsed times are 71.95/79.89 minutes, with 9.94% lower aggregate Deep time. This historical comparison is descriptive, not a resource-matched causal experiment, and is not extended to all 83 statistics cases.

## IMO

Exactly one archived guided run is selected for each of P1–P6. `actual-run-input/` contains the metadata-selected Lean input (SHA-256 checked), supplied mathematical proof and initial route when present. Parent-directory statements/proofs are also retained under `input/` with provenance and available licensing; those are not substituted for the actual run input. P3's target is `V_eq`.

Time is `done.finishedAt - metadata.startedAt`, excluding guide preparation, startup outside that interval and independent post-run rebuilding. These six journals have no compaction checkpoints. Completion receipts are deduplicated by request-attempt identity; unresolved intent/UNKNOWN pairs are retained separately. The $17.773732976 recorded completed usage excludes 17 UNKNOWN attempts: nine for P2 ($1.214112624 reservation) and eight for P3 ($1.115290126). These historical fees remain in the original JSON. The revised table uses the normalized off-peak estimates described above; neither series is a reconciled invoice cost.

## Paper developments

The revised paper displays **only Files and Lines** for this cohort. The historical timing and fee derivations below are retained for archival provenance and are not shown in the paper table.

The five selected targets come from the existing `20261030-gaussian-hmc-thinning-eills` archive. Its source papers, source hashes, task lists, separate reading copies, integrated modules and report PDFs are preserved. The superseded README and duplicate ZIPs are in the local cleanup backup. Task counts are registry entries, not internal DAG-node counts.

Time is the earliest recorded `run.start` through the case's final `exit.json`, including pauses/resume/recovery and delivery in that interval. We do not add nested `run.end.durationMs` values because those intervals can overlap. This is campaign elapsed time, not pure compute or proof-engine time. Costs use every usage row in each case's isolated `server.sqlite`, through the same final-exit second, with all main and child jobs included once. Only whitelisted usage fields are exported; databases, user records and credentials are not copied. Receipt identities are checked for duplicates. Costs after that endpoint remain separate: Gaussian $0.467585. Fee records may include preparation, failed attempts, recovery and report generation in the interval. Completeness against provider invoices and outstanding requests was not established from these database rows.

Per the user's explicit choice, paper cost per line uses **the complete integrated archive package**, not only the final root import closure. HMC 5.14 therefore uses 51 files / 3,345 lines, while its root closure is 36 files / 2,600 lines. Both inventories are retained. The other four package sizes match their root import closure sizes. Total package source is 25,137 lines and recorded through-exit usage $116.629939, yielding $0.0046397716 per line. `unknown_reservation_usd=null` means not measured for this cohort, not zero.

Retained citation-input counts describe the package export, not a fresh `#print axioms` traversal of the composed root. In particular, EILLS has one retained interface although its saved task-level audit reports no external axioms for that task's root. Root acceptance, package inventory, original-source fidelity and report delivery remain distinct. Unused/private declarations can contain placeholders without demonstrating that the accepted theorem uses them; conversely, a zero-sorry summary does not establish whole-source purity.

## CQR and BH/FDR

The current curated fixture YAML includes theorem shapes and embedded proof bodies. Sources under `proof/` are mechanically reconstructed by substituting those proof bodies for the designated placeholders; the input YAML and per-file source map are retained. These are not newly run or newly accepted proof experiments. CQR has six displayed modules / 388 physical lines. BH/FDR has four displayed modules / 144 lines plus fifteen fixed support modules; the revised table counts its **full nineteen-module package / 2,988 lines**, consistently including support sources. This recount supersedes old display-format counts of 381 and 148; it does not represent new mathematical work. Their timing/fees are unavailable; UI expected-time values are not measurements.

## Lines and costs

Individual theorem counts include each source module in the final local import closure once. Single-file cases count their selected `proof_final.lean`. Paper counts use the full integrated source package by user choice. Input snapshots, duplicate reading copies, ZIP contents, failed drafts and repeated snapshots are excluded from the denominator. Physical lines include comments, blanks and provided definitions. Installed Mathlib/Statlib imports are excluded from generated-artifact counts. Shared code across distinct runs is not deduplicated across cases: each run has its own artifact and expense.

For any cost-observed cohort, pooled USD/line is total recorded cost divided by total corresponding lines, not the mean of case ratios. The separately archived neural-network contribution is explicitly a seven-module library snapshot (55,922 lines), not one run's output. It has no reconstructed time or cost.

## Validation boundary

The measurement checks verify copy hashes, source inventory, local import closure, input hashes, existing terminal evidence and aggregation; they do not replay provider calls. Separate current compilation and kernel-replay evidence is described in [VALIDATION.md](../verification/VALIDATION.md). The neural public endpoint received a current compiled-interface check with `lake env lean`; its axiom report contains only `propext`, `Classical.choice`, and `Quot.sound`. That check loads the existing compiled library rather than rebuilding the seven source modules. Source placeholder scans are separate evidence. Original source documents and fixed specifications still require mathematical fidelity review.

Report-writing sources, earlier revisions and previews were moved outside this proof project. The data tables and original measurement evidence remain. See [cleanup records](../verification/cleanup.json).

## Later paper addition: HulC

HulC Theorem 1 and its fixed-batch lemma were archived on 2026-10-31 as a subsequent result. [Per-case metrics](../papers/hulc/metrics.json) record 15 integrated modules, 1,468 lines and the case-launcher-to-final-exit interval. HULC is included in the current package-size inventory and source verification, while the original five-paper timing/fee tables and their historical aggregates remain unchanged. No HULC fee estimate was reconstructed; the main-payload and group-summary token counters have different scopes and are not summed.
