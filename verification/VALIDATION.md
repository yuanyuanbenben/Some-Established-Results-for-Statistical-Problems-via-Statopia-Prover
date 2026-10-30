# Archive validation

Current update: **2026-10-31**, adding HulC. The original baseline below covers 96 cases; the current combined report covers **97 cases / 768 modules**. See the final section for the fresh-versus-reused compilation split.

Validation used Linux and Lean 4.28.0-rc1 with Mathlib revision 5352afccd6866369be9de43f5b7ec47203555f44. The initial validation did not upload, deploy, restart proof jobs, or modify the original Statlib workspace. The collection has since been published on GitHub; the source-publication update is recorded below.

## Results

- 83 statistics inputs and complete theorem signatures match their selected original proof entry statements in the bounded static audit. All six IMO targets also match; P3 is `V_eq`. Import graphs and copied source hashes were checked.
- 96 case developments passed source compilation in an isolated search path: 83 statistics, six IMO, five timed paper developments and two curated showcases. Every public target was recursively checked for axioms. The search path excluded original Statlib, StatAssist and ProverJobs builds.
- The first clean compilation checked all 96 sources. Its conservative equality check between retained declarations and actual root axioms flagged an unused EILLS citation. The final report resumes those hash-bound compilation receipts, accepts only actual axiom subsets of the disclosed boundary, and separately performs the neural checks. `clean-build-initial.json` preserves the first report; `clean-build.json` records original receipt provenance. This is one clean source recompilation, not two.
- The selected library binary directory contains 144 modules, 213165544 bytes (203.29 MiB), without the Statlib umbrella or Statlib source.
- Kernel replay accepted 5915 eligible safe non-partial declarations over public Mathlib/Lean. Three unsafe/partial runtime helpers were skipped and listed. Four identical duplicate equation theorems were deduplicated after comparing their complete types, values and universe parameters. The supplied modules declare no axioms. This does not recheck public Mathlib itself or establish that every unused library theorem is sorry-free.
- The new neural `AtResolution.lean` wrapper passed isolated source compilation and recursive axiom inspection; its only axioms are `propext`, `Classical.choice`, `Quot.sound`. It exposes the explicit depth and error dependence on resolution that was missing from the old public type.

## Actual final paper-root boundaries

| Development | Nonstandard root axioms | Retained but unused |
| --- | ---: | ---: |
| papers/bh-fdr | 0 | 0 |
| papers/cqr | 0 | 0 |
| papers/data-thinning | 0 | 0 |
| papers/eills | 0 | 1 |
| papers/gaussian | 3 | 0 |
| papers/hmc/theorem-2.2 | 1 | 0 |
| papers/hmc/theorem-5.14 | 0 | 0 |

Gaussian retains three actual citation assumptions and HMC 2.2 retains one. These remain conditional developments; compilation/replay does not prove those citations. The other paper/showcase roots inspected here have no nonstandard axioms.

## Source and material repairs

Original run sources remain unchanged. Derivatives narrow imports and remove redundant `open _root_.Statlib` scaffolding. One reconstructed BH-FDR file included English YAML instructions and alternative tactic examples after its complete proof; the derivative comments out that prose. The original raw reconstruction and its historical physical-line measurement remain visible as provenance, not as a claim that its original bytes compile.
The neural wrapper returns an existing compiled theorem constant through normal term elaboration; its full explicit target is still checked by Lean. The wrapper itself adds no axiom. The original public signature and library files were preserved.
Paper PDFs and provenance were added. Data Thinning/EILLS PDFs correspond to byte-identical archived TeX. HMC v5 includes the corrigendum. Gaussian and neural author-TeX previews are `pdf-with-errors` because of recorded reference/layout or missing-character diagnostics; original reference PDFs are the reading copies. Retrieved references do not retroactively establish the exact version supplied to every historical experiment.

## Code-quality review

Functional correctness: complete input/entry mappings, actual import graphs, source preservation/explicit repair hashes, isolated compilation, target axiom boundaries, binary-file hashes and private-source exclusions are checked. This is not an exhaustive mathematical faithfulness audit against every original natural-language question or paper.
Memory verdict: OK. The final compiler has a global 12-process limit (roughly 72 GiB at observed 6 GiB per process, within available memory); cache/hash operations stream files. Independent jobs use separate build roots, and dependency-ready modules are bounded within each case.
Other issues: these scripts do not open provider-key files or make proof-provider requests; no live job workspaces are overwritten. Only the seven explicitly authorized neural-network source modules are published; other Statlib implementation sources remain excluded. Local build outputs and Python caches are ignored. Its verification binds the exact compiled-source receipts, binary files, checker and neural wrapper. Cross-platform portability and a from-source rebuild of private Statlib are outside this validation.

## Standalone directory check

The generated outer delivery archive and compressed binary-cache archive were removed. The selected `.olean` files now live directly in `verification/statlib-cache/`, with unchanged bytes and unchanged binary manifest. At that earlier stage, private source snapshots were preserved outside the project, with relocation records in `directory-layout.json`. The seven neural-network modules have now been copied back under the explicit source-publication authorization below. The root Lake configuration uses only public git dependencies and pins the same Lean/Mathlib versions. The root verification and replay commands were exercised on Linux, reusing local caches of those public packages rather than a fresh network download. Case compilation receipts were revalidated by source/binary hashes using `--resume`; the neural wrapper was freshly compiled and inspected, and all selected eligible binary declarations were replayed again. No second full case recompilation is claimed.

## Delivery cleanup

One-time collection/minimization/report-generation scripts, report TeX and revisions, duplicate proof ZIPs, workflow TODO projections and redundant paper previews/logs were moved outside the project. Original question/paper input TeX, PDFs, Lean proofs, compiled dependencies and hash-bound compilation receipts remain. `cleanup.json` records the relocated file hashes and local backup location. Historical provenance destinations are interpreted together with that removal index; `documentation-derivations.json` records edited case READMEs.

Functional correctness: the runtime case index and import reader were extracted unchanged and compared for all 96 cases and 753 derived modules. Proof sources and all binary hashes are unchanged. Inventory/receipt checks cover the retained cases and dependencies; no new full Lean compilation is claimed by this cleanup.
Memory verdict: OK. Cleanup operations move files on the same filesystem, and the retained hash checker streams binary data. Other issues: the runtime verifier imports only retained standard-library Python modules; no collection script or private workspace source is needed.

## Neural-network source publication

The seven neural-network Lean modules listed in `statlib-contributions/neural-network-approximation/metrics.json` are now included at their original module-relative paths. All seven match their archived SHA-256 hashes and line counts (55,922 lines in total). Only this source subset is published; other Statlib dependencies remain binary-only. `make check` enforces the exact seven-file source inventory and hashes, while existing binary-manifest and proof-compilation receipts remain unchanged. No complete source rebuild of these seven modules is claimed by this publication step.

## HulC addition — 2026-10-31

The later HULC v2 Theorem 1 run and its fixed-batch coverage lemma are archived in `papers/hulc/`: 15 byte-identical integrated Lean source modules / 1,468 physical lines, the original Main/Supp TeX, structured inputs, combined paper PDF, generated report PDF, and whitelisted completion/provenance evidence. The case ran from 2026-10-30 14:41:30.627 UTC through 16:14:44.918 UTC (5,594.291 seconds, including report delivery), with exit 0, both tasks verified, canonical group closure/export completed, and report delivery completed. Its timing/cost data is kept outside the original five-paper aggregate; no fee estimate was reconstructed.

All 15 new HULC reproduction modules were **freshly compiled in isolation**. The first Mathlib-only candidate exposed one missing measure-bridge declaration. The final derivative adds only `Statlib.StatFoundation.BasicAnalysis.measure_le_ofReal_of_measureReal_le`, which was already in the existing 144-module cache. No binary manifest or cached file changed. Proof statements/bodies are preserved; allowed changes are narrowed imports and redundant root-namespace openings. The original sources, including two unused Base skeleton placeholders, remain intact.

Recursive inspection of the final integrated root found only `propext`, `Quot.sound` and `Classical.choice`: no external citation axioms or `sorryAx`. The historical Main-stage audit listed the proved child as an approved interface; the integrated-root result resolves it using the child's proof. This was not inferred from process exit, task counts or the absence of placeholder text.

The previous 96 case compilations were **reused after validating their source hashes and the unchanged binary manifest**; they were not all recompiled during this addition. Their complete prior report is preserved in hash-bound receipt history. The combined report has 97 passing cases / 768 modules, with HULC marked as a fresh case. The neural wrapper was freshly compiled and checked again. The existing kernel-replay receipt is unchanged because its binary and checker bytes are unchanged.

The pipeline records `assumptionsAutoAdopted: true`. HULC's actual Lean statement contains explicit modeling hypotheses for measurability, estimator independence, uniform randomization and randomizer independence, partition properties, and data/partition linkage. `papers/hulc/FORMALIZATION.md` makes these visible. No new exhaustive original-paper mathematical-equivalence audit is claimed.

Functional correctness: input/export/provenance hashes, exact 15-module import closure, statement preservation, fresh source compilation and actual root axioms were checked. The expanded resume path compiles the new case and preserves all old cases; the archive check now binds original as well as derivative source hashes. Memory verdict: OK. This addition used two compiler slots (roughly 12 GiB at prior observed process sizes), within the measured available memory. Other issues: no source run, live job, credential, database or runtime checkpoint was modified or copied into the archive; PDF/Lean/material fields were allowlisted.
