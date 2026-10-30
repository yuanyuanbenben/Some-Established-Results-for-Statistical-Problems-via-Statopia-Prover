# Archive validation — 2026-10-30

Validation used Linux and Lean 4.28.0-rc1 with Mathlib revision 5352afccd6866369be9de43f5b7ec47203555f44. No upload, deployment, proof-job restart, or Statlib source modification was performed.

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
The neural wrapper returns an existing compiled theorem constant through normal term elaboration; its full explicit target is still checked by Lean. It adds no axiom and publishes no Statlib implementation source. The original public signature and library files were preserved.
Paper PDFs and provenance were added. Data Thinning/EILLS PDFs correspond to byte-identical archived TeX. HMC v5 includes the corrigendum. Gaussian and neural author-TeX previews are `pdf-with-errors` because of recorded reference/layout or missing-character diagnostics; original reference PDFs are the reading copies. Retrieved references do not retroactively establish the exact version supplied to every historical experiment.

## Code-quality review

Functional correctness: complete input/entry mappings, actual import graphs, source preservation/explicit repair hashes, isolated compilation, target axiom boundaries, binary-file hashes and private-source exclusions are checked. This is not an exhaustive mathematical faithfulness audit against every original natural-language question or paper.
Memory verdict: OK. The final compiler has a global 12-process limit (roughly 72 GiB at observed 6 GiB per process, within available memory); cache/hash operations stream files. Independent jobs use separate build roots, and dependency-ready modules are bounded within each case.
Other issues: these scripts do not open provider-key files or make proof-provider requests; no live job workspaces are overwritten. The standalone project excludes Statlib source snapshots; local build outputs and Python caches are ignored. Its verification binds the exact compiled-source receipts, binary files, checker and neural wrapper. Cross-platform portability and a from-source rebuild of private Statlib are outside this validation.

## Standalone directory check

The generated outer delivery archive and compressed binary-cache archive were removed. The selected `.olean` files now live directly in `verification/statlib-cache/`, with unchanged bytes and unchanged binary manifest. Private source snapshots were preserved outside the project, with relocation records in `directory-layout.json`. The root Lake configuration uses only public git dependencies and pins the same Lean/Mathlib versions. The root verification and replay commands were exercised on Linux, reusing local caches of those public packages rather than a fresh network download. Case compilation receipts were revalidated by source/binary hashes using `--resume`; the neural wrapper was freshly compiled and inspected, and all selected eligible binary declarations were replayed again. No second full case recompilation is claimed.

## Delivery cleanup

One-time collection/minimization/report-generation scripts, report TeX and revisions, duplicate proof ZIPs, workflow TODO projections and redundant paper previews/logs were moved outside the project. Original question/paper input TeX, PDFs, Lean proofs, compiled dependencies and hash-bound compilation receipts remain. `cleanup.json` records the relocated file hashes and local backup location. Historical provenance destinations are interpreted together with that removal index; `documentation-derivations.json` records edited case READMEs.

Functional correctness: the runtime case index and import reader were extracted unchanged and compared for all 96 cases and 753 derived modules. Proof sources and all binary hashes are unchanged. Inventory/receipt checks cover the retained cases and dependencies; no new full Lean compilation is claimed by this cleanup.
Memory verdict: OK. Cleanup operations move files on the same filesystem, and the retained hash checker streams binary data. Other issues: the runtime verifier imports only retained standard-library Python modules; no collection script or private workspace source is needed.
