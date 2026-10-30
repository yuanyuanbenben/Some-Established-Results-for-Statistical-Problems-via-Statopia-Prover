# HulC — Theorem 1

Paper: *The HulC: Confidence Regions from Convex Hulls*, Arun Kumar Kuchibhotla, Sivaraman Balakrishnan and Larry Wasserman, arXiv:2105.14577v2.

The selected result is Theorem 1 (`thm:coverage-algorithm-known-Delta`): finite-sample coverage of at least `1 - alpha`, plus exact coverage under the stated additional conditions. Its supporting fixed-batch coverage lemma is included as a proved child task.

## Materials and proof entries

| Contents | Location |
| --- | --- |
| Original combined paper PDF, including supplement | [materials/paper.pdf](materials/paper.pdf) |
| Exact Main / Supplement TeX supplied to the run | [source/main.tex](source/main.tex), [source/supp.tex](source/supp.tex) |
| Selected theorem input | [materials/theorems.yaml](materials/theorems.yaml) |
| Fixed-batch lemma input | [materials/fixed-batch-lemma.yaml](materials/fixed-batch-lemma.yaml) |
| Main-task proof reading copy | [Main.lean](Main.lean) |
| Fixed-batch lemma proof reading copy | [task-main/fixed-batch-lemma.lean](task-main/fixed-batch-lemma.lean) |
| Final integrated Lean module tree and entry | [integrated/README.md](integrated/README.md) |
| Root-reachable source inventory | [root-closure.json](root-closure.json) |
| Lean reproduction with narrowed imports | [minimal-sources](../../verification/minimal-sources/papers/hulc/integrated/) |
| Historical generated proof report | [report/report.pdf](report/report.pdf) |
| Formalization assumptions and scope | [FORMALIZATION.md](FORMALIZATION.md) |

The integrated package contains **15 Lean files / 1,468 physical lines**, all reachable from the final entry. Original exported sources remain byte-identical. The separate reproduction copies remove `import Statlib` and redundant root-namespace openings; proof statements and bodies are preserved.

## Validation

The selected run completed with exit code 0, two verified tasks, a closed/exported task-group proof, and completed report delivery. These historical states are recorded in [manifest.json](manifest.json) and [evidence/run-summary.json](evidence/run-summary.json). The historical Main audit treated the fixed-batch child as an approved interface; the integrated proof resolves that interface with the child's actual proof.

Run `make verify` at the project root for source recompilation and final-target axiom inspection. The HULC derivative uses public Mathlib and one narrow measure-bridge import already present in the selected Statlib cache; no binary modules are added. All 15 HULC modules passed fresh isolated compilation on 2026-10-31. The final root uses only `propext`, `Quot.sound` and `Classical.choice`, with no external citation axioms or `sorryAx`. See the [HULC receipt](evidence/verification.json), [complete clean-build report](../../verification/clean-build.json), and [validation scope](../../verification/VALIDATION.md).

The pipeline recorded `assumptionsAutoAdopted: true`. The actual formal statement includes explicit measurability, estimator independence, randomizer independence and data/partition-link hypotheses. These are documented in [FORMALIZATION.md](FORMALIZATION.md); this archive does not claim a new exhaustive mathematical equivalence audit or formalization of every result in the paper.

The [metrics](metrics.json) record the launcher-to-exit interval and package size. This later addition is separate from the original five-paper timing/cost cohort in `evaluation/papers.json`; no fee estimate was reconstructed or added to that cohort. [Source provenance](evidence/source-provenance.json) binds the archived inputs and exported source bytes. No databases, credentials, runtime checkpoints, duplicate proof ZIPs, workflow TODOs or report TeX are included.
