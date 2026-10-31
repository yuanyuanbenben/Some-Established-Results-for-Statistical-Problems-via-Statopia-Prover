# IMO 2026 Problem 6: AxiomMath-input guided result

The current selected run is `real_main_theorem_edd06e2c7e6c`, completed on 2026-10-31. It replaces the older separately prepared-input result; [selection-history.json](selection-history.json) identifies the prior Git snapshot and metrics.

- [Published statement](input/problem.lean): byte-identical AxiomMath Q6 at commit c5a6a089d06d3619afe7ff45c5ccab9e2a30d5d2, with MIT attribution.
- [Actual Lean input](actual-run-input/input.lean): only the unsupported backward.isDefEq.respectTransparency option is removed. The definition and main_theorem statement are unchanged.
- [Our mathematical guide](actual-run-input/proof.md): exact existing docs/answer_imo6.md; no published Lean solution is used.
- [Main proof](proof/ProverJobs/real_main_theorem_edd06e2c7e6c/Main.lean) and [14-file / 1,215-line closure](proof/closure.json).
- Fresh job, no restored proof/DAG/checkpoint; five keys x three concurrent calls, LSP/build limits three. Current code context and original configuration are recorded in evidence/launch-record.json.
- Engine time 3,032.394 seconds (50.5399 minutes). Recorded completed fee USD 1.621568242; common frozen off-peak estimate USD 0.810784116. See evidence/usage-audit.json.
- Independent original-source compilation and exact-definition/statement plus root-axiom checks are retained in evidence/. Only propext, Classical.choice and Quot.sound are used by the root; the unused private Base skeleton remains outside its axiom closure.

The standalone reproduction sources in verification/minimal-sources/ remove the unused broad Statlib import, preserving declaration bodies. Their fresh isolated compilation and root axiom receipt supersede the old P6 validation receipt.
