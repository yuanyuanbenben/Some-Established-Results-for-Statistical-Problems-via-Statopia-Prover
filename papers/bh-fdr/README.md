# bh-fdr curated showcase

This archive retains 4 paper-facing modules (144 physical lines) and 15 fixed supporting modules. The source YAML contains theorem shapes and embedded proof bodies; `proof/` reconstructs their Lean source mechanically. `evidence/source-map.json` records source and reconstructed hashes. This is a curated historical case study, **not a fresh timed or newly compiled experiment**. Fees and runtime are unavailable.

The Dobriban branch uses fixed Appendix B certificates. The Lei branch composes explicit leave-one-out and tail-ratio/common-factor input interfaces. The fifteen seed modules and their dependency graph are retained; the 144-line displayed-node count excludes them.

Module names are preserved. Build only in a separate compatible Lean/Statlib project; this archive does not vendor external libraries.

Recompilation during packaging found that the reconstructed Dobriban endpoint includes copied YAML instructions after its closing proof tactic. That original reconstructed file is retained for provenance and does not compile as-is. The corresponding derivative in `verification/minimal-sources/papers/bh-fdr/proof/` comments out that prose and its alternative example tactics, retains the actual proof and theorem statement, and records the repair in `verification/minimization.json`. The original 144-line displayed-node measurement is a physical count of the raw reconstruction, not a claim that those original bytes form a compilable Lean module.
