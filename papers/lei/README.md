# Lei — BH/FDR interfaces

No Universal Multiplicative FDR Bound for the Benjamini–Hochberg Procedure with Correlated Two-Sided Gaussian Tests (arXiv:2607.14812v1)

Selected result: Theorem 3.1 leave-one-out, tail-ratio and explicit-bound interfaces.

The statements retain explicit leave-one-out and tail-ratio/common-factor hypotheses. They are structural theorem interfaces, not an unconditional formalization of the full paper. The checked targets have no nonstandard axioms.

| Basic statistic | Value |
| --- | ---: |
| Lean source files | 17 |
| Physical Lean lines | 2,786 |
| Passed / tasks (main + supporting) | 3/3 (1+2) |
| Used external references (main results) | 0 |
| Cached Statlib modules | 1 |

[input/](input/) · [Lean source](proof/src/) · [Targets and build configuration](proof/build.json)

## Main theorem

| Result | Lean declaration | Source |
| --- | --- | --- |
| Theorem 3.1: final BH/FDR bound interface | `app_lei31_theorem31_endpoint` | [Main.lean:12](proof/src/ProverJobs/app_lei31_theorem31_endpoint/Main.lean#L12) |

The linked declarations are the public proof entry points. Fully qualified declaration names and checked modules are listed in [proof/build.json](proof/build.json).

## Supporting tasks

| Task | Lean declaration | Source |
| --- | --- | --- |
| Leave-one-out FDR bound | `app_lei31_leave_one_out_fdr` | [Main.lean:10](proof/src/ProverJobs/app_lei31_leave_one_out_fdr/Main.lean#L10) |
| Tail-ratio excess bound | `app_lei31_tail_ratio_excess` | [Main.lean:8](proof/src/ProverJobs/app_lei31_tail_ratio_excess/Main.lean#L8) |

Additional checked helper (already included in the retained source; not an additional paper task):

- [Explicit BH/FDR bound display helper](proof/src/ProverJobs/bh_showcase_workspace_seed_15/Main.lean#L118): `lei_theorem31_explicit_bh_fdr_app_display`.

## External references used by the main results

No explicit external citation axioms are retained in this source package.
