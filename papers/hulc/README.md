# HulC — Theorem 1

The HulC: Confidence Regions from Convex Hulls (arXiv:2105.14577v2)

Selected result: Theorem 1, finite-sample coverage and the additional exact-coverage conclusion; fixed-batch coverage lemma.

The final theorem has no nonstandard axioms. Its explicit hypotheses include measurability, estimator and randomizer independence, the median-bias bound and the data/partition links. These modeling hypotheses remain part of the statement.

| Basic statistic | Value |
| --- | ---: |
| Lean source files | 15 |
| Physical Lean lines | 1,397 |
| Passed / tasks (main + supporting) | 2/2 (1+1) |
| Used external references (main results) | 0 |
| Cached Statlib modules | 1 |

[input/](input/) · [Lean source](proof/src/) · [Targets and build configuration](proof/build.json)

## Main theorem

| Result | Lean declaration | Source |
| --- | --- | --- |
| Theorem 1: randomized HulC coverage | `Theorem_1_thm_coverage_algorithm_known_Delta_HulC_finite_sample_coverage_and_exact_coverage_under_the_stated_additional` | [Result_r1_f59ddd7685054a2c91a43999dd384b62.lean:13](proof/src/ProverJobs/paper_fresh_20261030t143835550708z_hulc/PaperProofInterfaces/Result_r1_f59ddd7685054a2c91a43999dd384b62.lean#L13) |

The linked declarations are the public proof entry points. Fully qualified declaration names and checked modules are listed in [proof/build.json](proof/build.json).

`Base.lean` contains definitions and helper proofs; the selected public theorem statements are in the linked `PaperProofInterfaces` files.

## Supporting tasks

| Task | Lean declaration | Source |
| --- | --- | --- |
| Fixed-batch hull coverage bound | `paper_6093c8cdedac44ebaae3246c2f49ba3b` | [Result_r1_6db03351f5d34ffeb979aa1f3d18ae44.lean:12](proof/src/ProverJobs/paper_fresh_20261030t143835550708z_hulc/PaperProofInterfaces/Result_r1_6db03351f5d34ffeb979aa1f3d18ae44.lean#L12) |

## External references used by the main results

No explicit external citation axioms are retained in this source package.
