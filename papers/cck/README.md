# CCK — Gaussian comparison and anti-concentration

Comparison and anti-concentration bounds for maxima of Gaussian random vectors (arXiv:1301.4807v4)

Selected result: Theorem 2, second covariance-only Kolmogorov bound; five supporting paper tasks: smooth comparison, the smooth-max bound, Gaussian anti-concentration, smooth-max derivatives and the composed second-derivative bound.

The constant is chosen before the dimension and depends only on the diagonal variance bounds. The final root retains the Gaussian Stein integration-by-parts citation. The separately included anti-concentration source package retains density, monotonicity and Mills-ratio citation declarations; its checked final target uses only the Mills-ratio citation. The root does not use that task.

| Basic statistic | Value |
| --- | ---: |
| Lean source files | 78 |
| Physical Lean lines | 12,223 |
| Passed / tasks (main + supporting) | 6/6 (1+5) |
| Used external references (main results) | 1 |
| Cached Statlib modules | 122 |

[input/](input/) · [Lean source](proof/src/) · [Targets and build configuration](proof/build.json)

## Main theorem

| Result | Lean declaration | Source |
| --- | --- | --- |
| Theorem 2: covariance-only Kolmogorov bound | `Theorem_2_Comparison_of_distributions_second_conclusion_covariance_only_Kolmogorov_bound_Cprime_Delta_1_3_max_1_log_p_De` | [Result_r3_fd521a8883154f08aed28047a74c89af.lean:20](proof/src/ProverJobs/paper_fresh_20261030t163458307499z_cck_comparison/PaperProofInterfaces/Result_r3_fd521a8883154f08aed28047a74c89af.lean#L20) |

The linked declarations are the public proof entry points. Fully qualified declaration names and checked modules are listed in [proof/build.json](proof/build.json).

`Base.lean` contains definitions and helper proofs; the selected public theorem statements are in the linked `PaperProofInterfaces` files.

The public main theorem calls the complete uniform-constant proof, [`cck_covariance_comparison_uniform` in Base.lean](proof/src/ProverJobs/paper_fresh_20261030t163458307499z_cck_comparison/Base.lean#L1780).

## Supporting tasks

| Task | Lean declaration | Source |
| --- | --- | --- |
| Smooth Gaussian comparison | `paper_ea9c51e8f7d246ef967b6629540eeb01` | [Result_r1_73352fcb8d474f989e9692e64981daf0.lean:17](proof/src/ProverJobs/paper_fresh_20261030t163458307499z_cck_comparison/PaperProofInterfaces/Result_r1_73352fcb8d474f989e9692e64981daf0.lean#L17) |
| Smooth-max approximation bound | `paper_6f9d0d7c54164bfb958847cd7fbf89dc` | [Result_r1_1231042da3b54cff91b1538c5b77997c.lean:16](proof/src/ProverJobs/paper_fresh_20261030t163458307499z_cck_comparison/PaperProofInterfaces/Result_r1_1231042da3b54cff91b1538c5b77997c.lean#L16) |
| Gaussian anti-concentration | `paper_de3065fb922748188f3a0354eba90ed9` | [Result_r1_9c9a51f79a2f4805a37e982e166764fe.lean:18](proof/src/ProverJobs/paper_fresh_20261030t163458307499z_cck_comparison/PaperProofInterfaces/Result_r1_9c9a51f79a2f4805a37e982e166764fe.lean#L18) |
| Smooth-max derivatives and weight bounds | `paper_68f77b4042a84f6999315e1f7b578de2` | [Result_r1_65bf6e2b04054c96ad0fda6183a01452.lean:17](proof/src/ProverJobs/paper_fresh_20261030t163458307499z_cck_comparison/PaperProofInterfaces/Result_r1_65bf6e2b04054c96ad0fda6183a01452.lean#L17) |
| Composed smooth-max second-derivative identity | `paper_a86aea8c92ff4120874a0fdca6db77c5` | [Result_r1_b7b4e65b94494f8bbf721c514662f76e.lean:18](proof/src/ProverJobs/paper_fresh_20261030t163458307499z_cck_comparison/PaperProofInterfaces/Result_r1_b7b4e65b94494f8bbf721c514662f76e.lean#L18) |

## External references used by the main results

The count is the number of distinct external citation axioms in the actual recursive proof dependencies of the selected main theorem(s). A citation used by several main theorems is counted once. Citations used only by independently checked supporting tasks are excluded, together with unused declarations, ordinary library imports and explicit theorem hypotheses. Direct-use links identify proof code. These citations are assumptions, not proofs supplied here.

| Reference | Axiom declaration | Direct proof uses | Selected targets depending on it |
| --- | --- | --- | --- |
| Gaussian Stein integration by parts | [`ext_model_1` (line 25)](proof/src/ProverJobs/job_paper_ea9c51e8f7d246ef967b6629540eeb01/ExternalNodes/Node_6515c10a3b2a6920f75d.lean#L25) | [Node_1854214930_5c94c0df_e3ca69c5.lean:325](proof/src/ProverJobs/job_paper_ea9c51e8f7d246ef967b6629540eeb01/ProvedNodes/Node_1854214930_5c94c0df_e3ca69c5.lean#L325) | Theorem 2: covariance-only Kolmogorov bound; Smooth Gaussian comparison |

### Supporting-task-only citations (excluded from the main count)

The Mills-ratio citation is used by the separately checked anti-concentration task. That task is not called by the final main theorem, so this citation is excluded from the main-theorem count.

| Reference | Axiom declaration | Direct proof uses | Selected targets depending on it |
| --- | --- | --- | --- |
| Gaussian Mills-ratio bounds | [`ext_model_4` (line 16)](proof/src/ProverJobs/job_paper_de3065fb922748188f3a0354eba90ed9/ExternalNodes/Node_103826e30030eda123b2.lean#L16) | [Node_1572792732_43168f8b_9f1c2f60.lean:81](proof/src/ProverJobs/job_paper_de3065fb922748188f3a0354eba90ed9/ProvedNodes/Node_1572792732_43168f8b_9f1c2f60.lean#L81), [Node_486505997_f29df050_c92f1a1a.lean:54](proof/src/ProverJobs/job_paper_de3065fb922748188f3a0354eba90ed9/ProvedNodes/Node_486505997_f29df050_c92f1a1a.lean#L54), [Node_486505997_f29df050_c92f1a1a.lean:61](proof/src/ProverJobs/job_paper_de3065fb922748188f3a0354eba90ed9/ProvedNodes/Node_486505997_f29df050_c92f1a1a.lean#L61), [Node_486505997_f29df050_c92f1a1a.lean:106](proof/src/ProverJobs/job_paper_de3065fb922748188f3a0354eba90ed9/ProvedNodes/Node_486505997_f29df050_c92f1a1a.lean#L106), [Node_486505997_f29df050_c92f1a1a.lean:210](proof/src/ProverJobs/job_paper_de3065fb922748188f3a0354eba90ed9/ProvedNodes/Node_486505997_f29df050_c92f1a1a.lean#L210), [Node_486505997_f29df050_c92f1a1a.lean:256](proof/src/ProverJobs/job_paper_de3065fb922748188f3a0354eba90ed9/ProvedNodes/Node_486505997_f29df050_c92f1a1a.lean#L256) | Gaussian anti-concentration |

### Unused declarations (excluded from the count)

| Reference | Axiom declaration |
| --- | --- |
| Gaussian conditional-probability monotonicity | [`ExternalRevision_58f8b9f8d26309be8849b0e8c1d4cafebaef77ff60fcf2fda372bf76bd1fc229.citation` (line 24)](proof/src/ProverJobs/job_paper_de3065fb922748188f3a0354eba90ed9/ExternalNodes/Node_169d50a09ba170573f49.lean#L24) |
| Density formula for a Gaussian maximum | [`ext_model_1` (line 38)](proof/src/ProverJobs/job_paper_de3065fb922748188f3a0354eba90ed9/ExternalNodes/Node_6515c10a3b2a6920f75d.lean#L38) |
