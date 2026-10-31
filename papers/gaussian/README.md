# Gaussian approximation — Theorem 3.1

Bootstrapping Max Statistics in High Dimensions: Near-Parametric Rates Under Weak Variance Decay and Application to Functional and Multinomial Data

Selected result: Theorem 3.1 (THM:G) and supporting lemmas.

The final theorem retains three external citation assumptions, listed exactly in proof/build.json. These citations are assumed, not proved by this development.

| Basic statistic | Value |
| --- | ---: |
| Lean source files | 88 |
| Physical Lean lines | 15,047 |
| Passed / tasks (main + supporting) | 6/6 (1+5) |
| Used external references (main results) | 3 |
| Cached Statlib modules | 90 |

[input/](input/) · [Lean source](proof/src/) · [Targets and build configuration](proof/build.json)

## Main theorem

| Result | Lean declaration | Source |
| --- | --- | --- |
| Theorem 3.1: Gaussian approximation | `Theorem_3_1_Gaussian_approximation_THM_G` | [Result_r2_2a5e73d910e344948b8ec113203581bb.lean:15](proof/src/ProverJobs/paper_fresh_20261028t224543381z_gaussian/PaperProofInterfaces/Result_r2_2a5e73d910e344948b8ec113203581bb.lean#L15) |

The linked declarations are the public proof entry points. Fully qualified declaration names and checked modules are listed in [proof/build.json](proof/build.json).

`Base.lean` contains definitions and helper proofs; the selected public theorem statements are in the linked `PaperProofInterfaces` files.

## Supporting tasks

| Task | Lean declaration | Source |
| --- | --- | --- |
| Gaussian lower-tail bound for the maximum | `paper_d731a49b3997405b944f72bca5b16eab` | [Result_r1_f28e8eaa4e2044afaa45af4508dffc9f.lean:12](proof/src/ProverJobs/paper_fresh_20261028t224543381z_gaussian/PaperProofInterfaces/Result_r1_f28e8eaa4e2044afaa45af4508dffc9f.lean#L12) |
| Low-dimensional Gaussian approximation term II | `paper_e9c0500526fe4a15b7473a5f9efc21ed` | [Result_r3_7d087e4738994387bedc83094f5d7829.lean:15](proof/src/ProverJobs/paper_fresh_20261028t224543381z_gaussian/PaperProofInterfaces/Result_r3_7d087e4738994387bedc83094f5d7829.lean#L15) |
| Moment bound for standardized coordinate sums | `paper_df5fdc450bf24d85b08215e07b20fdad` | [Result_r4_0820023960264afb835d52f27bac476f.lean:12](proof/src/ProverJobs/paper_fresh_20261028t224543381z_gaussian/PaperProofInterfaces/Result_r4_0820023960264afb835d52f27bac476f.lean#L12) |
| Truncation terms I and III | `paper_82217ff9ed45452ea25ea7588fe2ef01` | [Result_r4_a06a6ac766994714a01a8e915a432c0a.lean:15](proof/src/ProverJobs/paper_fresh_20261028t224543381z_gaussian/PaperProofInterfaces/Result_r4_a06a6ac766994714a01a8e915a432c0a.lean#L15) |
| High-dimensional truncation error bound | `paper_cb04ce35a04d48a9bf96750470ca0eb0` | [Result_r5_ca80b56b6e6d48af8b8eeb22ad6a917d.lean:13](proof/src/ProverJobs/paper_fresh_20261028t224543381z_gaussian/PaperProofInterfaces/Result_r5_ca80b56b6e6d48af8b8eeb22ad6a917d.lean#L13) |

## External references used by the main results

The count is the number of distinct external citation axioms in the actual recursive proof dependencies of the selected main theorem(s). A citation used by several main theorems is counted once. Citations used only by independently checked supporting tasks are excluded, together with unused declarations, ordinary library imports and explicit theorem hypotheses. Direct-use links identify proof code. These citations are assumptions, not proofs supplied here.

| Reference | Axiom declaration | Direct proof uses | Selected targets depending on it |
| --- | --- | --- | --- |
| Rosenthal-type moment inequality | [`ExternalRevision_b6071945cf90850933f075b907c86da3bc0900ed9d0e2c5e428f11284eee47a4.citation` (line 25)](proof/src/ProverJobs/job_paper_df5fdc450bf24d85b08215e07b20fdad/ExternalNodes/Node_0a6b8bd7afa182dd69d9.lean#L25) | [Node_2505675723_75bd9af6_a08a960c.lean:62](proof/src/ProverJobs/job_paper_df5fdc450bf24d85b08215e07b20fdad/ProvedNodes/Node_2505675723_75bd9af6_a08a960c.lean#L62) | Theorem 3.1: Gaussian approximation; Moment bound for standardized coordinate sums; Truncation terms I and III; High-dimensional truncation error bound |
| Sub-exponential tail, moment and MGF equivalences | [`ext_model_2` (line 91)](proof/src/ProverJobs/job_paper_df5fdc450bf24d85b08215e07b20fdad/ExternalNodes/Node_4e38c0b212aeaf238af1.lean#L91) | [Node_2137929089_5f7d7f94_6371220c.lean:23](proof/src/ProverJobs/job_paper_df5fdc450bf24d85b08215e07b20fdad/ProvedNodes/Node_2137929089_5f7d7f94_6371220c.lean#L23), [Node_2505675723_75bd9af6_a08a960c.lean:63](proof/src/ProverJobs/job_paper_df5fdc450bf24d85b08215e07b20fdad/ProvedNodes/Node_2505675723_75bd9af6_a08a960c.lean#L63) | Theorem 3.1: Gaussian approximation; Moment bound for standardized coordinate sums; Truncation terms I and III; High-dimensional truncation error bound |
| Bentkus-type multivariate Berry–Esseen bound | [`ExternalRevision_bb11d988567af52975f2aee092d3dde32f3d1f221c6808fdb6d1bca0ad00547c.citation` (line 27)](proof/src/ProverJobs/job_paper_e9c0500526fe4a15b7473a5f9efc21ed/ExternalNodes/Node_bd6a8ff2ea70e2db0d42.lean#L27) | [Result_r3_7d087e4738994387bedc83094f5d7829.lean:104](proof/src/ProverJobs/paper_fresh_20261028t224543381z_gaussian/PaperProofInterfaces/Result_r3_7d087e4738994387bedc83094f5d7829.lean#L104) | Theorem 3.1: Gaussian approximation; Low-dimensional Gaussian approximation term II; Truncation terms I and III; High-dimensional truncation error bound |
