# Hamiltonian Monte Carlo

On the Geometric Ergodicity of Hamiltonian Monte Carlo (arXiv:1601.08057v5, including corrigendum)

Selected result: Theorem 2.2 (i), (ii), and corrected Theorem 5.14.

Theorem 2.2 retains one external citation assumption. Corrected Theorem 5.14 has no nonstandard axioms and uses the corrigendum condition (18), norm(y) >= 3 norm(x). The two targets are separate source namespaces within this paper directory.

| Basic statistic | Value |
| --- | ---: |
| Lean source files | 73 |
| Physical Lean lines | 7,214 |
| Passed / tasks (main + supporting) | 8/8 (2+6) |
| Used external references (main results) | 1 |
| Cached Statlib modules | 2 |

[input/](input/) · [Lean source](proof/src/) · [Targets and build configuration](proof/build.json)

## Main theorem

| Result | Lean declaration | Source |
| --- | --- | --- |
| Theorem 2.2 (i–ii) | `Theorem_2_2_thm_negative_both_parts_i_and_ii_using_v5_with_corrigendum` | [Result_r2_efa8fa985bbe48fe90bebe042f1092ee.lean:14](proof/src/theorem-2.2/ProverJobs/paper_fresh_20261028t224543381z_hmc_22/PaperProofInterfaces/Result_r2_efa8fa985bbe48fe90bebe042f1092ee.lean#L14) |
| Corrected Theorem 5.14 | `Theorem_5_14_corrected_statement_and_replacement_proof_in_the_v5_corrigendum_Appendix_D_original_label_thm_light_Use_the` | [Result_r2_388b741cbe374909a3f9937f201e99fc.lean:14](proof/src/theorem-5.14/ProverJobs/paper_fresh_20261028t151409527z_hmc_v5/PaperProofInterfaces/Result_r2_388b741cbe374909a3f9937f201e99fc.lean#L14) |

The linked declarations are the public proof entry points. Fully qualified declaration names and checked modules are listed in [proof/build.json](proof/build.json).

`Base.lean` contains definitions and helper proofs; the selected public theorem statements are in the linked `PaperProofInterfaces` files.

## Supporting tasks

| Task | Lean declaration | Source |
| --- | --- | --- |
| Essential supremum one for rejection rules out geometric ergodicity | `paper_a9a2ab5d4e094509b2cdb371b3b02f1c` | [Result_r1_4598ba3bbe264fd0ae3ec2dd30307767.lean:12](proof/src/theorem-5.14/ProverJobs/paper_fresh_20261028t151409527z_hmc_v5/PaperProofInterfaces/Result_r1_4598ba3bbe264fd0ae3ec2dd30307767.lean#L12) |
| Multi-step leapfrog position-norm growth | `paper_a62240be95074e8caf07c24daf22159a` | [Result_r1_5dd9cd994d2449adb01d0a0f42b38c45.lean:11](proof/src/theorem-5.14/ProverJobs/paper_fresh_20261028t151409527z_hmc_v5/PaperProofInterfaces/Result_r1_5dd9cd994d2449adb01d0a0f42b38c45.lean#L11) |
| Acceptance probability tends to zero | `paper_53e951f48c854f4db91e6ecda697ee2b` | [Result_r1_c98ad05e9014471087e93356330c1538.lean:14](proof/src/theorem-5.14/ProverJobs/paper_fresh_20261028t151409527z_hmc_v5/PaperProofInterfaces/Result_r1_c98ad05e9014471087e93356330c1538.lean#L14) |
| One-step position-norm growth | `paper_b7909512ace54739b0ef8eae60aa82ed` | [Result_r1_d73899bbfc454de7992b93e067f8c87d.lean:11](proof/src/theorem-5.14/ProverJobs/paper_fresh_20261028t151409527z_hmc_v5/PaperProofInterfaces/Result_r1_d73899bbfc454de7992b93e067f8c87d.lean#L11) |
| Metropolis–Hastings kernel decomposition | `paper_4f562633bddc4ee9afee32ec40dfa0f0` | [Result_r1_f1452eaf9e424e2bb6057a3750b7de24.lean:11](proof/src/theorem-5.14/ProverJobs/paper_fresh_20261028t151409527z_hmc_v5/PaperProofInterfaces/Result_r1_f1452eaf9e424e2bb6057a3750b7de24.lean#L11) |
| Random integration-time exponential-integrability interface | `paper_7ad7b898530c48b2be48d9fe88a3d538` | [Result_r2_6e683b73033e4102a234a951e6932c5e.lean:10](proof/src/theorem-5.14/ProverJobs/paper_fresh_20261028t151409527z_hmc_v5/PaperProofInterfaces/Result_r2_6e683b73033e4102a234a951e6932c5e.lean#L10) |

## External references used by the main results

The count is the number of distinct external citation axioms in the actual recursive proof dependencies of the selected main theorem(s). A citation used by several main theorems is counted once. Citations used only by independently checked supporting tasks are excluded, together with unused declarations, ordinary library imports and explicit theorem hypotheses. Direct-use links identify proof code. These citations are assumptions, not proofs supplied here.

| Reference | Axiom declaration | Direct proof uses | Selected targets depending on it |
| --- | --- | --- | --- |
| Geometric ergodicity plus local retention implies an exponential moment | [`ext_model_1` (line 14)](proof/src/theorem-2.2/ProverJobs/paper_fresh_20261028t224543381z_hmc_22/ExternalNodes/Node_6515c10a3b2a6920f75d.lean#L14) | [Result_r2_efa8fa985bbe48fe90bebe042f1092ee.lean:152](proof/src/theorem-2.2/ProverJobs/paper_fresh_20261028t224543381z_hmc_22/PaperProofInterfaces/Result_r2_efa8fa985bbe48fe90bebe042f1092ee.lean#L152) | Theorem 2.2 (i–ii) |
