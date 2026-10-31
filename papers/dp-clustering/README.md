# DP clustering — Theorem 1

Clustering consistency with Dirichlet process mixtures — Ascolani, Lijoi, Rebaudo and Zanella (2023), arXiv:2205.12924.

Selected result: posterior consistency for the number of completely separated clusters when the concentration parameter has a sufficiently fast-decaying prior, together with inconsistency for fixed positive concentration. The prior-rate threshold is chosen before the prior. Sixteen supporting task instances are also retained.

The main theorem includes global boundedness of the base density (B3), uniform positive lower/upper kernel bounds, a bounded logarithmic derivative, and a positive base-density lower bound near the true locations. Its concentration-prior condition requires `beta > 0`, so it does not cover the uniform-prior case `beta = 0`. These are the explicit formalized contracts; full coverage of the paper's broader main-text assumptions is not claimed.

The undersmoothing result uses the full latent sample, the Dirichlet-moment denominator outside the product, and KL support on a measurable mixing-measure parameter space. Its pointwise Bayes/kernel contract is retained. The original global WeakCons H1–H4 statement is outside this selection. The two denom1 entries below are different contract instances of one source lemma, counted as two selected tasks. Fixed-alpha, low-tail, and probability/density helper variants are not additional tasks.

| Basic statistic | Value |
| --- | ---: |
| Lean source files | 226 |
| Physical Lean lines | 50,508 |
| Passed / tasks (main + supporting) | 17/17 (1+16) |
| Used external references (main results) | 0 |
| Cached Statlib modules | 4 |

[input/](input/) · [Lean source](proof/src/) · [Targets and build configuration](proof/build.json)

## Main theorem

| Result | Lean declaration | Source |
| --- | --- | --- |
| Theorem 1: random-concentration consistency and fixed-concentration inconsistency | `OfflineDPSourceMain.source_theorem_1` | [SourceMain.lean:16](proof/src/ProverJobs/manual_dp_root_finish_20261031/SourceMain.lean#L16) |

## Supporting tasks

| Task | Lean declaration | Source |
| --- | --- | --- |
| Proposition 3: prior-factor bounds | `Statlib.Imported.paper_3208f098a8f94aafb53ad0b136d14110` | [Main.lean:10](proof/src/ProverJobs/manual_dp_prior_finish_20261031/Main.lean#L10) |
| Corollary C: prior-ratio moment bound | `OfflineCorC.Statlib.Imported.paper_33963587efec4920b10d414c6b312566` | [Main.lean:1575](proof/src/ProverJobs/manual_dp_cor_c_finish_20261031/Main.lean#L1575) |
| consGeneral: expected overfitting tail tends to zero | `OfflineDPConsGeneral.consGeneral_complete_density` | [ConsGeneralComplete.lean:47](proof/src/ProverJobs/manual_dp_root_finish_20261031/ConsGeneralComplete.lean#L47) |
| Undersmoothing: underfitting posterior tends to zero, corrected model | `OfflineDPUndersmoothing.undersmoothing_source` | [Undersmoothing.lean:89](proof/src/ProverJobs/manual_dp_weakcons_repair_20261031/Undersmoothing.lean#L89) |
| lemma:ConvProbBound | `Statlib.Imported.paper_d6348dc732d4474c900772ddadac1ef8` | [Main.lean:9](proof/src/ProverJobs/job_paper_d6348dc732d4474c900772ddadac1ef8/Main.lean#L9) |
| lemma:denom | `Statlib.Imported.paper_c93669ef201447419b92d6591d8bc1aa` | [Main.lean:9](proof/src/ProverJobs/job_paper_c93669ef201447419b92d6591d8bc1aa/Main.lean#L9) |
| Equation \eqref{upper_bound_ratios} | `Statlib.Imported.paper_f4f73a8b20b648f5b0c28430901a09f4` | [Main.lean:11](proof/src/ProverJobs/job_paper_f4f73a8b20b648f5b0c28430901a09f4/Main.lean#L11) |
| Lemma \ref{numerator} | `Statlib.Imported.paper_7aa885023a494b54a3d0f82a9b80e7b2` | [Main.lean:9](proof/src/ProverJobs/job_paper_7aa885023a494b54a3d0f82a9b80e7b2/Main.lean#L9) |
| Lemma 3 (Lemma \ref{suff_expectation}) | `Statlib.Imported.paper_20b0260ed6f74673a96e9b9321c3333f` | [Main.lean:9](proof/src/ProverJobs/job_paper_20b0260ed6f74673a96e9b9321c3333f/Main.lean#L9) |
| Lemma \ref{induction} | `Statlib.Imported.paper_26cf7ed67549489c93e7ce6890ea6ef9` | [Main.lean:8](proof/src/ProverJobs/job_paper_26cf7ed67549489c93e7ce6890ea6ef9/Main.lean#L8) |
| Lemma \ref{bound_sum} | `Statlib.Imported.paper_bd898e13604647fb8e67ad70fa3fcacd` | [Main.lean:7](proof/src/ProverJobs/job_paper_bd898e13604647fb8e67ad70fa3fcacd/Main.lean#L7) |
| Lemma \ref{lemma_weak_convergence} | `Statlib.Imported.paper_b0cf39bbf6c845c9a6b30a5db43f8efa` | [Main.lean:9](proof/src/ProverJobs/job_paper_b0cf39bbf6c845c9a6b30a5db43f8efa/Main.lean#L9) |
| Lemma \ref{first_auxiliary} | `Statlib.Imported.paper_2fbfd1902da645daba7b723031e5be32` | [Main.lean:10](proof/src/ProverJobs/job_paper_2fbfd1902da645daba7b723031e5be32/Main.lean#L10) |
| Lemma \ref{second_auxiliary} | `Statlib.Imported.paper_c1b4b2ae4a83402c9ed74e46a3652ba5` | [Main.lean:10](proof/src/ProverJobs/job_paper_c1b4b2ae4a83402c9ed74e46a3652ba5/Main.lean#L10) |
| Lemma denom1: translated-center likelihood bound | `Statlib.Imported.paper_a2bb64c47d4d486d8be39815258273b1` | [Main.lean:9](proof/src/ProverJobs/job_paper_a2bb64c47d4d486d8be39815258273b1/Main.lean#L9) |
| Lemma denom1: normalized logarithm-extension bound | `Statlib.Imported.paper_0baaef19576449e5945304ab4df728fe` | [Main.lean:9](proof/src/ProverJobs/job_paper_0baaef19576449e5945304ab4df728fe/Main.lean#L9) |

Each configured case compiles in an isolated environment. The shared `proof/src/` tree deduplicates source modules; the cases keep independently generated namespaces separate. All 17 selected declarations are checked for nonstandard axioms.

## External references used by the main results

No selected main or supporting target depends on an external citation axiom. All 17 checked targets use only Lean's standard axioms. The retained unused declaration below is excluded from the count.

### Unused declarations (excluded from the count)

| Reference | Axiom declaration |
| --- | --- |
| Weak limits preserve a uniform finite support-cardinality bound | [`OfflineCorrectedDP.ext_model_5`, line 990](proof/src/ProverJobs/manual_dp_weakcons_repair_20261031/BoxedWeakCons/CorrectedGeometry.lean#L990) |
