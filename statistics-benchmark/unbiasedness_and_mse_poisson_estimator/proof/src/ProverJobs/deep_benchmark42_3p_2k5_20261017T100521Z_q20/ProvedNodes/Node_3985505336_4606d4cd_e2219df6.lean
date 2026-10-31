import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q20.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q20.Base

open MeasureTheory ProbabilityTheory
open scoped BigOperators

open MeasureTheory ProbabilityTheory
open scoped BigOperators

set_option autoImplicit false in
theorem statopia_math_node_3985505336_4606d4cd : ∀ {Ω : Type*} [MeasurableSpace Ω] {ι : Type*}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ι → Ω → ℝ)
    (hY_indep : iIndepFun Y P)
    (hY_meas : ∀ i, Measurable (Y i))
    (hY_int : ∀ i, Integrable (Y i) P)
    (s : Finset ι),
    Integrable (fun ω => ∏ i ∈ s, Y i ω) P ∧
      ∫ ω, (∏ i ∈ s, Y i ω) ∂P = ∏ i ∈ s, (∫ ω, Y i ω ∂P) := by
  /- @proof-region region.target-node.session.1542a5c39c23cc1f begin -/
  intro Ω _ ι P _ Y hY_indep hY_meas hY_int s
  classical
  have hbridge : ∀ u : Finset ι, (∏ i ∈ u, Y i : Ω → ℝ) = fun ω => ∏ i ∈ u, Y i ω := by
    intro u
    funext ω
    simp
  suffices H : Integrable (∏ i ∈ s, Y i : Ω → ℝ) P ∧
      ∫ ω, (∏ i ∈ s, Y i) ω ∂P = ∏ i ∈ s, (∫ ω, Y i ω ∂P) by
    obtain ⟨h1, h2⟩ := H
    rw [hbridge s] at h1 h2
    exact ⟨h1, h2⟩
  induction s using Finset.induction_on with
  | empty =>
    constructor
    · simpa using integrable_const (1 : ℝ)
    · simp [MeasureTheory.integral_const]
  | insert j t hj ih =>
    obtain ⟨hZ_int, hZ_eq⟩ := ih
    have h_indep : (∏ i ∈ t, Y i : Ω → ℝ) ⟂ᵢ[P] Y j :=
      hY_indep.indepFun_finset_prod_of_notMem hY_meas hj
    have heq : (∏ i ∈ insert j t, Y i : Ω → ℝ) = (∏ i ∈ t, Y i) * Y j := by
      rw [Finset.prod_insert hj]
      exact mul_comm _ _
    refine ⟨?_, ?_⟩
    · rw [heq]
      exact h_indep.integrable_mul hZ_int (hY_int j)
    · rw [heq, h_indep.integral_mul hZ_int.aestronglyMeasurable
        (hY_meas j).aestronglyMeasurable, hZ_eq, Finset.prod_insert hj]
      exact mul_comm _ _
  /- @proof-region region.target-node.session.1542a5c39c23cc1f end -/
