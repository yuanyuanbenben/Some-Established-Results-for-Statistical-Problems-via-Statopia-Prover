import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q06.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q06.Base

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

set_option autoImplicit false in
theorem statopia_math_node_980666557_257fc9e4 : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ)
    (mean sigma : ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_ident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hmean : ∫ ω, X 0 ω ∂P = mean)
    (hvar : variance (X 0) P = sigma ^ 2)
    (hsigma : 0 < sigma),
    (∀ i, MemLp (X i) 2 P) ∧
    (∀ i, ∫ ω, X i ω ∂P = mean) ∧
    (∀ i, ∫ ω, (X i ω) ^ 2 ∂P = mean ^ 2 + sigma ^ 2) ∧
    Integrable (X 0) P ∧
    Integrable (fun ω => (X 0 ω) ^ 2) P := by
  /- @proof-region region.target-node.session.4d473cb42ad17ca0 begin -/
  intro Ω mΩ P hP X mean sigma hX_meas hX_ident hmean hvar hsigma
  have hvar_int : ∫ ω, (X 0 ω - ∫ x, X 0 x ∂P) ^ 2 ∂P = sigma ^ 2 := by
    rw [← hvar]
    exact (ProbabilityTheory.variance_eq_integral (hX_meas 0).aemeasurable).symm
  have hne : ∫ ω, (X 0 ω - ∫ x, X 0 x ∂P) ^ 2 ∂P ≠ 0 := by
    rw [hvar_int]
    exact pow_ne_zero 2 (ne_of_gt hsigma)
  have hInt : Integrable (fun ω => (X 0 ω - ∫ x, X 0 x ∂P) ^ 2) P := by
    by_contra hcon
    exact hne (MeasureTheory.integral_undef hcon)
  have hsub_memLp : MemLp (fun ω => X 0 ω - ∫ x, X 0 x ∂P) 2 P :=
    (MeasureTheory.memLp_two_iff_integrable_sq
      ((hX_meas 0).sub measurable_const).aestronglyMeasurable).2 hInt
  have hconst_memLp : MemLp (fun _ : Ω => (∫ x, X 0 x ∂P)) 2 P := by
    refine (MeasureTheory.memLp_two_iff_integrable_sq (μ := P)
      (measurable_const : Measurable (fun _ : Ω => (∫ x, X 0 x ∂P))).aestronglyMeasurable).2 ?_
    simpa using (MeasureTheory.integrable_const (μ := P) ((∫ x, X 0 x ∂P) ^ 2))
  have hX0_memLp : MemLp (X 0) 2 P := by
    have hadd := hsub_memLp.add hconst_memLp
    have hfun : ((fun ω => X 0 ω - (∫ x, X 0 x ∂P)) +
        (fun _ : Ω => (∫ x, X 0 x ∂P))) = X 0 := by
      funext ω
      simp
    rwa [hfun] at hadd
  have hX0_int : Integrable (X 0) P := hX0_memLp.integrable (by norm_num)
  have hX0_sq_int : Integrable (fun ω => (X 0 ω) ^ 2) P := hX0_memLp.integrable_sq
  have hsq0 : ∫ ω, (X 0 ω) ^ 2 ∂P = mean ^ 2 + sigma ^ 2 := by
    have hsub := ProbabilityTheory.variance_eq_sub hX0_memLp
    rw [hvar, hmean] at hsub
    have hfun : (∫ ω, (X 0 ω) ^ 2 ∂P) = ∫ x, (X 0 ^ 2) x ∂P := rfl
    linarith [hsub]
  have hint : ∀ i, ∫ ω, X i ω ∂P = mean := by
    intro i
    rw [(hX_ident i).integral_eq, hmean]
  have hsq : ∀ i, ∫ ω, (X i ω) ^ 2 ∂P = mean ^ 2 + sigma ^ 2 := by
    intro i
    rw [(hX_ident i).sq.integral_eq, hsq0]
  have hmemLp : ∀ i, MemLp (X i) 2 P := by
    intro i
    exact (MeasureTheory.memLp_two_iff_integrable_sq (hX_meas i).aestronglyMeasurable).2
      ((hX_ident i).sq.integrable_iff.2 hX0_sq_int)
  exact ⟨hmemLp, hint, hsq, hX0_int, hX0_sq_int⟩
  /- @proof-region region.target-node.session.4d473cb42ad17ca0 end -/
