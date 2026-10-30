import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q11.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q11.Base

open MeasureTheory

open MeasureTheory

set_option autoImplicit false in
theorem statopia_math_node_714068217_742cf005 : ∀ {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → H)
    (hXmeas : StronglyMeasurable X)
    (hXsq : Integrable (fun ω => ‖X ω‖ ^ 2) P),
    Integrable X P ∧
      AEStronglyMeasurable (fun ω => X ω - ∫ z, X z ∂P) P ∧
      Integrable (fun ω => ‖X ω - ∫ z, X z ∂P‖ ^ 2) P ∧
      (0 ≤ ∫ ω, ‖X ω - ∫ z, X z ∂P‖ ^ 2 ∂P) ∧
      (∀ ω : Ω, ‖X ω - ∫ z, X z ∂P‖ ^ 2 ≤ 2 * ‖X ω‖ ^ 2 + 2 * ‖∫ z, X z ∂P‖ ^ 2) := by
  /- @proof-region region.target-node.session.778cf38e2497b72a begin -/
  intro Ω H _ _ _ P _ X hXmeas hXsq
  have hconst : Integrable (fun _ : Ω => (1 : ℝ)) P := integrable_const 1
  have hdom : Integrable (fun ω => 1 + ‖X ω‖ ^ 2) P := hconst.add hXsq
  have hnorm_le : ∀ᵐ ω ∂P, ‖(‖X ω‖ : ℝ)‖ ≤ 1 + ‖X ω‖ ^ 2 := by
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (X ω))]
    nlinarith [sq_nonneg (‖X ω‖ - 1 / 2)]
  have hnorm_int : Integrable (fun ω => ‖X ω‖) P :=
    Integrable.mono' (g := fun ω => 1 + ‖X ω‖ ^ 2) hdom (hXmeas.norm).aestronglyMeasurable
      hnorm_le
  have hXint : Integrable X P :=
    (integrable_norm_iff hXmeas.aestronglyMeasurable).1 hnorm_int
  have hYmeas : StronglyMeasurable (fun ω => X ω - ∫ z, X z ∂P) :=
    hXmeas.sub stronglyMeasurable_const
  have hbd : Integrable (fun ω => 2 * ‖X ω‖ ^ 2 + 2 * ‖∫ z, X z ∂P‖ ^ 2) P := by
    have h1 : Integrable (fun ω => 2 * ‖X ω‖ ^ 2) P := by
      simpa [smul_eq_mul] using hXsq.const_mul 2
    have h2 : Integrable (fun _ : Ω => 2 * ‖∫ z, X z ∂P‖ ^ 2) P := integrable_const _
    exact h1.add h2
  have hYsq_int : Integrable (fun ω => ‖X ω - ∫ z, X z ∂P‖ ^ 2) P := by
    refine Integrable.mono' (g := fun ω => 2 * ‖X ω‖ ^ 2 + 2 * ‖∫ z, X z ∂P‖ ^ 2) hbd
      ((hYmeas.norm).pow 2).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 : ‖X ω - ∫ z, X z ∂P‖ ≤ ‖X ω‖ + ‖∫ z, X z ∂P‖ := norm_sub_le _ _
    nlinarith [h1, norm_nonneg (X ω), norm_nonneg (∫ z, X z ∂P),
      norm_nonneg (X ω - ∫ z, X z ∂P), sq_nonneg (‖X ω‖ - ‖∫ z, X z ∂P‖)]
  refine ⟨hXint, ?_, hYsq_int, ?_, ?_⟩
  · exact hYmeas.aestronglyMeasurable
  · exact integral_nonneg (fun ω => by positivity)
  · intro ω
    have h1 : ‖X ω - ∫ z, X z ∂P‖ ≤ ‖X ω‖ + ‖∫ z, X z ∂P‖ := norm_sub_le _ _
    have h2 : (‖X ω‖ + ‖∫ z, X z ∂P‖) ^ 2 ≤ 2 * ‖X ω‖ ^ 2 + 2 * ‖∫ z, X z ∂P‖ ^ 2 := by
      nlinarith [sq_nonneg (‖X ω‖ - ‖∫ z, X z ∂P‖)]
    nlinarith [h1, h2, norm_nonneg (X ω), norm_nonneg (∫ z, X z ∂P),
      norm_nonneg (X ω - ∫ z, X z ∂P)]
  /- @proof-region region.target-node.session.778cf38e2497b72a end -/
