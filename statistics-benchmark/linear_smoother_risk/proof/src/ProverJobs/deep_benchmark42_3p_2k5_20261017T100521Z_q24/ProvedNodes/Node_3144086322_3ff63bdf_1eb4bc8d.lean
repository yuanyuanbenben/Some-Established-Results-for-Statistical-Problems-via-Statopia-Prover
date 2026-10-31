import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q24.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q24.Base

open MeasureTheory

open MeasureTheory

set_option autoImplicit false in
theorem statopia_math_node_3144086322_3ff63bdf : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ)
    (xi : Ω → Fin n → ℝ)
    (hxi_meas : Measurable xi)
    (hxi_sq_int : Integrable (fun ω ↦ ∑ i, (xi ω i) ^ 2) P),
    ∀ i j : Fin n,
      Integrable (fun ω => (xi ω i) ^ 2) P ∧
      Integrable (fun ω => xi ω i) P ∧
      Integrable (fun ω => xi ω i * xi ω j) P := by
  /- @proof-region region.target-node.session.e5209bd93a4b1e2d begin -/
  intro Ω hΩ P hP n xi hxi_meas hxi_sq_int i j
  have hcoord : ∀ k : Fin n, Measurable (fun ω => xi ω k) := fun k =>
    ((continuous_apply k).measurable).comp hxi_meas
  have hsq_meas : ∀ k : Fin n, Measurable (fun ω => (xi ω k) ^ 2) := by
    intro k
    simpa [pow_two] using (hcoord k).mul (hcoord k)
  have hsq : ∀ k : Fin n, Integrable (fun ω => (xi ω k) ^ 2) P := by
    intro k
    refine hxi_sq_int.mono (hsq_meas k).aestronglyMeasurable ?_
    filter_upwards with ω
    have hnn1 : (0 : ℝ) ≤ (xi ω k) ^ 2 := sq_nonneg _
    have hnn2 : (0 : ℝ) ≤ ∑ m, (xi ω m) ^ 2 :=
      Finset.sum_nonneg (fun m _ => sq_nonneg (xi ω m))
    have hle : (xi ω k) ^ 2 ≤ ∑ m, (xi ω m) ^ 2 :=
      Finset.single_le_sum (fun m _ => sq_nonneg (xi ω m)) (Finset.mem_univ k)
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnn1, abs_of_nonneg hnn2] using hle
  have hint : ∀ k : Fin n, Integrable (fun ω => xi ω k) P := by
    intro k
    have hdom : Integrable (fun ω => (1 / 2 : ℝ) * ((xi ω k) ^ 2 + 1)) P :=
      ((hsq k).add (integrable_const (1 : ℝ))).const_mul (1 / 2 : ℝ)
    refine hdom.mono (hcoord k).aestronglyMeasurable ?_
    filter_upwards with ω
    have hnn : (0 : ℝ) ≤ (1 / 2 : ℝ) * ((xi ω k) ^ 2 + 1) := by positivity
    have habs : |xi ω k| ≤ (1 / 2 : ℝ) * ((xi ω k) ^ 2 + 1) := by
      refine abs_le.mpr ⟨?_, ?_⟩
      · nlinarith [sq_nonneg (xi ω k + 1)]
      · nlinarith [sq_nonneg (xi ω k - 1)]
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnn] using habs
  have hprod : ∀ k l : Fin n, Integrable (fun ω => xi ω k * xi ω l) P := by
    intro k l
    have hdom : Integrable (fun ω => (1 / 2 : ℝ) * ((xi ω k) ^ 2 + (xi ω l) ^ 2)) P :=
      ((hsq k).add (hsq l)).const_mul (1 / 2 : ℝ)
    refine hdom.mono ((hcoord k).mul (hcoord l)).aestronglyMeasurable ?_
    filter_upwards with ω
    have hnn : (0 : ℝ) ≤ (1 / 2 : ℝ) * ((xi ω k) ^ 2 + (xi ω l) ^ 2) := by positivity
    have habs : |xi ω k * xi ω l| ≤ (1 / 2 : ℝ) * ((xi ω k) ^ 2 + (xi ω l) ^ 2) := by
      refine abs_le.mpr ⟨?_, ?_⟩
      · nlinarith [sq_nonneg (xi ω k + xi ω l)]
      · nlinarith [sq_nonneg (xi ω k - xi ω l)]
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnn] using habs
  exact ⟨hsq i, hint i, hprod i j⟩
  /- @proof-region region.target-node.session.e5209bd93a4b1e2d end -/
