import Mathlib

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

theorem asymptotic_normality_of_sample_variance
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ)
    (mean varianceSq fourthMoment : ℝ)
    (G : Ω → ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X P)
    (hX_ident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hfourth_integrable : Integrable (fun ω ↦ |X 0 ω| ^ 4) P)
    (hmean : ∫ ω, X 0 ω ∂P = mean)
    (hvariance :
      ∫ ω, (X 0 ω - mean) ^ 2 ∂P = varianceSq)
    (hfourth :
      ∫ ω, (X 0 ω - mean) ^ 4 ∂P = fourthMoment)
    (hgap : varianceSq ^ 2 < fourthMoment)
    (hG_meas : Measurable G)
    (hG_law :
      IdentDistrib G id P
        (gaussianReal 0
          ⟨fourthMoment - varianceSq ^ 2, sub_nonneg.mpr hgap.le⟩)) :
    let Xbar : ℕ → Ω → ℝ :=
      fun n ω ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, X i ω
    let V : ℕ → Ω → ℝ :=
      fun n ω ↦
        (n : ℝ)⁻¹ *
          ∑ i ∈ Finset.range n, (X i ω - Xbar n ω) ^ 2
    TendstoInDistribution
      (fun (n : ℕ) ω ↦ Real.sqrt (n : ℝ) * (V n ω - varianceSq))
      atTop G P := by
  sorry
