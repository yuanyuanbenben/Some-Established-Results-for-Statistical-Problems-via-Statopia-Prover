import Mathlib

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

theorem studentized_central_limit_theorem
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ)
    (mean sigma : ℝ)
    (G : Ω → ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X P)
    (hX_ident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hmean : ∫ ω, X 0 ω ∂P = mean)
    (hvar : variance (X 0) P = sigma ^ 2)
    (hsigma : 0 < sigma)
    (hG_meas : Measurable G)
    (hG_law : IdentDistrib G id P (gaussianReal 0 1)) :
    let Xbar : ℕ → Ω → ℝ :=
      fun n ω ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, X i ω
    let S : ℕ → Ω → ℝ :=
      fun n ω ↦
        Real.sqrt
          ((n : ℝ)⁻¹ *
            ∑ i ∈ Finset.range n, (X i ω - Xbar n ω) ^ 2)
    let T : ℕ → Ω → ℝ :=
      fun n ω ↦
        if 0 < S n ω then
          Real.sqrt (n : ℝ) * (Xbar n ω - mean) / S n ω
        else 0
    TendstoInDistribution T atTop G P := by
  sorry
