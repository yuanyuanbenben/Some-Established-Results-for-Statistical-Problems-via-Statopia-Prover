import Mathlib

open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem power_function_one_sided_gaussian_mean_test
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 1 ≤ n)
    (mean mean₀ c sigma : ℝ) (hsigma : 0 < sigma)
    (X : Fin n → Ω → ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X P)
    (hX_law : ∀ i,
      IdentDistrib (X i) id P
        (gaussianReal mean ⟨sigma ^ 2, sq_nonneg sigma⟩)) :
    let Xbar : Ω → ℝ :=
      fun ω ↦ (n : ℝ)⁻¹ * ∑ i : Fin n, X i ω
    ENNReal.toReal
        (P {ω |
          Real.sqrt (n : ℝ) * (Xbar ω - mean₀) / sigma > c})
      =
      1 -
        cdf (gaussianReal 0 1)
          (c - Real.sqrt (n : ℝ) * (mean - mean₀) / sigma) := by
  sorry
