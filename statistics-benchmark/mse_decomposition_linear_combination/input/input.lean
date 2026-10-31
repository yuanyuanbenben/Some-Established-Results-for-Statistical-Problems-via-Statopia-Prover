import Mathlib

open MeasureTheory ProbabilityTheory

theorem mse_decomposition_linear_combination
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T₁ T₂ : Ω → ℝ)
    (theta v₁ v₂ w : ℝ)
    (hT₁_meas : Measurable T₁)
    (hT₂_meas : Measurable T₂)
    (hT_indep : IndepFun T₁ T₂ P)
    (hT₁_second : MemLp T₁ 2 P)
    (hT₂_second : MemLp T₂ 2 P)
    (hT₁_mean : ∫ ω, T₁ ω ∂P = theta)
    (hT₂_mean : ∫ ω, T₂ ω ∂P = theta)
    (hT₁_var : variance T₁ P = v₁)
    (hT₂_var : variance T₂ P = v₂)
    (hv₁ : 0 < v₁) (hv₂ : 0 < v₂) :
    (∫ ω, (w * T₁ ω + (1 - w) * T₂ ω - theta) ^ 2 ∂P)
      =
      v₁ * v₂ / (v₁ + v₂) +
        (v₁ + v₂) * (w - v₂ / (v₁ + v₂)) ^ 2 := by
  sorry
