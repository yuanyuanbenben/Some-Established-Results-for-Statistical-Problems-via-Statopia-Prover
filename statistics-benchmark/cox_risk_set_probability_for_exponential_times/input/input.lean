import Mathlib

open MeasureTheory ProbabilityTheory

theorem cox_risk_set_probability_for_exponential_times
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 1 ≤ n)
    (lambda₀ beta : ℝ) (hlambda : 0 < lambda₀)
    (z : Fin n → ℝ)
    (T : Fin n → Ω → ℝ)
    (hTmeas : ∀ i, Measurable (T i))
    (hTnonneg : ∀ i ω, 0 ≤ T i ω)
    (hindep : iIndepFun T P)
    (hsurvival : ∀ i t, 0 ≤ t →
      P {ω | t < T i ω} =
        ENNReal.ofReal (Real.exp (-lambda₀ * Real.exp (beta * z i) * t))) :
    ∀ i,
      P {ω | ∀ j, j ≠ i → T i ω < T j ω} =
        ENNReal.ofReal
          (Real.exp (beta * z i) /
            ∑ j, Real.exp (beta * z j)) := by
  sorry
