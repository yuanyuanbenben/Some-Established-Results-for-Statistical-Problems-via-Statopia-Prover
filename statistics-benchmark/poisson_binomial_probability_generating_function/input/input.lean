import Mathlib

open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem poisson_binomial_probability_generating_function
    {Ω : Type*}
    [MeasurableSpace Ω]
    (P : Measure Ω)
    [IsProbabilityMeasure P]
    (n : ℕ)
    (hn : 1 ≤ n)
    (p : Fin n → ℝ)
    (hp0 : ∀ i, 0 ≤ p i)
    (hp1 : ∀ i, p i ≤ 1)
    (X : Fin n → Ω → Bool)
    (hXmeas : ∀ i, Measurable (X i))
    (hXone : ∀ i, P {ω | X i ω = true} = ENNReal.ofReal (p i))
    (hXzero : ∀ i, P {ω | X i ω = false} = ENNReal.ofReal (1 - p i))
    (hXindep : iIndepFun X P) :
    ∀ z : ℝ,
      ∫ ω, z ^ (∑ i, if X i ω then 1 else 0) ∂P =
        ∏ i, ((1 - p i) + p i * z) := by
  sorry
