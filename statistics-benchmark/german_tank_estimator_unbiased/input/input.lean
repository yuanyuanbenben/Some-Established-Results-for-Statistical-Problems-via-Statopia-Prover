import Mathlib

open MeasureTheory

theorem german_tank_estimator_unbiased
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (N n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N)
    (M : Ω → ℕ) (hM_meas : Measurable M)
    (hM_range : ∀ ω, n ≤ M ω ∧ M ω ≤ N)
    (hM_pmf : ∀ r, n ≤ r → r ≤ N →
      P {ω | M ω = r} =
        ENNReal.ofReal ((Nat.choose (r - 1) (n - 1) : ℝ) / Nat.choose N n)) :
    ∫ ω, (((n + 1 : ℕ) : ℝ) / (n : ℝ)) * (M ω : ℝ) - 1 ∂P = (N : ℝ) := by
  sorry
