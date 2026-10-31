import Mathlib

open MeasureTheory ProbabilityTheory

theorem observed_failure_mass_under_independent_right_censoring
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : ℕ) (hm : 1 ≤ m)
    (T C : Ω → ℕ)
    (hTmeas : Measurable T)
    (hCmeas : Measurable C)
    (hT : ∀ ω, 1 ≤ T ω ∧ T ω ≤ m)
    (hC : ∀ ω, 1 ≤ C ω ∧ C ω ≤ m)
    (hindep : IndepFun T C P) :
    ∀ u : ℕ, 1 ≤ u → u ≤ m →
      P {ω | min (T ω) (C ω) = u ∧ T ω ≤ C ω} =
        P {ω | T ω = u} * P {ω | u ≤ C ω} := by
  sorry
