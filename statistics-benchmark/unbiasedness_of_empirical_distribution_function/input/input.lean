import Mathlib

open MeasureTheory ProbabilityTheory

namespace Msc62GroundTruth

/--
For identically distributed observations, the empirical distribution function
is unbiased for the common distribution function at every fixed point `t`.
-/
theorem unbiasedness_of_empirical_distribution_function
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : n ≥ 1) (X : Fin n → Ω → ℝ) (F : ℝ → ℝ) (t : ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (h_identically_distributed :
      ∀ i x, (P {ω | X i ω ≤ x}).toReal = F x) :
    let F_n_t : Ω → ℝ :=
      fun ω => (1 / (n : ℝ)) *
        ∑ i : Fin n, Set.indicator {ω' : Ω | X i ω' ≤ t} (fun _ => (1 : ℝ)) ω;
    (∫ ω, F_n_t ω ∂P) = F t := by
  sorry

end Msc62GroundTruth
