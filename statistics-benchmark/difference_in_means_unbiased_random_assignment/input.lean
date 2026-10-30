import Mathlib

open MeasureTheory ProbabilityTheory

namespace Msc62GroundTruth

/--
The difference-in-means estimator is unbiased under marginal randomized
assignment probabilities.
-/
theorem difference_in_means_unbiased_random_assignment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n1 n0 : ℕ) (hn1 : n1 ≥ 1) (hn0 : n0 ≥ 1)
    (N : ℕ) (hN : N = n1 + n0)
    (Y1 Y0 : Fin N → ℝ)
    (W : Fin N → Ω → ℝ)
    (hW_meas : ∀ i, Measurable (W i))
    (hW_int : ∀ i, Integrable (W i) P)
    (hWc_int : ∀ i, Integrable (fun ω => 1 - W i ω) P)
    (hW_mean :
      ∀ i, (∫ ω, W i ω ∂P) = (n1 : ℝ) / (N : ℝ))
    (hWc_mean :
      ∀ i, (∫ ω, (1 - W i ω) ∂P) = (n0 : ℝ) / (N : ℝ)) :
    let tauHat : Ω → ℝ :=
      fun ω =>
        (1 / (n1 : ℝ)) * ∑ i : Fin N, W i ω * Y1 i -
          (1 / (n0 : ℝ)) * ∑ i : Fin N, (1 - W i ω) * Y0 i;
    let tau : ℝ :=
      (1 / (N : ℝ)) * ∑ i : Fin N, (Y1 i - Y0 i);
    (∫ ω, tauHat ω ∂P) = tau := by
  sorry

end Msc62GroundTruth
