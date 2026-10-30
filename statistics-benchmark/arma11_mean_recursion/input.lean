import Mathlib

open MeasureTheory ProbabilityTheory

namespace Msc62GroundTruth

/--
For an ARMA(1,1) process with zero-mean innovations, the expected value follows
the same first-order affine recursion as an AR(1) mean.
-/
theorem arma11_mean_recursion
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (c phi theta m0 : ℝ)
    (eps X : ℕ → Ω → ℝ)
    (heps_meas : ∀ t, Measurable (eps t))
    (heps_integrable : ∀ t, Integrable (eps t) P)
    (hX_meas : ∀ t, Measurable (X t))
    (hX_integrable : ∀ t, Integrable (X t) P)
    (heps_mean_zero : ∀ t, (∫ ω, eps t ω ∂P) = 0)
    (hX0_mean : (∫ ω, X 0 ω ∂P) = m0)
    (hX_rec : ∀ t ω,
      X (t + 1) ω = c + phi * X t ω + eps (t + 1) ω + theta * eps t ω) :
    ∀ t : ℕ,
      (∫ ω, X t ω ∂P) =
        phi ^ t * m0 + c * (Finset.range t).sum (fun j => phi ^ j) := by
  sorry

end Msc62GroundTruth
