import Mathlib

open MeasureTheory ProbabilityTheory

namespace Msc62GroundTruth

/--
The autocovariance function of an MA(1) process has nonzero lags only at
0 and 1.
-/
theorem ma1_autocovariance
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (theta sigma2 : ℝ) (hsigma2 : 0 ≤ sigma2)
    (eps : ℤ → Ω → ℝ)
    (heps_meas : ∀ t, Measurable (eps t))
    (heps_memLp : ∀ t, MemLp (eps t) 2 P)
    (heps_mean : ∀ t, (∫ ω, eps t ω ∂P) = 0)
    (heps_var : ∀ t, ProbabilityTheory.variance (eps t) P = sigma2)
    (heps_cov_zero : ∀ s t, s ≠ t →
      ProbabilityTheory.covariance (eps s) (eps t) P = 0) :
    let X : ℤ → Ω → ℝ :=
      fun t ω => eps t ω + theta * eps (t - 1) ω
    (∀ h : ℕ, ∀ t1 t2 : ℤ,
      ProbabilityTheory.covariance (X t1) (X (t1 + (h : ℤ))) P =
        ProbabilityTheory.covariance (X t2) (X (t2 + (h : ℤ))) P) ∧
    (∀ t : ℤ, ProbabilityTheory.covariance (X t) (X (t + (0 : ℤ))) P =
      (1 + theta ^ 2) * sigma2) ∧
    (∀ t : ℤ, ProbabilityTheory.covariance (X t) (X (t + (1 : ℤ))) P =
      theta * sigma2) ∧
    (∀ h : ℕ, 2 ≤ h → ∀ t : ℤ,
      ProbabilityTheory.covariance (X t) (X (t + (h : ℤ))) P = 0) := by
  sorry

end Msc62GroundTruth
