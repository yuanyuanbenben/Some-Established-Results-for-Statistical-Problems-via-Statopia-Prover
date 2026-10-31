import Mathlib

open MeasureTheory ProbabilityTheory

namespace Msc62GroundTruth

/--
Entrywise unbiasedness of the Bessel-corrected centered sample covariance
matrix under common first and second moments and zero centered cross-products
between distinct observations.
-/
theorem sample_covariance_unbiased
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n d : ℕ) (hn : 2 ≤ n) (hd : 1 ≤ d)
    (X : Fin n → Ω → Fin d → ℝ)
    (hX_meas : ∀ i a, Measurable (fun ω => X i ω a))
    (hX_memLp : ∀ i a, MemLp (fun ω => X i ω a) 2 P)
    (mu : Fin d → ℝ)
    (hmean : ∀ i a, (∫ ω, X i ω a ∂P) = mu a)
    (Sigma : Matrix (Fin d) (Fin d) ℝ)
    (hSigma : ∀ i a b,
      Sigma a b =
        ∫ ω, (X i ω a - mu a) * (X i ω b - mu b) ∂P)
    (h_cross_zero : ∀ i j a b, i ≠ j →
      (∫ ω, (X i ω a - mu a) * (X j ω b - mu b) ∂P) = 0) :
    let barX : Fin d → Ω → ℝ :=
      fun a ω => (1 / (n : ℝ)) * ∑ i : Fin n, X i ω a
    let S : Fin d → Fin d → Ω → ℝ :=
      fun a b ω => (1 / ((n - 1 : ℕ) : ℝ)) *
        ∑ i : Fin n, (X i ω a - barX a ω) * (X i ω b - barX b ω)
    ∀ a b : Fin d,
      (∫ ω, S a b ω ∂P) = Sigma a b := by
  sorry

end Msc62GroundTruth
