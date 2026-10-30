import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology

namespace Msc62GroundTruth

/--
The sample mean of an iid finite-variance sequence has variance `sigma2 / n`,
therefore satisfies the Chebyshev bound and converges in probability.
-/
theorem chebyshev_sample_mean_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (mu sigma2 : ℝ) (hsigma2 : 0 ≤ sigma2)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_memLp : ∀ i, MemLp (X i) 2 P)
    (hX_mean : ∀ i, (∫ ω, X i ω ∂P) = mu)
    (hX_var : ∀ i, ProbabilityTheory.variance (X i) P = sigma2)
    (hX_indep : ProbabilityTheory.iIndepFun (β := fun _ : ℕ => ℝ) X P)
    (hX_ident : ∀ i j, ProbabilityTheory.IdentDistrib (X i) (X j) P P) :
    let barX : (n : ℕ) → Ω → ℝ :=
      fun n ω => (∑ i : Fin n, X (i : ℕ) ω) / (n : ℝ)
    (∀ n : ℕ, 1 ≤ n →
      ProbabilityTheory.variance (barX n) P =
        sigma2 / (n : ℝ)) ∧
    (∀ (n : ℕ) (epsilon : ℝ), 1 ≤ n → 0 < epsilon →
      (P {ω | epsilon ≤ |barX n ω - mu|}).toReal ≤
        sigma2 / ((n : ℝ) * epsilon ^ 2)) ∧
    (∀ epsilon : ℝ, 0 < epsilon →
      Tendsto
        (fun n : ℕ => (P {ω | epsilon ≤ |barX n ω - mu|}).toReal)
        atTop (nhds 0)) := by
  sorry

end Msc62GroundTruth
