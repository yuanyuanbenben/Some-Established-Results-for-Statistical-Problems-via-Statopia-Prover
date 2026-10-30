import Mathlib

open Finset

namespace Msc62GroundTruth

/--
For a uniform simple random sample without replacement, the variance of the
sample mean has the finite-population correction factor.
-/
theorem finite_population_correction_srs
    (N n : ℕ) (hN : 2 ≤ N) (hn_pos : 1 ≤ n) (hn_le : n ≤ N)
    (y : Fin N → ℝ) :
    let samples : Finset (Finset (Fin N)) :=
      (Finset.univ : Finset (Finset (Fin N))).filter (fun S => S.card = n)
    let mu : ℝ := (1 / (N : ℝ)) * ∑ i : Fin N, y i
    let sampleMean : Finset (Fin N) → ℝ :=
      fun S => (1 / (n : ℝ)) * S.sum (fun i => y i)
    let popVar : ℝ :=
      (1 / ((N - 1 : ℕ) : ℝ)) * ∑ i : Fin N, (y i - mu) ^ 2
    let varSampleMean : ℝ :=
      (1 / (samples.card : ℝ)) *
        samples.sum (fun S => (sampleMean S - mu) ^ 2)
    varSampleMean =
      (1 - (n : ℝ) / (N : ℝ)) * popVar / (n : ℝ) := by
  sorry

end Msc62GroundTruth
