import Mathlib

open Finset

namespace Msc62GroundTruth

/--
Under the null randomization model, the Wilcoxon rank-sum statistic has its
classical finite-sample mean and variance.
-/
theorem wilcoxon_rank_sum_mean_variance
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    let N : ℕ := m + n
    let samples : Finset (Finset (Fin N)) :=
      (Finset.univ : Finset (Finset (Fin N))).filter (fun A => A.card = m)
    let rank : Fin N → ℝ := fun r => ((r.val + 1 : ℕ) : ℝ)
    let W : Finset (Fin N) → ℝ := fun A => A.sum (fun r => rank r)
    let mean : ℝ := (1 / (samples.card : ℝ)) * samples.sum (fun A => W A)
    let variance : ℝ :=
      (1 / (samples.card : ℝ)) * samples.sum (fun A => (W A - mean) ^ 2)
    mean = (m : ℝ) * ((N : ℝ) + 1) / 2 ∧
      variance = (m : ℝ) * (n : ℝ) * ((N : ℝ) + 1) / 12 := by
  sorry

end Msc62GroundTruth
