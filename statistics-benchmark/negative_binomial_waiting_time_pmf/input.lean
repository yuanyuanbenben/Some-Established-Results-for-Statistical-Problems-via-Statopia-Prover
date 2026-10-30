import Mathlib

namespace Msc62GroundTruth

/--
The waiting time until the r-th Bernoulli success has the negative-binomial
mass formula.
-/
theorem negative_binomial_waiting_time_pmf
    (r m : ℕ) (hr : 1 ≤ r) (hrm : r ≤ m)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    let countBefore : (Fin (m - 1) → Bool) → ℕ :=
      fun x => ∑ i : Fin (m - 1), if x i then (1 : ℕ) else 0
    let prefixProb : (Fin (m - 1) → Bool) → ℝ :=
      fun x => p ^ countBefore x * (1 - p) ^ ((m - 1) - countBefore x)
    (∑ x : Fin (m - 1) → Bool,
      if countBefore x = r - 1 then prefixProb x * p else 0) =
        (Nat.choose (m - 1) (r - 1) : ℝ) * p ^ r * (1 - p) ^ (m - r) := by
  sorry

end Msc62GroundTruth
