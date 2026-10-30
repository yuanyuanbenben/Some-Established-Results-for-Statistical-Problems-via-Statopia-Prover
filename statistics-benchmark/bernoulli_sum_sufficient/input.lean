import Mathlib

namespace Msc62GroundTruth

/--
For an nid Bernoulli sample, the conditional distribution of the full binary
sample given the number of successes is uniform on that fiber.
-/
theorem bernoulli_sum_sufficient
    (n : ℕ) (hn : 1 ≤ n) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    let Ω : Type := Fin n → Bool
    let count : Ω → ℕ :=
      fun z => ∑ i : Fin n, if z i then (1 : ℕ) else 0
    let prob : ℝ → Ω → ℝ :=
      fun q z => q ^ count z * (1 - q) ^ (n - count z)
    let condProb : ℝ → ℕ → Ω → ℝ :=
      fun q k z =>
        if count z = k then
          prob q z / (∑ y : Ω, if count y = k then prob q y else 0)
        else 0
    (∀ k : ℕ, k ≤ n → ∀ x : Ω, count x = k →
      condProb p k x = 1 / (Nat.choose n k : ℝ)) ∧
    (∀ k : ℕ, k ≤ n →
      ∀ p1 : ℝ, 0 < p1 → p1 < 1 →
      ∀ p2 : ℝ, 0 < p2 → p2 < 1 →
        condProb p1 k = condProb p2 k) := by
  sorry

end Msc62GroundTruth
