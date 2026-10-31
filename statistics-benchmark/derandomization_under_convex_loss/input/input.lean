import Mathlib

open scoped BigOperators

theorem derandomization_under_convex_loss
    (m N k : ℕ)
    (hm : 1 ≤ m)
    (hN : 1 ≤ N)
    (hk : 1 ≤ k)
    (p : Fin m → Fin N → ℝ)
    (hp0 : ∀ j x, 0 ≤ p j x)
    (hp1 : ∀ j x, p j x ≤ 1)
    (hpsum : ∀ j, ∑ x, p j x = 1)
    (a : Fin k → ℝ)
    (q : Fin N → Fin k → ℝ)
    (hq0 : ∀ x r, 0 ≤ q x r)
    (hq1 : ∀ x r, q x r ≤ 1)
    (hqsum : ∀ x, ∑ r, q x r = 1)
    (ell : Fin m → ℝ → ℝ)
    (hell0 : ∀ j t, 0 ≤ ell j t)
    (hellconv : ∀ j, ConvexOn ℝ Set.univ (ell j)) :
    ∀ j,
      ∑ x, p j x * ell j (∑ r, q x r * a r) ≤
        ∑ x, p j x * ∑ r, q x r * ell j (a r) := by
  sorry
