import Mathlib

open Matrix

theorem no_logistic_mle_under_complete_separation
    (n p : ℕ) (hn : 1 ≤ n) (hp : 1 ≤ p)
    (x : Fin n → Fin p → ℝ)
    (y : Fin n → Bool)
    (v : Fin p → ℝ)
    (hsep : ∀ i,
      ((2 : ℝ) * (if y i then 1 else 0 : ℝ) - 1) *
        dotProduct (x i) v > 0) :
    let ell : (Fin p → ℝ) → ℝ := fun beta ↦
      ∑ i, ((if y i then 1 else 0 : ℝ) * dotProduct (x i) beta -
        Real.log (1 + Real.exp (dotProduct (x i) beta)))
    ¬ ∃ betaHat : Fin p → ℝ, ∀ beta : Fin p → ℝ,
      ell betaHat ≥ ell beta := by
  sorry
