import Mathlib

open Matrix

theorem strict_convexity_of_logistic_loss
    (n p : ℕ) (hnp : p ≤ n) (hp : 1 ≤ p)
    (X : Matrix (Fin n) (Fin p) ℝ)
    (hX : Function.Injective X.mulVec)
    (y : Fin n → Bool) :
    let L : (Fin p → ℝ) → ℝ := fun beta ↦
      ∑ i, (Real.log (1 + Real.exp (dotProduct (X i) beta)) -
        (if y i then 1 else 0 : ℝ) * dotProduct (X i) beta)
    ∀ beta gamma : Fin p → ℝ, beta ≠ gamma →
      ∀ t : ℝ, 0 < t → t < 1 →
        L (t • beta + (1 - t) • gamma) <
          t * L beta + (1 - t) * L gamma := by
  sorry
