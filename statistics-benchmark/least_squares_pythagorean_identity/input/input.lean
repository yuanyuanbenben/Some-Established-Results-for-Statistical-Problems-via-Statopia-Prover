import Mathlib

open Matrix

theorem least_squares_pythagorean_identity
    (n p : ℕ) (hnp : p ≤ n) (hp : 1 ≤ p)
    (X : Matrix (Fin n) (Fin p) ℝ)
    (y : Fin n → ℝ)
    (hX : Function.Injective X.mulVec) :
    let betaHat := (X.transpose * X)⁻¹ *ᵥ (X.transpose *ᵥ y)
    ∀ beta : Fin p → ℝ,
      dotProduct (y - X *ᵥ beta) (y - X *ᵥ beta) =
        dotProduct (y - X *ᵥ betaHat) (y - X *ᵥ betaHat) +
          dotProduct (X *ᵥ (beta - betaHat)) (X *ᵥ (beta - betaHat)) := by
  sorry
