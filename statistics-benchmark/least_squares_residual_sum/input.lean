import Mathlib

namespace Msc62GroundTruth

/--
For ordinary least squares with an intercept, residuals sum to zero at a
minimizer.
-/
theorem least_squares_residual_sum
    (n : ℕ) (hn : n ≥ 1) (x y : Fin n → ℝ)
    (Q : ℝ → ℝ → ℝ)
    (hQ : ∀ a b : ℝ, Q a b = ∑ i : Fin n, (y i - a - b * x i) ^ 2)
    (ahat bhat : ℝ)
    (hmin : ∀ a b : ℝ, Q ahat bhat ≤ Q a b)
    (e : Fin n → ℝ)
    (he : ∀ i, e i = y i - ahat - bhat * x i) :
    (∑ i : Fin n, e i) = 0 := by
  sorry

end Msc62GroundTruth
