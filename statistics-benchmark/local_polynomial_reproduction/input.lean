import Mathlib

open Matrix

theorem local_polynomial_reproduction
    (n : ℕ) (hn : 1 ≤ n)
    (ell : ℕ)
    (X : Fin n → ℝ)
    (K : ℝ → ℝ) (hK_nonneg : ∀ u, 0 ≤ K u)
    (x h : ℝ) (hh : 0 < h) :
    let U : ℝ → Fin (ell + 1) → ℝ := fun u k ↦
      u ^ k.1 / (Nat.factorial k.1 : ℝ)
    let B : Matrix (Fin (ell + 1)) (Fin (ell + 1)) ℝ := fun a b ↦
      ((n : ℝ) * h)⁻¹ *
        ∑ i, U ((X i - x) / h) a * U ((X i - x) / h) b *
          K ((X i - x) / h)
    IsUnit B.det →
      let W : Fin n → ℝ := fun i ↦
        ((n : ℝ) * h)⁻¹ *
          (∑ a, U 0 a * ∑ b, B⁻¹ a b * U ((X i - x) / h) b) *
          K ((X i - x) / h)
      ∀ Q : Polynomial ℝ, Q.natDegree ≤ ell →
        ∑ i, W i * Q.eval (X i) = Q.eval x := by
  sorry
