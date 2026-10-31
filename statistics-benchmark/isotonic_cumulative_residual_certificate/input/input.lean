import Mathlib

theorem isotonic_cumulative_residual_certificate
    (n : ℕ) (hn : 1 ≤ n)
    (y thetaHat : Fin n → ℝ) :
    let R : ℕ → ℝ := fun k ↦
      ∑ j : Fin n, if j.1 < k then y j - thetaHat j else 0
    (∀ i : ℕ, (hi : i + 1 < n) →
      thetaHat ⟨i, lt_trans (Nat.lt_succ_self i) hi⟩ ≤
        thetaHat ⟨i + 1, hi⟩) →
    (∀ i : ℕ, (hi : i + 1 < n) → 0 ≤ R (i + 1)) →
    R n = 0 →
    (∀ i : ℕ, (hi : i + 1 < n) →
      R (i + 1) *
        (thetaHat ⟨i + 1, hi⟩ -
          thetaHat ⟨i, lt_trans (Nat.lt_succ_self i) hi⟩) = 0) →
    ∀ theta : Fin n → ℝ,
      (∀ i : ℕ, (hi : i + 1 < n) →
        theta ⟨i, lt_trans (Nat.lt_succ_self i) hi⟩ ≤
          theta ⟨i + 1, hi⟩) →
      ∑ i, (y i - theta i) ^ 2 ≥
        ∑ i, (y i - thetaHat i) ^ 2 +
          ∑ i, (theta i - thetaHat i) ^ 2 := by
  sorry
