import Mathlib

theorem kaplan_meier_jump_mass_identity
    (m : ℕ) (hm : 1 ≤ m)
    (r d : ℕ → ℕ)
    (hr : ∀ j, 1 ≤ j → j ≤ m → 0 < r j)
    (hd : ∀ j, 1 ≤ j → j ≤ m → d j ≤ r j) :
    let S : ℕ → ℝ := fun k ↦
      ∏ j ∈ Finset.Icc 1 k, (1 - (d j : ℝ) / (r j : ℝ))
    let mass : ℕ → ℝ := fun j ↦
      S (j - 1) * (d j : ℝ) / (r j : ℝ)
    ∀ k, 1 ≤ k → k ≤ m →
      S k + ∑ j ∈ Finset.Icc 1 k, mass j = 1 := by
  sorry
