import Mathlib

open Set

theorem finite_weighted_bayes_rule
    (m N : ℕ) (hm : 1 ≤ m) (hN : 1 ≤ N)
    (π : Fin m → ℝ)
    (hπ_mem : ∀ j, π j ∈ Icc 0 1)
    (hπ_sum : ∑ j, π j = 1)
    (p : Fin m → Fin N → ℝ)
    (hp_mem : ∀ j x, p j x ∈ Icc 0 1)
    (hp_sum : ∀ j, ∑ x, p j x = 1)
    (w : Fin m → ℝ) (hw : ∀ j, 0 ≤ w j)
    (g : Fin m → ℝ) :
    let D : Fin N → ℝ := fun x ↦ ∑ j, π j * p j x * w j
    (∀ x, 0 < D x) →
    let δstar : Fin N → ℝ := fun x ↦
      (∑ j, π j * p j x * w j * g j) / D x
    let risk : (Fin N → ℝ) → ℝ := fun δ ↦
      ∑ j, π j * ∑ x, p j x * w j * (g j - δ x) ^ 2
    ∀ δ : Fin N → ℝ, risk δstar ≤ risk δ := by
  sorry
