import Mathlib

open Matrix

theorem fisher_linear_discriminant_optimality
    (d : ℕ) (hd : 1 ≤ d)
    (mu₀ mu₁ : Fin d → ℝ) (hmu : mu₀ ≠ mu₁)
    (W : Matrix (Fin d) (Fin d) ℝ)
    (hWsymm : W.IsSymm) (hWpos : W.PosDef) :
    ∀ a : Fin d → ℝ, a ≠ 0 →
      (dotProduct a (mu₁ - mu₀)) ^ 2 /
          dotProduct a (W *ᵥ a) ≤
        dotProduct (mu₁ - mu₀) (W⁻¹ *ᵥ (mu₁ - mu₀)) := by
  sorry
