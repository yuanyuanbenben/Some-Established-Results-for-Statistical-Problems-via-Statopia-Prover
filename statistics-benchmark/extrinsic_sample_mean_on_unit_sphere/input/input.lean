import Mathlib

open Matrix

theorem extrinsic_sample_mean_on_unit_sphere
    (d n : ℕ) (hd : 2 ≤ d) (hn : 1 ≤ n)
    (x : Fin n → Fin d → ℝ)
    (hx : ∀ i, dotProduct (x i) (x i) = 1) :
    let xBar : Fin d → ℝ := (n : ℝ)⁻¹ • ∑ i, x i
    xBar ≠ 0 →
      let objective : (Fin d → ℝ) → ℝ := fun p ↦
        (n : ℝ)⁻¹ *
          ∑ i, dotProduct (x i - p) (x i - p)
      {p : Fin d → ℝ |
        dotProduct p p = 1 ∧
          ∀ q, dotProduct q q = 1 → objective p ≤ objective q} =
        {((Real.sqrt (dotProduct xBar xBar))⁻¹ : ℝ) • xBar} := by
  sorry
