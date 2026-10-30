import Mathlib

open MeasureTheory

theorem kernel_density_normalization
    (n : ℕ) (hn : 1 ≤ n)
    (x : Fin n → ℝ)
    (K : ℝ → ℝ) (hK_meas : Measurable K)
    (hK_nonneg : ∀ u, 0 ≤ K u)
    (hK_int : Integrable K)
    (hK_one : ∫ u, K u = 1)
    (h : ℝ) (hh : 0 < h) :
    let estimate : ℝ → ℝ := fun z ↦
      ((n : ℝ) * h)⁻¹ * ∑ i, K ((x i - z) / h)
    ∫ z, estimate z = 1 := by
  sorry
