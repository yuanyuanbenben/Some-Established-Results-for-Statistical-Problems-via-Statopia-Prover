import Mathlib

open Matrix

theorem axial_extrinsic_mean_leading_eigenvector
    (d n : ℕ) (hd : 2 ≤ d) (hn : 1 ≤ n)
    (x : Fin n → Fin d → ℝ)
    (hx : ∀ i, dotProduct (x i) (x i) = 1)
    (v : Fin d → ℝ) (hv : dotProduct v v = 1)
    (lambda : ℝ) :
    let A : Matrix (Fin d) (Fin d) ℝ :=
      (n : ℝ)⁻¹ • ∑ i, vecMulVec (x i) (x i)
    A *ᵥ v = lambda • v →
    (∀ u, dotProduct u u = 1 →
      dotProduct u (A *ᵥ u) ≤ lambda) →
    (∀ u, A *ᵥ u = lambda • u →
      ∃ c : ℝ, u = c • v) →
      let objective : (Fin d → ℝ) → ℝ := fun u ↦
        (n : ℝ)⁻¹ *
          ∑ i, ∑ j, ∑ k,
            (u j * u k - x i j * x i k) ^ 2
      {u : Fin d → ℝ |
        dotProduct u u = 1 ∧
          ∀ w, dotProduct w w = 1 → objective u ≤ objective w} =
        {v, -v} := by
  sorry
