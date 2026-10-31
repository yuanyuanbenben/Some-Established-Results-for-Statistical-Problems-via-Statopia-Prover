import Mathlib

theorem average_jackknife_pseudo_value_sample_variance
    (n : ℕ) (hn : 2 ≤ n)
    (x : Fin n → ℝ) :
    let mean : ℝ := (n : ℝ)⁻¹ * ∑ j, x j
    let V : ℝ := (n : ℝ)⁻¹ * ∑ j, (x j - mean) ^ 2
    let meanMinus : Fin n → ℝ := fun i ↦
      (((n - 1 : ℕ) : ℝ))⁻¹ * ∑ j ∈ Finset.univ.erase i, x j
    let VMinus : Fin n → ℝ := fun i ↦
      (((n - 1 : ℕ) : ℝ))⁻¹ *
        ∑ j ∈ Finset.univ.erase i, (x j - meanMinus i) ^ 2
    let pseudo : Fin n → ℝ := fun i ↦
      (n : ℝ) * V - ((n - 1 : ℕ) : ℝ) * VMinus i
    (n : ℝ)⁻¹ * ∑ i, pseudo i =
      (((n - 1 : ℕ) : ℝ))⁻¹ * ∑ i, (x i - mean) ^ 2 := by
  sorry
