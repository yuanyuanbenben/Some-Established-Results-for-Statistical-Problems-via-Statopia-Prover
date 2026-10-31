import Mathlib

open MeasureTheory ProbabilityTheory

theorem beta_bernoulli_marginal_likelihood
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (n : ℕ) (hn : 1 ≤ n)
    (x : Fin n → Bool) :
    let s : ℕ := ∑ i, if x i then 1 else 0
    let prior : ℝ → ℝ := fun t ↦
      t ^ (α - 1) * (1 - t) ^ (β - 1) / beta α β
    let likelihood : ℝ → ℝ := fun t ↦
      t ^ s * (1 - t) ^ (n - s)
    let marginal : ℝ :=
      ∫ t in Set.Icc (0 : ℝ) 1, likelihood t * prior t
    marginal = beta (α + s) (β + (n - s)) / beta α β := by
  sorry
