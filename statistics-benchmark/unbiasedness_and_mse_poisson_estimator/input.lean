import Mathlib

open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem unbiasedness_and_mse_poisson_estimator
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (theta a : ℝ) (htheta : 0 < theta) (ha : 0 < a)
    (X : ℕ → Ω → ℕ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X P)
    (n : ℕ) (hn : a < (n : ℝ)) :
    let rate : NNReal := ⟨theta, htheta.le⟩
    (∀ i, IdentDistrib (X i) id P (poissonMeasure rate)) →
    let S : Ω → ℕ :=
      fun ω ↦ ∑ i ∈ Finset.range n, X i ω
    let T : Ω → ℝ :=
      fun ω ↦ (1 - a / (n : ℝ)) ^ S ω
    (∫ ω, T ω ∂P = Real.exp (-a * theta)) ∧
      (∫ ω, (T ω - Real.exp (-a * theta)) ^ 2 ∂P) =
        Real.exp (-2 * a * theta) *
          (Real.exp (a ^ 2 * theta / (n : ℝ)) - 1) := by
  sorry
