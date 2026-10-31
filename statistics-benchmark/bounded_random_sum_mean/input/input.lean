import Mathlib

open MeasureTheory ProbabilityTheory

theorem bounded_random_sum_mean
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : ℕ) (hm : 1 ≤ m)
    (N : Ω → ℕ) (hN_meas : Measurable N)
    (hN_bound : ∀ ω, N ω ≤ m)
    (X : Fin m → Ω → ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_int : ∀ i, Integrable (X i) P)
    (μ : ℝ) (hX_mean : ∀ i, ∫ ω, X i ω ∂P = μ)
    (h_indep : IndepFun N (fun ω i ↦ X i ω) P) :
    let S : Ω → ℝ := fun ω ↦
      ∑ i : Fin m, if i.1 + 1 ≤ N ω then X i ω else 0
    let NReal : Ω → ℝ := fun ω ↦ N ω
    ∫ ω, S ω ∂P = μ * ∫ ω, NReal ω ∂P := by
  sorry
