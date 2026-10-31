import Mathlib

open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem complete_case_mean_conditionally_unbiased_under_mcar
    {Ω : Type*}
    [MeasurableSpace Ω]
    (P : Measure Ω)
    [IsProbabilityMeasure P]
    (n : ℕ)
    (hn : 1 ≤ n)
    (μ : ℝ)
    (Y : Fin n → Ω → ℝ)
    (R : Fin n → Ω → Bool)
    (hYmeas : ∀ i, Measurable (Y i))
    (hYint : ∀ i, Integrable (Y i) P)
    (hYmean : ∀ i, ∫ ω, Y i ω ∂P = μ)
    (hRmeas : ∀ i, Measurable (R i))
    (hIndep :
      IndepFun (fun ω i ↦ R i ω) (fun ω i ↦ Y i ω) P) :
    let K : Ω → ℕ := fun ω ↦ ∑ i, if R i ω then 1 else 0
    let μhat : Ω → ℝ := fun ω ↦
      if 0 < K ω then
        (∑ i, if R i ω then Y i ω else 0) / (K ω : ℝ)
      else 0
    0 < P {ω | 0 < K ω} →
      (∫ ω, if 0 < K ω then μhat ω else 0 ∂P) /
          (P {ω | 0 < K ω}).toReal = μ := by
  sorry
