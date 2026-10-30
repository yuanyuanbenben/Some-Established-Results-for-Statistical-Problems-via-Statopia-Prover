import Mathlib

open MeasureTheory

theorem sequential_brier_risk_decomposition
    {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T : ℕ) (hT : 1 ≤ T)
    (filtration : ℕ → MeasurableSpace Ω)
    (hfiltration : ∀ s t, s ≤ t → t ≤ T →
      filtration s ≤ filtration t)
    (hsub : ∀ t ≤ T, filtration t ≤ m)
    (Y p q : ℕ → Ω → ℝ)
    (hYmeas : ∀ t, 1 ≤ t → t ≤ T →
      StronglyMeasurable[filtration t] (Y t))
    (hYzeroOne : ∀ t, 1 ≤ t → t ≤ T →
      ∀ ω, Y t ω = 0 ∨ Y t ω = 1)
    (hYint : ∀ t, 1 ≤ t → t ≤ T → Integrable (Y t) P)
    (hqmeas : ∀ t, 1 ≤ t → t ≤ T →
      StronglyMeasurable[filtration (t - 1)] (q t))
    (hqint : ∀ t, 1 ≤ t → t ≤ T → Integrable (q t) P)
    (hp : ∀ t, 1 ≤ t → t ≤ T →
      p t =ᵐ[P] condExp (filtration (t - 1)) P (Y t))
    (hqbounds : ∀ t, 1 ≤ t → t ≤ T →
      ∀ᵐ ω ∂P, 0 ≤ q t ω ∧ q t ω ≤ 1) :
    ∫ ω, ∑ t ∈ Finset.Icc 1 T, (Y t ω - q t ω) ^ 2 ∂P =
      ∫ ω, ∑ t ∈ Finset.Icc 1 T, (Y t ω - p t ω) ^ 2 ∂P +
        ∫ ω, ∑ t ∈ Finset.Icc 1 T, (q t ω - p t ω) ^ 2 ∂P := by
  sorry
