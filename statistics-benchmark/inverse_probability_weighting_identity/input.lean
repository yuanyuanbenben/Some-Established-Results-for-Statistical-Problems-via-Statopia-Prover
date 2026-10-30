import Mathlib

open MeasureTheory

theorem inverse_probability_weighting_identity
    {Ω 𝒵 : Type*}
    [MeasurableSpace Ω]
    [Fintype 𝒵]
    [MeasurableSpace 𝒵]
    [MeasurableSingletonClass 𝒵]
    (P : Measure Ω)
    [IsProbabilityMeasure P]
    (T : Ω → Bool)
    (Z : Ω → 𝒵)
    (hTmeas : Measurable T)
    (hZmeas : Measurable Z)
    (a : Bool)
    (hZpos : ∀ z, 0 < P {ω | Z ω = z})
    (hepos :
      ∀ z, 0 <
        (P {ω | T ω = a ∧ Z ω = z}).toReal / (P {ω | Z ω = z}).toReal) :
    let e : 𝒵 → ℝ := fun z ↦
      (P {ω | T ω = a ∧ Z ω = z}).toReal / (P {ω | Z ω = z}).toReal
    ∀ h : 𝒵 → ℝ,
      ∫ ω, (if T ω = a then (1 : ℝ) else 0) * h (Z ω) / e (Z ω) ∂P =
        ∫ ω, h (Z ω) ∂P := by
  sorry
