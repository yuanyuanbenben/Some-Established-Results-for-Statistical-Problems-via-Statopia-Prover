import Mathlib

open MeasureTheory
open scoped BigOperators ENNReal

theorem sample_maximum_sufficient
    (n : ℕ)
    (hn : 1 ≤ n) :
    let Θ := Set.Ioi (0 : ℝ)
    let ν : Measure (Fin n → ℝ) :=
      Measure.pi (fun _ : Fin n ↦ (volume : Measure ℝ))
    let f : Θ → (Fin n → ℝ) → ℝ≥0∞ := fun θ x ↦
      ∏ i, if x i ∈ Set.Ioo (0 : ℝ) θ.1 then
        (ENNReal.ofReal θ.1)⁻¹
      else 0
    let P : Θ → Measure (Fin n → ℝ) := fun θ ↦
      ν.withDensity (f θ)
    let M : (Fin n → ℝ) → ℝ := fun x ↦
      sSup (Set.range x)
    let h : (Fin n → ℝ) → ℝ≥0∞ := fun x ↦
      if ∀ i, 0 < x i then 1 else 0
    let g : Θ → ℝ → ℝ≥0∞ := fun θ m ↦
      if m < θ.1 then ((ENNReal.ofReal θ.1)⁻¹) ^ n else 0
    Measurable M ∧
      (∀ θ, Measurable (f θ) ∧ IsProbabilityMeasure (P θ)) ∧
      ∀ θ x, f θ x = h x * g θ (M x) := by
  sorry
