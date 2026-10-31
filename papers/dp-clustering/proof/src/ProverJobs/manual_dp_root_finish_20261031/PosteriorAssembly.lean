import Mathlib
open MeasureTheory Filter Topology
open scoped ENNReal
noncomputable section
namespace OfflineDPRoot

/-- The final probability union bound. Low/high-tail estimates and normalization
on a high-probability good event are explicit intermediate proof obligations. -/
theorem posterior_converges_from_tails {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f low high : ℕ → Ω → ℝ) (G : ℕ → Set Ω)
    (hG : Tendsto (fun n => μ (G n)ᶜ) atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop, ∀ ω ∈ G n, |f n ω - 1| ≤ low n ω + high n ω)
    (hLow : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => μ {ω | ε < low n ω}) atTop (𝓝 0))
    (hHigh : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => μ {ω | ε < high n ω}) atTop (𝓝 0)) :
    TendstoInMeasure μ f atTop (fun _ => (1 : ℝ)) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have hε3 : 0 < ε/3 := by linarith
  have hlim := (hG.add (hLow (ε/3) hε3)).add (hHigh (ε/3) hε3)
  simp only [zero_add] at hlim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Filter.Eventually.of_forall (fun n => zero_le _))
  filter_upwards [hbound] with n hn
  calc
    μ {ω | ε ≤ ‖f n ω - 1‖} ≤
        μ ((G n)ᶜ ∪ {ω | ε/3 < low n ω} ∪ {ω | ε/3 < high n ω}) := by
      apply measure_mono
      intro ω hω
      by_cases hωG : ω ∈ G n
      · by_cases hl : ε/3 < low n ω
        · exact Or.inl (Or.inr hl)
        · by_cases hh : ε/3 < high n ω
          · exact Or.inr hh
          · simp only [Set.mem_setOf_eq, Real.norm_eq_abs] at hω
            have := hn ω hωG
            have := not_lt.mp hl
            have := not_lt.mp hh
            linarith
      · exact Or.inl (Or.inl hωG)
    _ ≤ (μ (G n)ᶜ + μ {ω | ε/3 < low n ω}) + μ {ω | ε/3 < high n ω} :=
      (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)

#print axioms posterior_converges_from_tails
end OfflineDPRoot
