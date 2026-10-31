import ProverJobs.job_paper_c93669ef201447419b92d6591d8bc1aa.Vocabulary
import ProverJobs.job_paper_c93669ef201447419b92d6591d8bc1aa.Base

open Statlib.Imported
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators

namespace Statlib.Imported
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators

set_option autoImplicit false in
theorem statopia_math_node_4114883645_8b1ad159 : ∀ (t : ℕ) (ht : 1 ≤ t)
    (c : ℝ) (hc : 0 < c)
    (θstar : Fin t → ℝ)
    (g : ℝ → ℝ) (M : ℝ) (hM : 0 < M)
    (hg_nonneg : ∀ x : ℝ, 0 ≤ g x)
    (hg_le : ∀ x ∈ Set.Icc (-c) c, g x ≤ M)
    (hg_zero : ∀ x : ℝ, x ∉ Set.Icc (-c) c → g x = 0)
    (p : Fin t → ℝ) (hp_pos : ∀ j : Fin t, 0 < p j)
    (hp_sum : ∑ j : Fin t, p j = 1)
    (Rcomp : Fin t → Measure ℝ)
    (hRcomp_dens : ∀ j : Fin t,
      Rcomp j = volume.withDensity (fun x : ℝ => ENNReal.ofReal (g (x - θstar j))))
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_meas : ∀ i : ℕ, Measurable (X i))
    (hX_law : ∀ i : ℕ, Measure.map (X i) μ = mixLaw p Rcomp),
      ∀ᵐ ω ∂μ,
        (∀ (i : ℕ) (j : Fin t), X i ω - θstar j ≠ c ∧ X i ω - θstar j ≠ -c) ∧
        (∀ (i : ℕ) (j : Fin t),
          X i ω - θstar j ∈ Set.Icc (-c) c → X i ω - θstar j ∈ Set.Ioo (-c) c) ∧
        (∀ (i : ℕ) (j : Fin t),
          X i ω ∈ Set.Icc (θstar j - c) (θstar j + c) →
            X i ω ∈ Set.Ioo (θstar j - c) (θstar j + c)) := by
  /- @proof-region region.target-node.session.2ada993313986a10 begin -/
  intro t ht c hc θstar g M hM hg_nonneg hg_le hg_zero p hp_pos hp_sum Rcomp hRcomp_dens Ω instΩ μ instμ X hX_meas hX_law
  have hbound : ∀ x : ℝ, g x ≤ M := by
    intro x
    by_cases hx : x ∈ Set.Icc (-c) c
    · exact hg_le x hx
    · rw [hg_zero x hx]
      exact hM.le
  have hRcomp_zero : ∀ (j : Fin t) (y : ℝ), Rcomp j {y} = 0 := by
    intro j y
    have hden : Rcomp j {y} = ∫⁻ x in {y}, ENNReal.ofReal (g (x - θstar j)) ∂volume := by
      rw [hRcomp_dens j, MeasureTheory.withDensity_apply]
      exact MeasurableSet.singleton y
    rw [hden]
    have hz : ENNReal.ofReal M * volume {y} = 0 := by rw [Real.volume_singleton, mul_zero]
    have hle : ∫⁻ x in {y}, ENNReal.ofReal (g (x - θstar j)) ∂volume ≤ 0 := by
      calc ∫⁻ x in {y}, ENNReal.ofReal (g (x - θstar j)) ∂volume
          ≤ ∫⁻ x in {y}, ENNReal.ofReal M ∂volume :=
            MeasureTheory.setLIntegral_mono measurable_const
              (fun x _ => ENNReal.ofReal_le_ofReal (hbound (x - θstar j)))
        _ = ENNReal.ofReal M * volume {y} := MeasureTheory.setLIntegral_const {y} (ENNReal.ofReal M)
        _ = 0 := hz
    exact le_antisymm hle bot_le
  have hmix_zero : ∀ y : ℝ, mixLaw p Rcomp {y} = 0 := by
    intro y
    have hsum : mixLaw p Rcomp {y} = ∑ j : Fin t, ENNReal.ofReal (p j) * Rcomp j {y} := by
      unfold mixLaw
      rw [MeasureTheory.Measure.finset_sum_apply]
      simp
    rw [hsum]
    simp [hRcomp_zero]
  have hpre : ∀ (i : ℕ) (y : ℝ), μ {ω : Ω | X i ω = y} = 0 := by
    intro i y
    calc μ {ω : Ω | X i ω = y} = Measure.map (X i) μ {y} := by
          rw [MeasureTheory.Measure.map_apply (hX_meas i) (MeasurableSet.singleton y)]
          rfl
      _ = mixLaw p Rcomp {y} := by rw [hX_law i]
      _ = 0 := hmix_zero y
  have hshift1 : ∀ (i : ℕ) (j : Fin t),
      {ω : Ω | X i ω - θstar j = c} = {ω : Ω | X i ω = θstar j + c} := by
    intro i j
    ext ω
    simp only [Set.mem_setOf_eq]
    constructor <;> intro h <;> linarith
  have hshift2 : ∀ (i : ℕ) (j : Fin t),
      {ω : Ω | X i ω - θstar j = -c} = {ω : Ω | X i ω = θstar j - c} := by
    intro i j
    ext ω
    simp only [Set.mem_setOf_eq]
    constructor <;> intro h <;> linarith
  have hB : μ (⋃ i : ℕ, ⋃ j : Fin t,
      ({ω : Ω | X i ω - θstar j = c} ∪ {ω : Ω | X i ω - θstar j = -c})) = 0 := by
    rw [MeasureTheory.measure_iUnion_null_iff]
    intro i
    rw [MeasureTheory.measure_iUnion_null_iff]
    intro j
    rw [MeasureTheory.measure_union_null_iff]
    constructor
    · rw [hshift1 i j]
      exact hpre i (θstar j + c)
    · rw [hshift2 i j]
      exact hpre i (θstar j - c)
  have h1 : ∀ᵐ ω ∂μ, ∀ (i : ℕ) (j : Fin t), X i ω - θstar j ≠ c ∧ X i ω - θstar j ≠ -c := by
    rw [MeasureTheory.ae_iff]
    refine measure_mono_null ?_ hB
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    push_neg at hω
    obtain ⟨i, j, hij⟩ := hω
    by_cases hc' : X i ω - θstar j = c
    · exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j, Set.mem_union_left _ hc'⟩⟩
    · exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j, Set.mem_union_right _ (hij hc')⟩⟩
  have h2 : ∀ᵐ ω ∂μ, ∀ (i : ℕ) (j : Fin t),
      X i ω - θstar j ∈ Set.Icc (-c) c → X i ω - θstar j ∈ Set.Ioo (-c) c := by
    filter_upwards [h1] with ω hω i j hij
    obtain ⟨hne1, hne2⟩ := hω i j
    rw [Set.mem_Icc] at hij
    exact Set.mem_Ioo.mpr ⟨lt_of_le_of_ne hij.1 (Ne.symm hne2), lt_of_le_of_ne hij.2 hne1⟩
  have h3 : ∀ᵐ ω ∂μ, ∀ (i : ℕ) (j : Fin t),
      X i ω ∈ Set.Icc (θstar j - c) (θstar j + c) →
        X i ω ∈ Set.Ioo (θstar j - c) (θstar j + c) := by
    filter_upwards [h1] with ω hω i j hij
    obtain ⟨hne1, hne2⟩ := hω i j
    rw [Set.mem_Icc] at hij
    exact Set.mem_Ioo.mpr
      ⟨lt_of_le_of_ne hij.1 (by intro h; exact hne2 (by linarith)),
       lt_of_le_of_ne hij.2 (by intro h; exact hne1 (by linarith))⟩
  filter_upwards [h1, h2, h3] with ω h1ω h2ω h3ω
  exact ⟨h1ω, h2ω, h3ω⟩
  /- @proof-region region.target-node.session.2ada993313986a10 end -/

end Statlib.Imported
