import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.Definitions
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M031_Vocabulary
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M032_Base
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M036_Node_3788355289_2a3e6b7e_b3f2870a

/- Original module ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.ProvedNodes.Node_1497788876_00e778c3_68730201; genuine source relocated, namespace-isolated only. -/
namespace DPCompletedProof
open _root_.Statlib.Imported

open MeasureTheory
open Statlib.Imported

noncomputable section
open MeasureTheory
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_1497788876_00e778c3 : ∀ (t : ℝ) (ht : 1 ≤ t)
    (π : ℝ → ℝ) (hπ_meas : Measurable π)
    (hπ_nonneg : ∀ α ∈ Set.Ioi (0 : ℝ), 0 ≤ π α)
    (hπ_prob : ∫⁻ α in Set.Ioi (0 : ℝ), ENNReal.ofReal (π α) = 1)
    (ε δ β : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hβ : 0 < β)
    (hA2 : ∀ α ∈ Set.Ioo (0 : ℝ) ε, δ⁻¹ * α ^ β ≤ π α ∧ π α ≤ δ * α ^ β)
    (n s : ℕ) (hs : 1 ≤ s) (hns : (s : ℝ) + t ≤ (n : ℝ)),
    Cratio π n t (s : ℝ) =
      ENNReal.ofReal
        (((∫ α in Set.Ioo (0 : ℝ) ε, α ^ (t + (s : ℝ)) / risingFac α n * π α) +
            (∫ α in Set.Ioi ε, α ^ (t + (s : ℝ)) / risingFac α n * π α)) /
          ((∫ α in Set.Ioo (0 : ℝ) ε, α ^ t / risingFac α n * π α) +
            (∫ α in Set.Ioi ε, α ^ t / risingFac α n * π α))) := by
  /- @proof-region region.target-node.session.38940f16a3368d6a begin -/
  intro t ht π hπ_meas hπ_nonneg hπ_prob ε δ β hε hδ hβ hA2 n s hs hns
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := statopia_math_node_3788355289_2a3e6b7e t ht π hπ_meas hπ_nonneg hπ_prob ε δ β hε hδ hβ hA2 n s hs hns
  have hdenpos : 0 < (∫ α in Set.Ioo (0 : ℝ) ε, α ^ t / risingFac α n * π α) +
      (∫ α in Set.Ioi ε, α ^ t / risingFac α n * π α) := by linarith
  have hnum : priorRatioIntegral π (t + (s : ℝ)) n =
      ENNReal.ofReal ((∫ α in Set.Ioo (0 : ℝ) ε, α ^ (t + (s : ℝ)) / risingFac α n * π α) +
        (∫ α in Set.Ioi ε, α ^ (t + (s : ℝ)) / risingFac α n * π α)) := by
    have hg_meas : Measurable (fun α : ℝ => α ^ (t + (s : ℝ)) / risingFac α n * π α) := by
      unfold risingFac
      measurability
    have hg_nonneg : ∀ α ∈ Set.Ioi (0 : ℝ), 0 ≤ α ^ (t + (s : ℝ)) / risingFac α n * π α := by
      intro α hα
      have hα0 : 0 < α := hα
      have hrf : 0 < risingFac α n := by
        unfold risingFac
        exact Finset.prod_pos (fun k _ => by
          have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
          linarith)
      exact mul_nonneg
        (div_nonneg (le_of_lt (Real.rpow_pos_of_pos hα0 (t + (s : ℝ)))) (le_of_lt hrf))
        (hπ_nonneg α hα0)
    have hint_Ioo : IntegrableOn (fun α : ℝ => α ^ (t + (s : ℝ)) / risingFac α n * π α) (Set.Ioo (0 : ℝ) ε) := h1
    have hint_Ioi : IntegrableOn (fun α : ℝ => α ^ (t + (s : ℝ)) / risingFac α n * π α) (Set.Ioi ε) := h5
    have hint_sing : IntegrableOn (fun α : ℝ => α ^ (t + (s : ℝ)) / risingFac α n * π α) ({ε} : Set ℝ) :=
      MeasureTheory.IntegrableOn.of_measure_zero (by simp)
    have hint_Ioc : IntegrableOn (fun α : ℝ => α ^ (t + (s : ℝ)) / risingFac α n * π α) (Set.Ioc (0 : ℝ) ε) := by
      have hset : Set.Ioo (0 : ℝ) ε ∪ ({ε} : Set ℝ) = Set.Ioc (0 : ℝ) ε := by
        ext x
        simp only [Set.mem_union, Set.mem_Ioo, Set.mem_singleton_iff, Set.mem_Ioc]
        constructor
        · rintro (⟨ha, hb⟩ | hb)
          · exact ⟨ha, le_of_lt hb⟩
          · rw [hb]; exact ⟨hε, le_refl ε⟩
        · rintro ⟨ha, hb⟩
          rcases lt_or_eq_of_le hb with hc | hc
          · exact Or.inl ⟨ha, hc⟩
          · exact Or.inr hc
      rw [← hset]
      exact MeasureTheory.IntegrableOn.union hint_Ioo hint_sing
    have hint_Ioi0 : IntegrableOn (fun α : ℝ => α ^ (t + (s : ℝ)) / risingFac α n * π α) (Set.Ioi (0 : ℝ)) := by
      have hset : Set.Ioc (0 : ℝ) ε ∪ Set.Ioi ε = Set.Ioi (0 : ℝ) := by
        ext x
        simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
        constructor
        · rintro (⟨ha, _⟩ | hb)
          · exact ha
          · linarith
        · intro ha
          by_cases hc : x ≤ ε
          · exact Or.inl ⟨ha, hc⟩
          · push_neg at hc; exact Or.inr hc
      rw [← hset]
      exact MeasureTheory.IntegrableOn.union hint_Ioc hint_Ioi
    have hnn_Ioi0 : 0 ≤ᶠ[ae (volume.restrict (Set.Ioi (0 : ℝ)))]
        (fun α : ℝ => α ^ (t + (s : ℝ)) / risingFac α n * π α) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
      exact hg_nonneg x hx
    have hsplit : ∫ α in Set.Ioi (0 : ℝ), α ^ (t + (s : ℝ)) / risingFac α n * π α =
        (∫ α in Set.Ioo (0 : ℝ) ε, α ^ (t + (s : ℝ)) / risingFac α n * π α) +
        (∫ α in Set.Ioi ε, α ^ (t + (s : ℝ)) / risingFac α n * π α) := by
      have hdisj : Disjoint (Set.Ioc (0 : ℝ) ε) (Set.Ioi ε) := by
        rw [Set.disjoint_left]
        intro x hx1 hx2
        exact absurd hx1.2 (not_le_of_gt hx2)
      have hunion : Set.Ioc (0 : ℝ) ε ∪ Set.Ioi ε = Set.Ioi (0 : ℝ) := by
        ext x
        simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
        constructor
        · rintro (⟨ha, _⟩ | hb)
          · exact ha
          · linarith
        · intro ha
          by_cases hc : x ≤ ε
          · exact Or.inl ⟨ha, hc⟩
          · push_neg at hc; exact Or.inr hc
      rw [← hunion,
        MeasureTheory.setIntegral_union hdisj measurableSet_Ioi hint_Ioc hint_Ioi,
        MeasureTheory.integral_Ioc_eq_integral_Ioo]
    unfold priorRatioIntegral
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint_Ioi0 hnn_Ioi0, hsplit]
  have hden : priorRatioIntegral π t n =
      ENNReal.ofReal ((∫ α in Set.Ioo (0 : ℝ) ε, α ^ t / risingFac α n * π α) +
        (∫ α in Set.Ioi ε, α ^ t / risingFac α n * π α)) := by
    have hg_meas : Measurable (fun α : ℝ => α ^ t / risingFac α n * π α) := by
      unfold risingFac
      measurability
    have hg_nonneg : ∀ α ∈ Set.Ioi (0 : ℝ), 0 ≤ α ^ t / risingFac α n * π α := by
      intro α hα
      have hα0 : 0 < α := hα
      have hrf : 0 < risingFac α n := by
        unfold risingFac
        exact Finset.prod_pos (fun k _ => by
          have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
          linarith)
      exact mul_nonneg (div_nonneg (le_of_lt (Real.rpow_pos_of_pos hα0 t)) (le_of_lt hrf))
        (hπ_nonneg α hα0)
    have hint_Ioo : IntegrableOn (fun α : ℝ => α ^ t / risingFac α n * π α) (Set.Ioo (0 : ℝ) ε) := h3
    have hint_Ioi : IntegrableOn (fun α : ℝ => α ^ t / risingFac α n * π α) (Set.Ioi ε) := h7
    have hint_sing : IntegrableOn (fun α : ℝ => α ^ t / risingFac α n * π α) ({ε} : Set ℝ) :=
      MeasureTheory.IntegrableOn.of_measure_zero (by simp)
    have hint_Ioc : IntegrableOn (fun α : ℝ => α ^ t / risingFac α n * π α) (Set.Ioc (0 : ℝ) ε) := by
      have hset : Set.Ioo (0 : ℝ) ε ∪ ({ε} : Set ℝ) = Set.Ioc (0 : ℝ) ε := by
        ext x
        simp only [Set.mem_union, Set.mem_Ioo, Set.mem_singleton_iff, Set.mem_Ioc]
        constructor
        · rintro (⟨h1, h2⟩ | h2)
          · exact ⟨h1, le_of_lt h2⟩
          · rw [h2]; exact ⟨hε, le_refl ε⟩
        · rintro ⟨h1, h2⟩
          rcases lt_or_eq_of_le h2 with h | h
          · exact Or.inl ⟨h1, h⟩
          · exact Or.inr h
      rw [← hset]
      exact MeasureTheory.IntegrableOn.union hint_Ioo hint_sing
    have hint_Ioi0 : IntegrableOn (fun α : ℝ => α ^ t / risingFac α n * π α) (Set.Ioi (0 : ℝ)) := by
      have hset : Set.Ioc (0 : ℝ) ε ∪ Set.Ioi ε = Set.Ioi (0 : ℝ) := by
        ext x
        simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
        constructor
        · rintro (⟨h1, _⟩ | h2)
          · exact h1
          · linarith
        · intro h1
          by_cases h : x ≤ ε
          · exact Or.inl ⟨h1, h⟩
          · push_neg at h; exact Or.inr h
      rw [← hset]
      exact MeasureTheory.IntegrableOn.union hint_Ioc hint_Ioi
    have hnn_Ioi0 : 0 ≤ᶠ[ae (volume.restrict (Set.Ioi (0 : ℝ)))]
        (fun α : ℝ => α ^ t / risingFac α n * π α) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
      exact hg_nonneg x hx
    have hsplit : ∫ α in Set.Ioi (0 : ℝ), α ^ t / risingFac α n * π α =
        (∫ α in Set.Ioo (0 : ℝ) ε, α ^ t / risingFac α n * π α) +
        (∫ α in Set.Ioi ε, α ^ t / risingFac α n * π α) := by
      have hdisj : Disjoint (Set.Ioc (0 : ℝ) ε) (Set.Ioi ε) := by
        rw [Set.disjoint_left]
        intro x hx1 hx2
        exact absurd hx1.2 (not_le_of_gt hx2)
      have hunion : Set.Ioc (0 : ℝ) ε ∪ Set.Ioi ε = Set.Ioi (0 : ℝ) := by
        ext x
        simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
        constructor
        · rintro (⟨h1, _⟩ | h2)
          · exact h1
          · linarith
        · intro h1
          by_cases h : x ≤ ε
          · exact Or.inl ⟨h1, h⟩
          · push_neg at h; exact Or.inr h
      rw [← hunion,
        MeasureTheory.setIntegral_union hdisj measurableSet_Ioi hint_Ioc hint_Ioi,
        MeasureTheory.integral_Ioc_eq_integral_Ioo]
    unfold priorRatioIntegral
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint_Ioi0 hnn_Ioi0, hsplit]
  show priorRatioIntegral π (t + (s : ℝ)) n / priorRatioIntegral π t n =
      ENNReal.ofReal
        (((∫ α in Set.Ioo (0 : ℝ) ε, α ^ (t + (s : ℝ)) / risingFac α n * π α) +
            (∫ α in Set.Ioi ε, α ^ (t + (s : ℝ)) / risingFac α n * π α)) /
          ((∫ α in Set.Ioo (0 : ℝ) ε, α ^ t / risingFac α n * π α) +
            (∫ α in Set.Ioi ε, α ^ t / risingFac α n * π α)))
  rw [hnum, hden, ENNReal.ofReal_div_of_pos hdenpos]
  /- @proof-region region.target-node.session.38940f16a3368d6a end -/

end Statlib.Imported
end
end DPCompletedProof
