import ProverJobs.paper_fresh_20261028t151409527z_hmc_v5.Vocabulary
import ProverJobs.paper_fresh_20261028t151409527z_hmc_v5.Base

namespace PaperProofTasks.paper_fresh_20261028t151409527z_hmc_v5

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal
open _root_.PaperProofTasks.paper_fresh_20261028t151409527z_hmc_v5.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal
namespace Statlib.Imported
open _root_.Statlib

set_option autoImplicit false in
theorem statopia_math_node_760579675_5c0b5f8c : ∀ (d : ℕ) (U : HMCState d → ℝ) (L : ℕ) (ε : ℝ)
    (halpha_nonneg : ∀ (x p : HMCState d), 0 ≤ hmcAlpha U L ε x p)
    (halpha_le_one : ∀ (x p : HMCState d), hmcAlpha U L ε x p ≤ 1)
    (halpha_meas : ∀ x : HMCState d, Measurable fun p => hmcAlpha U L ε x p)
    (hsup : ∀ eta : ℝ, 0 < eta → ∃ R1 : ℝ, ∀ x : HMCState d, R1 < ‖x‖ →
      ∀ p : HMCState d, ‖p‖ ≤ Real.sqrt ‖x‖ → hmcAlpha U L ε x p ≤ eta)
    (gamma : ℝ) (hgamma_pos : 0 < gamma) (hgamma_lt_one : gamma < 1),
    ∃ R : ℝ, ∀ x : HMCState d, R < ‖x‖ →
      1 - gamma ≤ 1 - ∫ p, hmcAlpha U L ε x p ∂(standardGaussianMomentum d) := by
  /- @proof-region region.target-node.session.a92f15a6cc9b744a begin -/
  intro d U L ε halpha_nonneg halpha_le_one halpha_meas hsup gamma hgamma_pos hgamma_lt_one
  set μ : Measure (HMCState d) := standardGaussianMomentum d with hμdef
  have hμ_prob : IsProbabilityMeasure μ := by
    rw [hμdef]
    unfold standardGaussianMomentum
    exact MeasureTheory.Measure.isProbabilityMeasure_map (by measurability)
  haveI := hμ_prob
  have hgamma_half : 0 < gamma / 2 := by linarith
  have htail : ∃ N : ℕ, μ {p : HMCState d | (N : ℝ) < ‖p‖} ≤ ENNReal.ofReal (gamma / 2) := by
    have hanti : Antitone (fun n : ℕ => {p : HMCState d | (n : ℝ) < ‖p‖}) := by
      intro m n hmn p hp
      simp only [Set.mem_setOf_eq] at hp ⊢
      exact lt_of_le_of_lt (by exact_mod_cast hmn) hp
    have hnull : ∀ n : ℕ, NullMeasurableSet {p : HMCState d | (n : ℝ) < ‖p‖} μ := fun n =>
      (measurableSet_lt measurable_const measurable_norm).nullMeasurableSet
    have hfin : ∃ n : ℕ, μ {p : HMCState d | (n : ℝ) < ‖p‖} ≠ ⊤ :=
      ⟨0, measure_ne_top μ _⟩
    have htend : Tendsto (fun n : ℕ => μ {p : HMCState d | (n : ℝ) < ‖p‖}) atTop
        (nhds (μ (⋂ n : ℕ, {p : HMCState d | (n : ℝ) < ‖p‖}))) :=
      tendsto_measure_iInter_atTop hnull hanti hfin
    have hInter : (⋂ n : ℕ, {p : HMCState d | (n : ℝ) < ‖p‖}) = (∅ : Set (HMCState d)) := by
      ext p
      simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_forall]
      obtain ⟨n, hn⟩ := exists_nat_ge ‖p‖
      exact ⟨n, not_lt.mpr hn⟩
    rw [hInter, measure_empty] at htend
    have hmem : Set.Iic (ENNReal.ofReal (gamma / 2)) ∈ nhds (0 : ENNReal) :=
      Iic_mem_nhds (ENNReal.ofReal_pos.mpr hgamma_half)
    have hev : ∀ᶠ n : ℕ in atTop,
        μ {p : HMCState d | (n : ℝ) < ‖p‖} ≤ ENNReal.ofReal (gamma / 2) :=
      htend.eventually hmem
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    exact ⟨N, hN N le_rfl⟩
  obtain ⟨N, hN⟩ := htail
  obtain ⟨R1, hR1⟩ := hsup (gamma / 2) hgamma_half
  refine ⟨max R1 ((N : ℝ) ^ 2), ?_⟩
  intro x hxR
  have hxR1 : R1 < ‖x‖ := lt_of_le_of_lt (le_max_left _ _) hxR
  have hxN : (N : ℝ) ^ 2 < ‖x‖ := lt_of_le_of_lt (le_max_right _ _) hxR
  have hsqrtN : (N : ℝ) < Real.sqrt ‖x‖ := by
    have hstep : Real.sqrt ((N : ℝ) ^ 2) < Real.sqrt ‖x‖ :=
      Real.sqrt_lt_sqrt (sq_nonneg (N : ℝ)) hxN
    rwa [Real.sqrt_sq (Nat.cast_nonneg N)] at hstep
  have hbound : ∫ p, hmcAlpha U L ε x p ∂μ ≤ gamma := by
    set A : Set (HMCState d) := {p : HMCState d | ‖p‖ ≤ Real.sqrt ‖x‖} with hAdef
    have hAmeas : MeasurableSet A := by
      rw [hAdef]
      exact measurableSet_le measurable_norm measurable_const
    have hα_int : Integrable (fun p => hmcAlpha U L ε x p) μ := by
      refine Integrable.of_bound (halpha_meas x).aestronglyMeasurable 1 ?_
      filter_upwards with p
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [halpha_nonneg x p], halpha_le_one x p⟩
    have hsplit : ∫ p, hmcAlpha U L ε x p ∂μ
        = ∫ p in A, hmcAlpha U L ε x p ∂μ + ∫ p in Aᶜ, hmcAlpha U L ε x p ∂μ :=
      (integral_add_compl hAmeas hα_int).symm
    have hball : ∫ p in A, hmcAlpha U L ε x p ∂μ ≤ gamma / 2 := by
      have hleA : μ A ≤ 1 := by
        have h1 : μ Set.univ = 1 := measure_univ
        rw [← h1]
        exact measure_mono (Set.subset_univ A)
      have hmono : ∫ p in A, hmcAlpha U L ε x p ∂μ
          ≤ ∫ p in A, (gamma / 2 : ℝ) ∂μ := by
        apply setIntegral_mono_on
        · exact hα_int.integrableOn
        · exact integrable_const (gamma / 2)
        · exact hAmeas
        · intro p hp
          exact hR1 x hxR1 p (by simpa [hAdef] using hp)
      calc ∫ p in A, hmcAlpha U L ε x p ∂μ
          ≤ ∫ p in A, (gamma / 2 : ℝ) ∂μ := hmono
        _ = (μ A).toReal * (gamma / 2) := by rw [setIntegral_const, smul_eq_mul]; rfl
        _ ≤ 1 * (gamma / 2) := by
            apply mul_le_mul_of_nonneg_right _ (le_of_lt hgamma_half)
            calc (μ A).toReal ≤ (1 : ENNReal).toReal :=
                  ENNReal.toReal_mono ENNReal.one_ne_top hleA
              _ = 1 := ENNReal.toReal_one
        _ = gamma / 2 := by ring
    have htail_le : μ Aᶜ ≤ ENNReal.ofReal (gamma / 2) := by
      refine le_trans (measure_mono ?_) hN
      intro p hp
      simp only [Set.mem_compl_iff, hAdef, Set.mem_setOf_eq, not_le] at hp ⊢
      exact lt_trans hsqrtN hp
    have htail_bound : ∫ p in Aᶜ, hmcAlpha U L ε x p ∂μ ≤ gamma / 2 := by
      have hmono : ∫ p in Aᶜ, hmcAlpha U L ε x p ∂μ
          ≤ ∫ p in Aᶜ, (1 : ℝ) ∂μ := by
        apply setIntegral_mono_on
        · exact hα_int.integrableOn
        · exact integrable_const (1 : ℝ)
        · exact hAmeas.compl
        · intro p _
          exact halpha_le_one x p
      calc ∫ p in Aᶜ, hmcAlpha U L ε x p ∂μ
          ≤ ∫ p in Aᶜ, (1 : ℝ) ∂μ := hmono
        _ = (μ Aᶜ).toReal * 1 := by rw [setIntegral_const, smul_eq_mul]; rfl
        _ = (μ Aᶜ).toReal := by ring
        _ ≤ gamma / 2 := by
            have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top htail_le
            rwa [ENNReal.toReal_ofReal (le_of_lt hgamma_half)] at h
    rw [hsplit]
    linarith [hball, htail_bound]
  linarith [hbound]
  /- @proof-region region.target-node.session.a92f15a6cc9b744a end -/

end Statlib.Imported
end

