import Statlib.StatFoundation.BasicAnalysis.ENNRealBridge
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.Vocabulary
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.Base
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.ProvedNodes.Node_1445702134_3c8d3810_8f7a15fe
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.ProvedNodes.Node_3788355289_2a3e6b7e_b3f2870a


open MeasureTheory
open Statlib.Imported

noncomputable section
open MeasureTheory
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_1866815261_49718380 : ∀ (t : ℝ) (ht : 1 ≤ t)
    (π : ℝ → ℝ) (hπ_meas : Measurable π)
    (hπ_nonneg : ∀ α ∈ Set.Ioi (0 : ℝ), 0 ≤ π α)
    (hπ_prob : ∫⁻ α in Set.Ioi (0 : ℝ), ENNReal.ofReal (π α) = 1)
    (ε δ β : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hβ : 0 < β)
    (hA2 : ∀ α ∈ Set.Ioo (0 : ℝ) ε, δ⁻¹ * α ^ β ≤ π α ∧ π α ≤ δ * α ^ β),
    0 < risingFac ε (Nat.ceil (t + 1)) * ε ^ (t - (Nat.ceil (t + 1) : ℝ)) /
        (∫ α in Set.Ioo (0 : ℝ) ε, α ^ t * π α) ∧
      ∀ n : ℕ, Nat.ceil (t + 1) ≤ n →
        (∫ α in Set.Ioi ε, α ^ t / risingFac α n * π α) ≤
          (risingFac ε (Nat.ceil (t + 1)) * ε ^ (t - (Nat.ceil (t + 1) : ℝ)) /
              (∫ α in Set.Ioo (0 : ℝ) ε, α ^ t * π α)) *
            (∫ α in Set.Ioo (0 : ℝ) ε, α ^ t / risingFac α n * π α) := by
  /- @proof-region region.target-node.session.83535d72d602e65e begin -/
  intro t ht π hπ_meas hπ_nonneg hπ_prob ε δ β hε hδ hβ hA2
  obtain ⟨rfa_pos, rfa_ge, rfa_fact, rfa_monoOn, rfa_mono, rfa_posEps, rfa_rest⟩ := statopia_math_node_1445702134_3c8d3810
  set K : ℕ := Nat.ceil (t + 1) with hKdef
  set D : ℝ := ∫ α in Set.Ioo (0:ℝ) ε, α ^ t * π α with hDdef
  set M : ℝ := risingFac ε K * ε ^ (t - (K:ℝ)) / D with hMdef
  have hKge : t + 1 ≤ (K:ℝ) := by rw [hKdef]; exact Nat.le_ceil (t + 1)
  have hFacKpos : 0 < risingFac ε K := rfa_pos ε K hε
  have hEpspow_pos : 0 < ε ^ (t - (K:ℝ)) := Real.rpow_pos_of_pos hε _
  have hApos : 0 < risingFac ε K * ε ^ (t - (K:ℝ)) := mul_pos hFacKpos hEpspow_pos
  have hDpos : 0 < D := by
    rw [hDdef]
    have hbase : IntegrableOn (fun α : ℝ => α ^ (t + β)) (Set.Ioo (0:ℝ) ε) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff hε).mpr (by linarith)
    have hg : IntegrableOn (fun α : ℝ => δ * α ^ (t + β)) (Set.Ioo (0:ℝ) ε) := hbase.const_mul δ
    have hf_int : IntegrableOn (fun α : ℝ => α ^ t * π α) (Set.Ioo (0:ℝ) ε) := by
      refine MeasureTheory.Integrable.mono hg ?_ ?_
      · exact ((continuous_id.rpow_const (fun x => Or.inr (show (0:ℝ) ≤ t by linarith))).measurable.mul hπ_meas).aestronglyMeasurable
      · filter_upwards [MeasureTheory.self_mem_ae_restrict (measurableSet_Ioo (a := (0:ℝ)) (b := ε))] with a ha
        have ha0 : (0:ℝ) < a := ha.1
        have hπa := hA2 a ha
        have hδinv_pos : 0 < δ⁻¹ := inv_pos.mpr hδ
        have haz : 0 < a ^ β := Real.rpow_pos_of_pos ha0 β
        have hπpos : 0 < π a := lt_of_lt_of_le (mul_pos hδinv_pos haz) hπa.1
        have hle : a ^ t * π a ≤ δ * a ^ (t + β) := by
          calc a ^ t * π a ≤ a ^ t * (δ * a ^ β) := mul_le_mul_of_nonneg_left hπa.2 (Real.rpow_nonneg ha0.le t)
            _ = δ * a ^ (t + β) := by rw [Real.rpow_add ha0 t β]; ring
        have hkey : ‖a ^ t * π a‖ ≤ ‖δ * a ^ (t + β)‖ := by
          calc ‖a ^ t * π a‖ = a ^ t * π a := by rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ha0.le t) hπpos.le)]
            _ ≤ δ * a ^ (t + β) := hle
            _ = ‖δ * a ^ (t + β)‖ := by rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hδ.le (Real.rpow_nonneg ha0.le (t + β)))]
        exact hkey
    have hae : 0 ≤ᵐ[volume.restrict (Set.Ioo (0:ℝ) ε)] (fun α : ℝ => α ^ t * π α) := by
      filter_upwards [MeasureTheory.self_mem_ae_restrict (measurableSet_Ioo (a := (0:ℝ)) (b := ε))] with a ha
      have ha0 : (0:ℝ) < a := ha.1
      have hπa := hA2 a ha
      have hδinv_pos : 0 < δ⁻¹ := inv_pos.mpr hδ
      have haz : 0 < a ^ β := Real.rpow_pos_of_pos ha0 β
      exact mul_nonneg (Real.rpow_nonneg ha0.le t) (le_of_lt (lt_of_lt_of_le (mul_pos hδinv_pos haz) hπa.1))
    rw [MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae hae hf_int]
    have hsupp : Set.Ioo (0:ℝ) ε ⊆ Function.support (fun α : ℝ => α ^ t * π α) := by
      intro a ha
      have ha0 : (0:ℝ) < a := ha.1
      have hπa := hA2 a ha
      have hδinv_pos : 0 < δ⁻¹ := inv_pos.mpr hδ
      have haz : 0 < a ^ β := Real.rpow_pos_of_pos ha0 β
      have hπpos : 0 < π a := lt_of_lt_of_le (mul_pos hδinv_pos haz) hπa.1
      exact Function.mem_support.mpr (ne_of_gt (mul_pos (Real.rpow_pos_of_pos ha0 t) hπpos))
    have hsub : Set.Ioo (0:ℝ) ε ⊆ Function.support (fun α : ℝ => α ^ t * π α) ∩ Set.Ioo (0:ℝ) ε :=
      Set.subset_inter hsupp (subset_refl _)
    have hvol : volume (Set.Ioo (0:ℝ) ε) = ENNReal.ofReal ε := by
      rw [Real.volume_Ioo, sub_zero]
    have hpos' : 0 < volume (Set.Ioo (0:ℝ) ε) := by
      rw [hvol]; exact ENNReal.ofReal_pos.mpr hε
    exact lt_of_lt_of_le hpos' (measure_mono hsub)
  refine ⟨?_, ?_⟩
  · exact div_pos hApos hDpos
  · intro n hn
    have hn1 : ((1:ℕ):ℝ) + t ≤ (n:ℝ) := by
      have h1 : (K:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
      push_cast
      linarith
    obtain ⟨_, _, hBn_int, Bpos, _, _, hBtn_int, Bnonneg, _⟩ :=
      statopia_math_node_3788355289_2a3e6b7e t ht π hπ_meas hπ_nonneg hπ_prob ε δ β hε hδ hβ hA2 n 1 le_rfl hn1
    have hαt_meas : Measurable (fun α : ℝ => α ^ t) :=
      (continuous_id.rpow_const (fun x => Or.inr (show (0:ℝ) ≤ t by linarith))).measurable
    have hπ_int0 : IntegrableOn π (Set.Ioi (0:ℝ)) := by
      refine (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable (μ := volume.restrict (Set.Ioi (0:ℝ))) hπ_meas.aestronglyMeasurable ?_).mp ?_
      · filter_upwards [MeasureTheory.self_mem_ae_restrict (measurableSet_Ioi (a := (0:ℝ)))] with a ha
        exact hπ_nonneg a ha
      · rw [hπ_prob]; exact ENNReal.one_ne_top
    have hπ_tail : IntegrableOn π (Set.Ioi ε) :=
      hπ_int0.mono_set (Set.Ioi_subset_Ioi hε.le)
    have hπ_mass : (∫ α in Set.Ioi ε, π α) ≤ 1 := by
      have h1 : (∫ α in Set.Ioi (0:ℝ), π α) = 1 := by
        have hmem : 0 ≤ᶠ[ae (volume.restrict (Set.Ioi (0:ℝ)))] π := by
          filter_upwards [MeasureTheory.self_mem_ae_restrict (measurableSet_Ioi (a := (0:ℝ)))] with a ha
          exact hπ_nonneg a ha
        rw [Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.integral_eq_lintegral_toReal_of_nonneg hmem hπ_int0]
        rw [hπ_prob]
        simp
      calc (∫ α in Set.Ioi ε, π α) ≤ ∫ α in Set.Ioi (0:ℝ), π α := by
              apply MeasureTheory.setIntegral_mono_set hπ_int0
              · filter_upwards [MeasureTheory.self_mem_ae_restrict (measurableSet_Ioi (a := (0:ℝ)))] with a ha
                exact hπ_nonneg a ha
              · exact Filter.Eventually.of_forall (fun a ha => lt_trans hε ha)
        _ = 1 := h1
    have hetap : IntegrableOn (fun α : ℝ => α ^ t * π α) (Set.Ioo (0:ℝ) ε) := by
      have hbase : IntegrableOn (fun α : ℝ => α ^ (t + β)) (Set.Ioo (0:ℝ) ε) :=
        (intervalIntegral.integrableOn_Ioo_rpow_iff hε).mpr (by linarith)
      have hg2 : IntegrableOn (fun α : ℝ => δ * α ^ (t + β)) (Set.Ioo (0:ℝ) ε) := hbase.const_mul δ
      refine MeasureTheory.Integrable.mono hg2 ?_ ?_
      · exact (hαt_meas.mul hπ_meas).aestronglyMeasurable
      · filter_upwards [MeasureTheory.self_mem_ae_restrict (measurableSet_Ioo (a := (0:ℝ)) (b := ε))] with a ha
        have ha0 : (0:ℝ) < a := ha.1
        have hπa := hA2 a ha
        have hδinv_pos : 0 < δ⁻¹ := inv_pos.mpr hδ
        have haz : 0 < a ^ β := Real.rpow_pos_of_pos ha0 β
        have hπpos : 0 < π a := lt_of_lt_of_le (mul_pos hδinv_pos haz) hπa.1
        have hle : a ^ t * π a ≤ δ * a ^ (t + β) := by
          calc a ^ t * π a ≤ a ^ t * (δ * a ^ β) := mul_le_mul_of_nonneg_left hπa.2 (Real.rpow_nonneg ha0.le t)
            _ = δ * a ^ (t + β) := by rw [Real.rpow_add ha0 t β]; ring
        have hkey : ‖a ^ t * π a‖ ≤ ‖δ * a ^ (t + β)‖ := by
          calc ‖a ^ t * π a‖ = a ^ t * π a := by rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ha0.le t) hπpos.le)]
            _ ≤ δ * a ^ (t + β) := hle
            _ = ‖δ * a ^ (t + β)‖ := by rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hδ.le (Real.rpow_nonneg ha0.le (t + β)))]
        exact hkey
    have rfsucc : ∀ (a : ℝ) (j : ℕ), risingFac a (j+1) = risingFac a j * (a + (j:ℝ)) := by
      intro a j
      unfold risingFac
      rw [Finset.prod_range_succ]
    have hprod : ∀ (a : ℝ), 0 < a → ε ≤ a → risingFac ε n * a ^ K ≤ risingFac ε K * risingFac a n := by
      intro a ha0 hae
      have hgen : ∀ m : ℕ, risingFac ε (K + m) * a ^ K ≤ risingFac ε K * risingFac a (K + m) := by
        intro m
        induction m with
        | zero =>
            simp only [Nat.add_zero]
            exact mul_le_mul_of_nonneg_left (rfa_ge a K ha0) (le_of_lt hFacKpos)
        | succ m ih =>
            rw [Nat.add_succ, Nat.succ_eq_add_one]
            rw [rfsucc ε (K + m), rfsucc a (K + m)]
            calc risingFac ε (K + m) * (ε + (↑(K + m))) * a ^ K
                = (risingFac ε (K + m) * a ^ K) * (ε + (↑(K + m))) := by ring
              _ ≤ (risingFac ε K * risingFac a (K + m)) * (ε + (↑(K + m))) := by
                  apply mul_le_mul_of_nonneg_right ih (by positivity)
              _ = risingFac ε K * (risingFac a (K + m) * (ε + (↑(K + m)))) := by ring
              _ ≤ risingFac ε K * (risingFac a (K + m) * (a + (↑(K + m)))) := by
                  apply mul_le_mul_of_nonneg_left _ (le_of_lt hFacKpos)
                  exact mul_le_mul_of_nonneg_left (by linarith) (le_of_lt (rfa_pos a (K + m) ha0))
      have h := hgen (n - K)
      rw [show K + (n - K) = n from by omega] at h
      exact h
    have hpoint : ∀ a ∈ Set.Ioi ε, a ^ t / risingFac a n * π a ≤ (risingFac ε K / risingFac ε n) * (a ^ (t - (K:ℝ)) * π a) := by
      intro a ha
      have ha0 : (0:ℝ) < a := lt_trans hε ha
      have hae : ε ≤ a := le_of_lt ha
      have hpa : (0:ℝ) ≤ π a := hπ_nonneg a (lt_trans hε ha)
      have hpownn : (0:ℝ) ≤ a ^ (t - (K:ℝ)) := Real.rpow_nonneg ha0.le (t - (K:ℝ))
      have han_pos : (0:ℝ) < risingFac a n := rfa_pos a n ha0
      have hrεn_pos : (0:ℝ) < risingFac ε n := rfa_pos ε n hε
      have hpK : a ^ K * a ^ (t - (K:ℝ)) = a ^ t := by
        rw [← Real.rpow_natCast a K, ← Real.rpow_add ha0]
        congr 1
        ring
      have hcross : risingFac ε n * a ^ K * a ^ (t - (K:ℝ)) ≤ risingFac ε K * risingFac a n * a ^ (t - (K:ℝ)) :=
        mul_le_mul_of_nonneg_right (hprod a ha0 hae) hpownn
      have hcross2 : a ^ t * risingFac ε n ≤ risingFac ε K * a ^ (t - (K:ℝ)) * risingFac a n := by
        have e1 : risingFac ε n * a ^ K * a ^ (t - (K:ℝ)) = a ^ t * risingFac ε n := by
          rw [mul_assoc, hpK]
          exact mul_comm (risingFac ε n) (a ^ t)
        have e2 : risingFac ε K * risingFac a n * a ^ (t - (K:ℝ)) = risingFac ε K * a ^ (t - (K:ℝ)) * risingFac a n := by
          ring
        rw [← e1, ← e2]
        exact hcross
      have hbase : a ^ t / risingFac a n ≤ (risingFac ε K / risingFac ε n) * a ^ (t - (K:ℝ)) := by
        rw [div_le_iff₀ han_pos]
        have heq : (risingFac ε K / risingFac ε n) * a ^ (t - (K:ℝ)) * risingFac a n
            = risingFac ε K * a ^ (t - (K:ℝ)) * risingFac a n / risingFac ε n := by
          ring_nf
        rw [heq]
        exact (le_div_iff₀' hrεn_pos).mpr (by rw [mul_comm (risingFac ε n) (a ^ t)]; exact hcross2)
      calc a ^ t / risingFac a n * π a
          ≤ ((risingFac ε K / risingFac ε n) * a ^ (t - (K:ℝ))) * π a := mul_le_mul_of_nonneg_right hbase hpa
        _ = (risingFac ε K / risingFac ε n) * (a ^ (t - (K:ℝ)) * π a) := by ring
    have hAK_meas : Measurable (fun a : ℝ => a ^ K) := (continuous_id.pow K).measurable
    have hAtK_meas : Measurable (fun a : ℝ => a ^ t / a ^ K * π a) := (hαt_meas.div hAK_meas).mul hπ_meas
    have hεtK_nn : (0:ℝ) ≤ ε ^ (t - (K:ℝ)) := le_of_lt hEpspow_pos
    have hgt : IntegrableOn (fun a : ℝ => ε ^ (t - (K:ℝ)) * π a) (Set.Ioi ε) := hπ_tail.const_mul (ε ^ (t - (K:ℝ)))
    have hcongr : (fun a : ℝ => a ^ t / a ^ K * π a) =ᶠ[ae (volume.restrict (Set.Ioi ε))] (fun a : ℝ => a ^ (t - (K:ℝ)) * π a) := by
      filter_upwards [MeasureTheory.self_mem_ae_restrict (measurableSet_Ioi (a := ε))] with a ha
      have ha0 : (0:ℝ) < a := lt_trans hε ha
      have h : a ^ (t - (K:ℝ)) = a ^ t / a ^ K := by
        rw [Real.rpow_sub ha0, Real.rpow_natCast]
      rw [h]
    have hAtK_meas' : AEStronglyMeasurable (fun a : ℝ => a ^ (t - (K:ℝ)) * π a) (volume.restrict (Set.Ioi ε)) :=
      hAtK_meas.aestronglyMeasurable.congr hcongr
    have htK_int : IntegrableOn (fun a : ℝ => a ^ (t - (K:ℝ)) * π a) (Set.Ioi ε) := by
      refine MeasureTheory.Integrable.mono hgt hAtK_meas' ?_
      filter_upwards [MeasureTheory.self_mem_ae_restrict (measurableSet_Ioi (a := ε))] with a ha
      have ha0 : (0:ℝ) < a := lt_trans hε ha
      have hae : ε ≤ a := le_of_lt ha
      have hπnn : (0:ℝ) ≤ π a := hπ_nonneg a (lt_trans hε ha)
      have hle : a ^ (t - (K:ℝ)) ≤ ε ^ (t - (K:ℝ)) := Real.rpow_le_rpow_of_nonpos hε hae (by linarith [hKge])
      have htl : (0:ℝ) ≤ a ^ (t - (K:ℝ)) := Real.rpow_nonneg ha0.le _
      have hkey : ‖a ^ (t - (K:ℝ)) * π a‖ ≤ ‖ε ^ (t - (K:ℝ)) * π a‖ := by
        calc ‖a ^ (t - (K:ℝ)) * π a‖ = a ^ (t - (K:ℝ)) * π a := by rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg htl hπnn)]
          _ ≤ ε ^ (t - (K:ℝ)) * π a := mul_le_mul_of_nonneg_right hle hπnn
          _ = ‖ε ^ (t - (K:ℝ)) * π a‖ := by rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hεtK_nn hπnn)]
      exact hkey
    have htail_bound : (∫ a in Set.Ioi ε, a ^ (t - (K:ℝ)) * π a) ≤ ε ^ (t - (K:ℝ)) := by
      have hstep : (∫ a in Set.Ioi ε, a ^ (t - (K:ℝ)) * π a) ≤ ∫ a in Set.Ioi ε, ε ^ (t - (K:ℝ)) * π a := by
        apply MeasureTheory.setIntegral_mono_on htK_int hgt measurableSet_Ioi
        intro a ha
        have hae : ε ≤ a := le_of_lt ha
        have hle : a ^ (t - (K:ℝ)) ≤ ε ^ (t - (K:ℝ)) := Real.rpow_le_rpow_of_nonpos hε hae (by linarith [hKge])
        exact mul_le_mul_of_nonneg_right hle (hπ_nonneg a (lt_trans hε ha))
      calc (∫ a in Set.Ioi ε, a ^ (t - (K:ℝ)) * π a) ≤ ∫ a in Set.Ioi ε, ε ^ (t - (K:ℝ)) * π a := hstep
        _ = ε ^ (t - (K:ℝ)) * (∫ a in Set.Ioi ε, π a) := by rw [MeasureTheory.integral_const_mul]
        _ ≤ ε ^ (t - (K:ℝ)) * 1 := mul_le_mul_of_nonneg_left hπ_mass hεtK_nn
        _ = ε ^ (t - (K:ℝ)) := mul_one _
    have hUp : (∫ α in Set.Ioi ε, α ^ t / risingFac α n * π α) ≤ risingFac ε K * ε ^ (t - (K:ℝ)) / risingFac ε n := by
      have hstep1 : (∫ α in Set.Ioi ε, α ^ t / risingFac α n * π α) ≤ ∫ α in Set.Ioi ε, (risingFac ε K / risingFac ε n) * (α ^ (t - (K:ℝ)) * π α) :=
        MeasureTheory.setIntegral_mono_on hBtn_int (htK_int.const_mul (risingFac ε K / risingFac ε n)) measurableSet_Ioi hpoint
      have hstep2 : (∫ α in Set.Ioi ε, (risingFac ε K / risingFac ε n) * (α ^ (t - (K:ℝ)) * π α)) = (risingFac ε K / risingFac ε n) * (∫ α in Set.Ioi ε, α ^ (t - (K:ℝ)) * π α) := by
        rw [MeasureTheory.integral_const_mul]
      calc (∫ α in Set.Ioi ε, α ^ t / risingFac α n * π α)
          ≤ ∫ α in Set.Ioi ε, (risingFac ε K / risingFac ε n) * (α ^ (t - (K:ℝ)) * π α) := hstep1
        _ = (risingFac ε K / risingFac ε n) * (∫ α in Set.Ioi ε, α ^ (t - (K:ℝ)) * π α) := hstep2
        _ ≤ (risingFac ε K / risingFac ε n) * ε ^ (t - (K:ℝ)) := mul_le_mul_of_nonneg_left htail_bound (div_nonneg (le_of_lt hFacKpos) (le_of_lt (rfa_pos ε n hε)))
        _ = risingFac ε K * ε ^ (t - (K:ℝ)) / risingFac ε n := by ring_nf
    have hLow : D / risingFac ε n ≤ ∫ α in Set.Ioo (0:ℝ) ε, α ^ t / risingFac α n * π α := by
      have hr_pos : (0:ℝ) < risingFac ε n := rfa_pos ε n hε
      have hf1 : IntegrableOn (fun α : ℝ => (risingFac ε n)⁻¹ * (α ^ t * π α)) (Set.Ioo (0:ℝ) ε) :=
        hetap.const_mul _
      have hle : (fun α : ℝ => (risingFac ε n)⁻¹ * (α ^ t * π α)) ≤ᶠ[ae (volume.restrict (Set.Ioo (0:ℝ) ε))] (fun α : ℝ => α ^ t / risingFac α n * π α) := by
        filter_upwards [MeasureTheory.self_mem_ae_restrict (measurableSet_Ioo (a := (0:ℝ)) (b := ε))] with a ha
        have ha0 : (0:ℝ) < a := ha.1
        have haε : a ≤ ε := le_of_lt ha.2
        have hfac_le : risingFac a n ≤ risingFac ε n := rfa_mono n a ε ha0 haε
        have hfac_pos : (0:ℝ) < risingFac a n := rfa_pos a n ha0
        have hπa := hA2 a ha
        have hδinv_pos : 0 < δ⁻¹ := inv_pos.mpr hδ
        have haz : 0 < a ^ β := Real.rpow_pos_of_pos ha0 β
        have hπpos : 0 < π a := lt_of_lt_of_le (mul_pos hδinv_pos haz) hπa.1
        have htp : (0:ℝ) ≤ a ^ t * π a := mul_nonneg (Real.rpow_nonneg ha0.le t) hπpos.le
        have hinv : (risingFac ε n)⁻¹ ≤ (risingFac a n)⁻¹ := (inv_le_inv₀ hr_pos hfac_pos).mpr hfac_le
        calc (risingFac ε n)⁻¹ * (a ^ t * π a) ≤ (risingFac a n)⁻¹ * (a ^ t * π a) := mul_le_mul_of_nonneg_right hinv htp
          _ = a ^ t / risingFac a n * π a := by rw [div_eq_mul_inv]; ring
      have hmono := MeasureTheory.setIntegral_mono_ae_restrict hf1 hBn_int hle
      rw [MeasureTheory.integral_const_mul] at hmono
      rw [← hDdef] at hmono
      have hgoal : D / risingFac ε n = (risingFac ε n)⁻¹ * D := by rw [div_eq_inv_mul]
      rw [hgoal]
      exact hmono
    clear hMdef
    have hADpos : (0:ℝ) < risingFac ε K * ε ^ (t - (K:ℝ)) / D := div_pos hApos hDpos
    have hkey : risingFac ε K * ε ^ (t - (K:ℝ)) / risingFac ε n
        ≤ (risingFac ε K * ε ^ (t - (K:ℝ)) / D) * (∫ α in Set.Ioo (0:ℝ) ε, α ^ t / risingFac α n * π α) := by
      calc risingFac ε K * ε ^ (t - (K:ℝ)) / risingFac ε n
          = (risingFac ε K * ε ^ (t - (K:ℝ)) / D) * (D / risingFac ε n) := by
              field_simp [hDpos.ne', (rfa_pos ε n hε).ne']
        _ ≤ (risingFac ε K * ε ^ (t - (K:ℝ)) / D) * (∫ α in Set.Ioo (0:ℝ) ε, α ^ t / risingFac α n * π α) :=
              mul_le_mul_of_nonneg_left hLow (le_of_lt hADpos)
    exact le_trans hUp hkey
  /- @proof-region region.target-node.session.83535d72d602e65e end -/

end Statlib.Imported
end
