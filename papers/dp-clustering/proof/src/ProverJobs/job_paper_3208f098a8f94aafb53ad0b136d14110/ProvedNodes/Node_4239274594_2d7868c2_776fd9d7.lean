import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.Vocabulary
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.Base
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.ProvedNodes.Node_1445702134_3c8d3810_8f7a15fe
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.ProvedNodes.Node_2166343247_005d03d5_e190fc11
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.ProvedNodes.Node_3788355289_2a3e6b7e_b3f2870a
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.ProvedNodes.Node_579847656_e0acc0ed_2e75236f
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.ProvedNodes.Node_905812526_6919174c_47f3b117





open MeasureTheory
open Statlib.Imported

noncomputable section
open MeasureTheory
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_4239274594_2d7868c2 : ∀ (t : ℝ) (ht : 1 ≤ t)
    (s : ℝ) (hs : 1 ≤ s)
    (eps : ℝ) (heps : 0 < eps)
    (n : ℕ) (hn : 1 ≤ n)
    (pi : ℝ → ℝ) (hpi_meas : Measurable pi)
    (hpi_nonneg : ∀ alpha ∈ Set.Ioi (0 : ℝ), 0 ≤ pi alpha)
    (hpi_prob : ∫⁻ alpha in Set.Ioi (0 : ℝ), ENNReal.ofReal (pi alpha) = 1)
    (hpi_tail : 1 / 2 ≤ ∫ alpha in Set.Ioi eps, pi alpha)
    (hint : IntegrableOn (fun alpha : ℝ => alpha ^ (t + s - 1) * pi alpha) (Set.Ioi (0 : ℝ))),
    (if 0 < ∫ alpha in Set.Ioi eps, alpha ^ t / risingFac alpha n * pi alpha
      then (∫ alpha in Set.Ioi eps, alpha ^ (t + s) / risingFac alpha n * pi alpha) /
        (∫ alpha in Set.Ioi eps, alpha ^ t / risingFac alpha n * pi alpha)
      else 0) ≤
      2 * (∫ alpha in Set.Ioi (0 : ℝ), alpha ^ (t + s - 1) * pi alpha) / eps ^ (t - 1) := by
  /- @proof-region region.target-node.session.88302564ce166e68 begin -/
  intro t ht s hs eps heps n hn pi hpi_meas hpi_nonneg hpi_prob hpi_tail hE_fin
  set Bt : ℝ := ∫ alpha in Set.Ioi eps, alpha ^ t / risingFac alpha n * pi alpha with hBt
  set As : ℝ := ∫ alpha in Set.Ioi eps, alpha ^ (t + s) / risingFac alpha n * pi alpha with hAs
  set Et : ℝ := ∫ alpha in Set.Ioi eps, alpha ^ (t + s - 1) * pi alpha with hEt
  set M1 : ℝ := ∫ alpha in Set.Ioi eps, alpha ^ (t - 1) * pi alpha with hM1
  set E : ℝ := ∫ alpha in Set.Ioi (0:ℝ), alpha ^ (t + s - 1) * pi alpha with hE
  have h_asm : AEStronglyMeasurable (fun α : ℝ => α ^ (t + s - 1) * pi α) (volume.restrict (Set.Ioi (0:ℝ))) := by
    have hcont : Continuous fun α : ℝ => α ^ (t + s - 1) :=
      Continuous.rpow_const (f := fun α : ℝ => α) (p := t + s - 1) continuous_id (fun _ => Or.inr (by linarith))
    exact (hcont.measurable.mul hpi_meas).aestronglyMeasurable
  have h_nn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0:ℝ))] (fun α : ℝ => α ^ (t + s - 1) * pi α) :=
    Filter.Eventually.mono (MeasureTheory.self_mem_ae_restrict measurableSet_Ioi)
      (fun α hα => mul_nonneg (le_of_lt (Real.rpow_pos_of_pos hα (t + s - 1))) (hpi_nonneg α hα))
  have h_int : Integrable (fun α : ℝ => α ^ (t + s - 1) * pi α) (volume.restrict (Set.Ioi (0:ℝ))) := hE_fin
  have hden : 0 < eps ^ (t - 1) := Real.rpow_pos_of_pos heps (t - 1)
  have hrf_pos : ∀ α : ℝ, 0 < α → ∀ m : ℕ, 0 < risingFac α m :=
    fun α hα m => statopia_math_node_1445702134_3c8d3810.1 α m hα
  have hAs_nn : 0 ≤ As := by
    rw [hAs]
    apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
    intro α hα
    have hα0 : 0 < α := lt_trans heps hα
    exact mul_nonneg
      (div_nonneg (le_of_lt (Real.rpow_pos_of_pos hα0 (t + s))) (le_of_lt (hrf_pos α hα0 n)))
      (hpi_nonneg α hα0)
  have hBt_nn : 0 ≤ Bt := by
    rw [hBt]
    apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
    intro α hα
    have hα0 : 0 < α := lt_trans heps hα
    exact mul_nonneg
      (div_nonneg (le_of_lt (Real.rpow_pos_of_pos hα0 t)) (le_of_lt (hrf_pos α hα0 n)))
      (hpi_nonneg α hα0)
  have hE_nn : 0 ≤ E := by
    rw [hE]
    apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
    intro α hα
    exact mul_nonneg (le_of_lt (Real.rpow_pos_of_pos hα (t + s - 1))) (hpi_nonneg α hα)
  have h_intpi0 : Integrable (fun α : ℝ => pi α) (volume.restrict (Set.Ioi (0:ℝ))) := by
    have hm : AEStronglyMeasurable (fun α : ℝ => pi α) (volume.restrict (Set.Ioi (0:ℝ))) :=
      hpi_meas.aestronglyMeasurable
    have hn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0:ℝ))] (fun α : ℝ => pi α) :=
      Filter.Eventually.mono (MeasureTheory.self_mem_ae_restrict measurableSet_Ioi)
        (fun x hx => hpi_nonneg x hx)
    have ht : (∫⁻ α : ℝ, ENNReal.ofReal (pi α) ∂(volume.restrict (Set.Ioi (0:ℝ)))) ≠ ⊤ := by
      rw [hpi_prob]
      exact ENNReal.one_ne_top
    exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hm hn).mp ht
  have hsubst : volume.restrict (Set.Ioi eps) ≤ volume.restrict (Set.Ioi (0:ℝ)) :=
    MeasureTheory.Measure.restrict_mono (Set.Ioi_subset_Ioi (le_of_lt heps)) (le_refl volume)
  have h_intpi : Integrable (fun α : ℝ => pi α) (volume.restrict (Set.Ioi eps)) :=
    h_intpi0.mono_measure hsubst
  have h_intf : Integrable (fun α : ℝ => α ^ (t + s - 1) * pi α) (volume.restrict (Set.Ioi eps)) :=
    h_int.mono_measure hsubst
  have hnnE : 0 ≤ᵐ[volume.restrict (Set.Ioi eps)] (fun α : ℝ => pi α) :=
    Filter.Eventually.mono (MeasureTheory.self_mem_ae_restrict measurableSet_Ioi)
      (fun x hx => hpi_nonneg x (lt_trans heps hx))
  have hmeasE : AEStronglyMeasurable (fun α : ℝ => pi α) (volume.restrict (Set.Ioi eps)) :=
    hpi_meas.aestronglyMeasurable
  have hLne : (∫⁻ α in Set.Ioi eps, ENNReal.ofReal (pi α)) ≠ ⊤ :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hmeasE hnnE).mpr h_intpi
  have htailR : (1/2 : ℝ) ≤ ∫ α in Set.Ioi eps, pi α := hpi_tail
  have h_int1 : Integrable (fun α : ℝ => α ^ (t - 1) * pi α) (volume.restrict (Set.Ioi eps)) := by
    have hsum : Integrable (fun α : ℝ => pi α + α ^ (t + s - 1) * pi α) (volume.restrict (Set.Ioi eps)) :=
      h_intpi.add h_intf
    have hm1 : AEStronglyMeasurable (fun α : ℝ => α ^ (t - 1) * pi α) (volume.restrict (Set.Ioi eps)) := by
      have hc : Continuous fun α : ℝ => α ^ (t - 1) :=
        Continuous.rpow_const (f := fun α : ℝ => α) (p := t - 1) continuous_id (fun _ => Or.inr (by linarith))
      exact (hc.measurable.mul hpi_meas).aestronglyMeasurable
    refine hsum.mono' hm1 ?_
    apply Filter.Eventually.mono (MeasureTheory.self_mem_ae_restrict measurableSet_Ioi)
    intro α hα
    have hα0 : 0 < α := lt_trans heps hα
    have hnn1 : 0 ≤ α ^ (t - 1) * pi α :=
      mul_nonneg (le_of_lt (Real.rpow_pos_of_pos hα0 (t - 1))) (hpi_nonneg α hα0)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn1]
    have hkey : α ^ (t - 1) ≤ 1 + α ^ (t + s - 1) := by
      rcases le_total α 1 with h1 | h1
      · have hle : α ^ (t - 1) ≤ 1 := by
          have h := Real.rpow_le_rpow (le_of_lt hα0) h1 (by linarith : (0:ℝ) ≤ t - 1)
          rwa [Real.one_rpow] at h
        have hpos := Real.rpow_pos_of_pos hα0 (t + s - 1)
        linarith
      · have hle : α ^ (t - 1) ≤ α ^ (t + s - 1) :=
          Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
        have hpos := Real.rpow_pos_of_pos hα0 (t + s - 1)
        linarith
    calc α ^ (t - 1) * pi α ≤ (1 + α ^ (t + s - 1)) * pi α :=
          mul_le_mul_of_nonneg_right hkey (hpi_nonneg α hα0)
      _ = pi α + α ^ (t + s - 1) * pi α := by ring
  have h_intc : Integrable (fun α : ℝ => eps ^ (t - 1) * pi α) (volume.restrict (Set.Ioi eps)) :=
    h_intpi.const_mul (eps ^ (t - 1))
  have hmono : ∫ α in Set.Ioi eps, eps ^ (t - 1) * pi α ≤ ∫ α in Set.Ioi eps, α ^ (t - 1) * pi α := by
    apply MeasureTheory.setIntegral_mono_on h_intc h_int1 measurableSet_Ioi
    intro α hα
    have hα0 : 0 < α := lt_trans heps hα
    have hle : eps ^ (t - 1) ≤ α ^ (t - 1) :=
      Real.rpow_le_rpow (le_of_lt heps) (le_of_lt hα) (by linarith : (0:ℝ) ≤ t - 1)
    exact mul_le_mul_of_nonneg_right hle (hpi_nonneg α hα0)
  have hconst : ∫ α in Set.Ioi eps, eps ^ (t - 1) * pi α = eps ^ (t - 1) * ∫ α in Set.Ioi eps, pi α :=
    MeasureTheory.integral_const_mul (eps ^ (t - 1)) pi
  have hM1lb : eps ^ (t - 1) / 2 ≤ M1 := by
    rw [hM1]
    refine le_trans ?_ hmono
    rw [hconst]
    have hp : eps ^ (t - 1) * (1/2) ≤ eps ^ (t - 1) * ∫ α in Set.Ioi eps, pi α :=
      mul_le_mul_of_nonneg_left htailR (le_of_lt hden)
    have he : eps ^ (t - 1) * (1/2) = eps ^ (t - 1) / 2 := by ring
    rwa [he] at hp
  have hEtub : Et ≤ E := by
    rw [hEt, hE]
    exact MeasureTheory.setIntegral_mono_set h_int h_nn (Filter.Eventually.of_forall (fun x hx => lt_trans heps hx))

  have hcheb : M1 * As ≤ Et * Bt := by
    rw [hM1, hAs, hEt, hBt]
    exact statopia_math_node_579847656_e0acc0ed t ht s hs eps heps n hn pi hpi_meas hpi_nonneg h_int
  have hclear : As * eps ^ (t - 1) ≤ 2 * E * Bt := by
    have hle : eps ^ (t - 1) ≤ 2 * M1 := by linarith [hM1lb]
    have h1 : As * eps ^ (t - 1) ≤ As * (2 * M1) := mul_le_mul_of_nonneg_left hle hAs_nn
    have h2 : As * (2 * M1) = 2 * (M1 * As) := by ring
    have h3 : 2 * (M1 * As) ≤ 2 * (Et * Bt) := by
      have hh := mul_le_mul_of_nonneg_left hcheb (by norm_num : (0:ℝ) ≤ 2)
      linarith [hh]
    have h4 : 2 * (Et * Bt) ≤ 2 * (E * Bt) := by
      have hle2 : Et * Bt ≤ E * Bt := mul_le_mul_of_nonneg_right hEtub hBt_nn
      exact mul_le_mul_of_nonneg_left hle2 (by norm_num : (0:ℝ) ≤ 2)
    calc As * eps ^ (t - 1) ≤ As * (2 * M1) := h1
      _ = 2 * (M1 * As) := h2
      _ ≤ 2 * (Et * Bt) := h3
      _ ≤ 2 * (E * Bt) := h4
      _ = 2 * E * Bt := by ring
  by_cases hB : 0 < Bt
  · rw [if_pos hB]
    have hgoal : As / Bt ≤ 2 * E / eps ^ (t - 1) := by
      rw [div_le_iff₀ hB, div_mul_eq_mul_div, le_div_iff₀ hden]
      linarith [hclear]
    exact hgoal
  · rw [if_neg hB]
    have htwo : (0:ℝ) ≤ 2 * E := by linarith [hE_nn]
    exact div_nonneg htwo (le_of_lt hden)
  /- @proof-region region.target-node.session.88302564ce166e68 end -/

end Statlib.Imported
end
