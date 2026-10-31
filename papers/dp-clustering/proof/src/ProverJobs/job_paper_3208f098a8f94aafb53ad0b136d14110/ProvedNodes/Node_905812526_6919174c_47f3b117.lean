import Statlib.StatFoundation.BasicAnalysis.ENNRealBridge
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.Vocabulary
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.Base

open MeasureTheory
open Statlib.Imported

noncomputable section
open MeasureTheory
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_905812526_6919174c : ∀ (π : ℝ → ℝ) (hπ_meas : Measurable π)
    (hπ_nonneg : ∀ α ∈ Set.Ioi (0 : ℝ), 0 ≤ π α)
    (hπ_prob : ∫⁻ α in Set.Ioi (0 : ℝ), ENNReal.ofReal (π α) = 1)
    (hπ_int : IntegrableOn π (Set.Ioi (0 : ℝ)))
    (ε δ β : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hβ : 0 < β)
    (hB1 : δ * ε ^ (β + 1) / (β + 1) ≤ 1 / 2)
    (hA2 : ∀ α ∈ Set.Ioo (0 : ℝ) ε, π α ≤ δ * α ^ β),
    (∫ α in Set.Ioo (0 : ℝ) ε, π α) ≤ 1 / 2 ∧
      1 / 2 ≤ ∫ α in Set.Ioi ε, π α := by
  /- @proof-region region.target-node.session.5632306a93f2eaa6 begin -/
  intro pi h_pi_meas h_pi_nonneg h_pi_prob h_pi_int eps delta beta h_eps h_delta h_beta hB1 hA2
  have h_ae_nonneg : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] pi := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with a ha
    exact h_pi_nonneg a ha
  have h_fin : MeasureTheory.HasFiniteIntegral pi (volume.restrict (Set.Ioi (0 : ℝ))) := by
    rw [MeasureTheory.hasFiniteIntegral_iff_ofReal h_ae_nonneg]
    rw [h_pi_prob]
    exact ENNReal.one_lt_top
  have h_int_total : MeasureTheory.IntegrableOn pi (Set.Ioi (0 : ℝ)) volume :=
    ⟨h_pi_meas.aestronglyMeasurable, h_fin⟩
  have h_total : ∫ a in Set.Ioi (0 : ℝ), pi a = 1 := by
    rw [Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.integral_eq_lintegral_toReal_of_nonneg h_ae_nonneg h_int_total]
    rw [h_pi_prob]
    simp
  have hb : MeasureTheory.Integrable (fun a : ℝ => a ^ beta) (volume.restrict (Set.Ioo (0 : ℝ) eps)) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff (s := beta) h_eps).2 (by linarith)
  have hg : MeasureTheory.IntegrableOn (fun a : ℝ => delta * a ^ beta) (Set.Ioo (0 : ℝ) eps) volume := by
    have hm := hb.const_mul delta
    simpa [smul_eq_mul] using hm
  have hpi : MeasureTheory.IntegrableOn pi (Set.Ioo (0 : ℝ) eps) volume :=
    h_int_total.mono_set (by intro x hx; exact hx.1)
  have hmono : ∫ a in Set.Ioo (0 : ℝ) eps, pi a ≤ ∫ a in Set.Ioo (0 : ℝ) eps, delta * a ^ beta :=
    MeasureTheory.setIntegral_mono_on hpi hg measurableSet_Ioo hA2
  have hrpow : ∫ a in (0 : ℝ)..eps, a ^ beta = eps ^ (beta + 1) / (beta + 1) := by
    rw [integral_rpow (Or.inl (show (-1 : ℝ) < beta by linarith))]
    rw [Real.zero_rpow (by linarith : beta + 1 ≠ 0)]
    simp
  have hval : ∫ a in Set.Ioo (0 : ℝ) eps, delta * a ^ beta = delta * eps ^ (beta + 1) / (beta + 1) := by
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le h_eps.le]
    rw [intervalIntegral.integral_const_mul, hrpow]
    ring
  have hfirst : ∫ a in Set.Ioo (0 : ℝ) eps, pi a ≤ 1 / 2 := by
    have h1 := hmono
    rw [hval] at h1
    exact le_trans h1 hB1
  have h_tail_int : MeasureTheory.IntegrableOn pi (Set.Ioi eps) volume :=
    h_int_total.mono_set (by intro x hx; exact lt_trans h_eps hx)
  have hsplit : (∫ x in (0 : ℝ)..eps, pi x) + (∫ x in Set.Ioi eps, pi x) = ∫ x in Set.Ioi (0 : ℝ), pi x :=
    intervalIntegral.integral_interval_add_Ioi h_int_total h_tail_int
  have h_interval_le : (∫ x in (0 : ℝ)..eps, pi x) ≤ 1 / 2 := by
    rw [intervalIntegral.integral_of_le h_eps.le]
    rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]
    exact hfirst
  have htail : 1 / 2 ≤ ∫ x in Set.Ioi eps, pi x := by
    have heq : (∫ x in Set.Ioi eps, pi x) = 1 - (∫ x in (0 : ℝ)..eps, pi x) := by
      have h2 := hsplit
      rw [h_total] at h2
      linarith
    rw [heq]
    linarith
  exact ⟨hfirst, htail⟩
  /- @proof-region region.target-node.session.5632306a93f2eaa6 end -/

end Statlib.Imported
end
