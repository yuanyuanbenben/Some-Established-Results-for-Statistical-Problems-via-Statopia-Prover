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
theorem statopia_math_node_1797268609_53e08000 : ∀ (t : ℝ) (ht : 1 ≤ t)
    (s : ℕ) (hs : 1 ≤ s)
    (π : ℝ → ℝ) (hπ_meas : Measurable π)
    (hπ_nonneg : ∀ α ∈ Set.Ioi (0 : ℝ), 0 ≤ π α)
    (hπ_prob : ∫⁻ α in Set.Ioi (0 : ℝ), ENNReal.ofReal (π α) = 1)
    (ε δ β : ℝ) (hε : 0 < ε) (hε_lt : ε < 1 / 2) (hδ : 0 < δ) (hβ : 0 < β)
    (hA2 : ∀ α ∈ Set.Ioo (0 : ℝ) ε, δ⁻¹ * α ^ β ≤ π α ∧ π α ≤ δ * α ^ β)
    (hB1 : δ * ε ^ (β + 1) / (β + 1) ≤ 1 / 2),
    ((∫ α in Set.Ioo (0 : ℝ) ε, α ^ β) = ε ^ (β + 1) / (β + 1)) ∧
    ((∫ α in Set.Ioo (0 : ℝ) ε, π α) ≤ δ * ε ^ (β + 1) / (β + 1) ∧
      δ * ε ^ (β + 1) / (β + 1) ≤ 1 / 2) ∧
    ((∫ α in Set.Ioi ε, π α) = 1 - (∫ α in Set.Ioo (0 : ℝ) ε, π α) ∧
      1 / 2 ≤ (∫ α in Set.Ioi ε, π α)) ∧
    (IntegrableOn (fun α : ℝ => α ^ (t + (s : ℝ) - 1) * π α) (Set.Ioo (0 : ℝ) ε) ∧
      (∫ α in Set.Ioo (0 : ℝ) ε, α ^ (t + (s : ℝ) - 1) * π α) ≤
        ε ^ (t + (s : ℝ) - 1) * (1 / 2)) ∧
    (ENNReal.ofReal (ε ^ (t + (s : ℝ) - 1) / 2) ≤ priorMoment π (t + (s : ℝ) - 1) ∧
      (priorMoment π (t + (s : ℝ) - 1) ≠ ⊤ →
        ε ^ (t + (s : ℝ) - 1) / 2 ≤ (priorMoment π (t + (s : ℝ) - 1)).toReal) ∧
      (priorMoment π (t + (s : ℝ) - 1) ≠ ⊤ →
        ε ^ (t + (s : ℝ) - 1) / 2 ≤
          ∫ α in Set.Ioi (0 : ℝ), α ^ (t + (s : ℝ) - 1) * π α)) := by
  /- @proof-region region.target-node.session.cace72e46d830a27 begin -/
  intro t ht s hs π hπ_meas hπ_nonneg hπ_prob ε δ β hε hε_lt hδ hβ hA2 hB1
  have hπnn : 0 ≤ᶠ[ae (volume.restrict (Set.Ioi (0:ℝ)))] π := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with α hα
    exact hπ_nonneg α hα
  have hπne : (∫⁻ α in Set.Ioi (0:ℝ), ENNReal.ofReal (π α)) ≠ ⊤ := by
    rw [hπ_prob]
    simp
  have hπ_int : IntegrableOn π (Set.Ioi (0:ℝ)) :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hπ_meas.aestronglyMeasurable hπnn).mp hπne
  have hπ_mass : (∫ α in Set.Ioi (0:ℝ), π α) = 1 := by
    have hbridge : (∫⁻ α in Set.Ioi (0:ℝ), ENNReal.ofReal (π α)).toReal
        = ∫ α in Set.Ioi (0:ℝ), π α :=
      Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.lintegral_toReal_eq_integral_of_nonneg hπnn hπ_int
    rw [hπ_prob] at hbridge
    simpa using hbridge.symm
  have hpow : (∫ α in Set.Ioo (0:ℝ) ε, α ^ β) = ε ^ (β + 1) / (β + 1) := by
    have hconv : (∫ α in Set.Ioo (0:ℝ) ε, α ^ β) = ∫ α in (0:ℝ)..ε, α ^ β := by
      rw [intervalIntegral.integral_of_le (le_of_lt hε),
        MeasureTheory.integral_Ioc_eq_integral_Ioo]
    have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) ε,
        HasDerivAt (fun y : ℝ => y ^ (β + 1) / (β + 1)) (x ^ β) x := by
      intro x hx
      have hb1 : β + 1 ≠ 0 := by linarith
      have h1 : HasDerivAt (fun y : ℝ => y ^ (β + 1)) ((β + 1) * x ^ (β + 1 - 1)) x :=
        Real.hasDerivAt_rpow_const (Or.inr (by linarith : (1:ℝ) ≤ β + 1))
      have h3 : ((β + 1) * x ^ (β + 1 - 1)) / (β + 1) = x ^ β := by
        rw [show β + 1 - 1 = β by ring]
        field_simp
      have h2 : HasDerivAt (fun y : ℝ => y ^ (β + 1) / (β + 1)) (x ^ β) x := by
        have h2' := h1.div_const (β + 1)
        rwa [h3] at h2'
      exact h2
    have hint : IntervalIntegrable (fun x : ℝ => x ^ β) volume (0:ℝ) ε :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith)
    have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    rw [hconv, hfund, Real.zero_rpow (by linarith : β + 1 ≠ 0)]
    ring
  have hbound : (∫ α in Set.Ioo (0:ℝ) ε, π α) ≤ δ * ε ^ (β + 1) / (β + 1) := by
    have hπIoo : IntegrableOn π (Set.Ioo (0:ℝ) ε) :=
      hπ_int.mono_set (fun x hx => hx.1)
    have hpowIoo : IntegrableOn (fun x : ℝ => x ^ β) (Set.Ioo (0:ℝ) ε) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff hε).mpr (by linarith)
    have hmono : (∫ α in Set.Ioo (0:ℝ) ε, π α) ≤
        ∫ α in Set.Ioo (0:ℝ) ε, δ * α ^ β :=
      MeasureTheory.setIntegral_mono_on hπIoo (hpowIoo.const_mul δ) measurableSet_Ioo
        (fun x hx => (hA2 x hx).2)
    have hlin : (∫ α in Set.Ioo (0:ℝ) ε, δ * α ^ β) =
        δ * ∫ α in Set.Ioo (0:ℝ) ε, α ^ β := by
      have hsm := MeasureTheory.integral_smul
        (μ := volume.restrict (Set.Ioo (0:ℝ) ε)) δ (fun α : ℝ => α ^ β)
      simpa [smul_eq_mul] using hsm
    rw [hlin, hpow] at hmono
    calc (∫ α in Set.Ioo (0:ℝ) ε, π α) ≤ δ * (ε ^ (β + 1) / (β + 1)) := hmono
      _ = δ * ε ^ (β + 1) / (β + 1) := by ring
  have hdecomp : (∫ α in Set.Ioi ε, π α) = 1 - ∫ α in Set.Ioo (0:ℝ) ε, π α := by
    have hunion : Set.Ioi (0:ℝ) = Set.Ioo (0:ℝ) ε ∪ Set.Ici ε := by
      ext x
      constructor
      · intro hx
        rcases lt_or_ge x ε with h | h
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr h
      · rintro (⟨h1, _⟩ | h1)
        · exact h1
        · exact lt_of_lt_of_le hε h1
    have hdisj : Disjoint (Set.Ioo (0:ℝ) ε) (Set.Ici ε) := by
      rw [Set.disjoint_left]
      intro x hx1 hx2
      exact absurd hx1.2 (not_lt.mpr hx2)
    have hπIoo' : IntegrableOn π (Set.Ioo (0:ℝ) ε) :=
      hπ_int.mono_set (fun x hx => hx.1)
    have hπIci' : IntegrableOn π (Set.Ici ε) :=
      hπ_int.mono_set (fun x hx => lt_of_lt_of_le hε hx)
    have hsplit : (∫ α in Set.Ioi (0:ℝ), π α) =
        (∫ α in Set.Ioo (0:ℝ) ε, π α) + ∫ α in Set.Ici ε, π α := by
      rw [hunion,
        MeasureTheory.setIntegral_union hdisj measurableSet_Ici hπIoo' hπIci']
    have hci : (∫ α in Set.Ici ε, π α) = ∫ α in Set.Ioi ε, π α :=
      MeasureTheory.integral_Ici_eq_integral_Ioi
    rw [hci, hπ_mass] at hsplit
    linarith
  have hhalf : (1:ℝ) / 2 ≤ ∫ α in Set.Ioi ε, π α := by
    linarith [hdecomp, hbound, hB1]
  have hmoment : ENNReal.ofReal (ε ^ (t + (s:ℝ) - 1) / 2) ≤ priorMoment π (t + (s:ℝ) - 1) := by
    have hr : (0:ℝ) ≤ t + (s:ℝ) - 1 := by
      have hs1 : (1:ℝ) ≤ (s:ℝ) := by exact_mod_cast hs
      linarith
    have hπIoi : IntegrableOn π (Set.Ioi ε) :=
      hπ_int.mono_set (fun x hx => lt_trans hε hx)
    have hConstInt : IntegrableOn (fun α : ℝ => ε ^ (t + (s:ℝ) - 1) * π α) (Set.Ioi ε) :=
      hπIoi.const_mul (ε ^ (t + (s:ℝ) - 1))
    have hConstNonneg : 0 ≤ᶠ[ae (volume.restrict (Set.Ioi ε))]
        (fun α : ℝ => ε ^ (t + (s:ℝ) - 1) * π α) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with α hα
      exact mul_nonneg (Real.rpow_nonneg (le_of_lt hε) _) (hπ_nonneg α (lt_trans hε hα))
    have htail_eq : (∫⁻ α in Set.Ioi ε, ENNReal.ofReal (ε ^ (t + (s:ℝ) - 1) * π α))
        = ENNReal.ofReal (ε ^ (t + (s:ℝ) - 1) * ∫ α in Set.Ioi ε, π α) := by
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hConstInt hConstNonneg]
      congr 1
      rw [MeasureTheory.integral_const_mul]
    have htail_le : (∫⁻ α in Set.Ioi ε, ENNReal.ofReal (ε ^ (t + (s:ℝ) - 1) * π α))
        ≤ priorMoment π (t + (s:ℝ) - 1) := by
      have h1 : (∫⁻ α in Set.Ioi ε, ENNReal.ofReal (ε ^ (t + (s:ℝ) - 1) * π α))
          ≤ ∫⁻ α in Set.Ioi ε, ENNReal.ofReal (α ^ (t + (s:ℝ) - 1) * π α) := by
        refine MeasureTheory.lintegral_mono_ae ?_
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with α hα
        refine ENNReal.ofReal_le_ofReal ?_
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow (le_of_lt hε) (le_of_lt hα) hr) (hπ_nonneg α (lt_trans hε hα))
      refine h1.trans ?_
      exact MeasureTheory.lintegral_mono_set (fun x hx => lt_trans hε hx)
    calc ENNReal.ofReal (ε ^ (t + (s:ℝ) - 1) / 2)
        = ENNReal.ofReal (ε ^ (t + (s:ℝ) - 1) * (1/2)) := by
          rw [show ε ^ (t + (s:ℝ) - 1) / 2 = ε ^ (t + (s:ℝ) - 1) * (1/2) by ring]
      _ ≤ ENNReal.ofReal (ε ^ (t + (s:ℝ) - 1) * ∫ α in Set.Ioi ε, π α) := by
          refine ENNReal.ofReal_le_ofReal ?_
          exact mul_le_mul_of_nonneg_left hhalf (Real.rpow_nonneg (le_of_lt hε) _)
      _ = ∫⁻ α in Set.Ioi ε, ENNReal.ofReal (ε ^ (t + (s:ℝ) - 1) * π α) := htail_eq.symm
      _ ≤ priorMoment π (t + (s:ℝ) - 1) := htail_le
  have hFint : IntegrableOn (fun α : ℝ => α ^ (t + (s:ℝ) - 1) * π α) (Set.Ioo (0:ℝ) ε) := by
    have hπIoo : IntegrableOn π (Set.Ioo (0:ℝ) ε) :=
      hπ_int.mono_set (fun x hx => hx.1)
    have hGint : IntegrableOn (fun α : ℝ => ε ^ (t + (s:ℝ) - 1) * π α) (Set.Ioo (0:ℝ) ε) :=
      hπIoo.const_mul (ε ^ (t + (s:ℝ) - 1))
    have hcont : ContinuousOn (fun x : ℝ => x ^ (t + (s:ℝ) - 1)) (Set.Ioo (0:ℝ) ε) :=
      (continuous_id.continuousOn : ContinuousOn (fun x : ℝ => x) (Set.Ioo (0:ℝ) ε)).rpow_const
        (fun x hx => Or.inl (ne_of_gt hx.1))
    have hmeas_pow : AEStronglyMeasurable (fun x : ℝ => x ^ (t + (s:ℝ) - 1))
        (volume.restrict (Set.Ioo (0:ℝ) ε)) :=
      hcont.aestronglyMeasurable measurableSet_Ioo
    have hmeasF : AEStronglyMeasurable (fun α : ℝ => α ^ (t + (s:ℝ) - 1) * π α)
        (volume.restrict (Set.Ioo (0:ℝ) ε)) :=
      hmeas_pow.mul hπ_meas.aestronglyMeasurable
    have hnnF : 0 ≤ᶠ[ae (volume.restrict (Set.Ioo (0:ℝ) ε))]
        (fun α : ℝ => α ^ (t + (s:ℝ) - 1) * π α) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with α hα
      exact mul_nonneg (Real.rpow_nonneg (le_of_lt hα.1) _) (hπ_nonneg α hα.1)
    have hnnG : 0 ≤ᶠ[ae (volume.restrict (Set.Ioo (0:ℝ) ε))]
        (fun α : ℝ => ε ^ (t + (s:ℝ) - 1) * π α) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with α hα
      exact mul_nonneg (Real.rpow_nonneg (le_of_lt hε) _) (hπ_nonneg α hα.1)
    have hOfin : (∫⁻ α in Set.Ioo (0:ℝ) ε,
        ENNReal.ofReal (ε ^ (t + (s:ℝ) - 1) * π α)) ≠ ⊤ := by
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hGint hnnG]
      simp
    have hle : (∫⁻ α in Set.Ioo (0:ℝ) ε, ENNReal.ofReal (α ^ (t + (s:ℝ) - 1) * π α))
        ≤ ∫⁻ α in Set.Ioo (0:ℝ) ε, ENNReal.ofReal (ε ^ (t + (s:ℝ) - 1) * π α) := by
      refine MeasureTheory.lintegral_mono_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with α hα
      have hr : (0:ℝ) ≤ t + (s:ℝ) - 1 := by
        have hs1 : (1:ℝ) ≤ (s:ℝ) := by exact_mod_cast hs
        linarith
      refine ENNReal.ofReal_le_ofReal ?_
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (le_of_lt hα.1) (le_of_lt hα.2) hr) (hπ_nonneg α hα.1)
    exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hmeasF hnnF).mp
      (ne_top_of_le_ne_top hOfin hle)
  have hf_bound : (∫ α in Set.Ioo (0:ℝ) ε, α ^ (t + (s:ℝ) - 1) * π α) ≤
      ε ^ (t + (s:ℝ) - 1) * (1/2) := by
    have hr : (0:ℝ) ≤ t + (s:ℝ) - 1 := by
      have hs1 : (1:ℝ) ≤ (s:ℝ) := by exact_mod_cast hs
      linarith
    have hπIoo : IntegrableOn π (Set.Ioo (0:ℝ) ε) :=
      hπ_int.mono_set (fun x hx => hx.1)
    have hGint : IntegrableOn (fun α : ℝ => ε ^ (t + (s:ℝ) - 1) * π α) (Set.Ioo (0:ℝ) ε) :=
      hπIoo.const_mul (ε ^ (t + (s:ℝ) - 1))
    have hmono : (∫ α in Set.Ioo (0:ℝ) ε, α ^ (t + (s:ℝ) - 1) * π α) ≤
        ∫ α in Set.Ioo (0:ℝ) ε, ε ^ (t + (s:ℝ) - 1) * π α :=
      MeasureTheory.setIntegral_mono_on hFint hGint measurableSet_Ioo
        (fun x hx => mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow (le_of_lt hx.1) (le_of_lt hx.2) hr) (hπ_nonneg x hx.1))
    calc (∫ α in Set.Ioo (0:ℝ) ε, α ^ (t + (s:ℝ) - 1) * π α)
        ≤ ∫ α in Set.Ioo (0:ℝ) ε, ε ^ (t + (s:ℝ) - 1) * π α := hmono
      _ = ε ^ (t + (s:ℝ) - 1) * ∫ α in Set.Ioo (0:ℝ) ε, π α := by
          rw [MeasureTheory.integral_const_mul]
      _ ≤ ε ^ (t + (s:ℝ) - 1) * (1/2) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (le_of_lt hε) _)
          linarith [hbound, hB1]
  refine ⟨hpow, ⟨hbound, hB1⟩, ⟨hdecomp, hhalf⟩, ⟨hFint, hf_bound⟩, hmoment, ?_, ?_⟩
  · intro hE
    exact (ENNReal.ofReal_le_iff_le_toReal hE).mp hmoment
  · intro hE
    have hE' : (∫⁻ α in Set.Ioi (0:ℝ), ENNReal.ofReal (α ^ (t + (s:ℝ) - 1) * π α)) ≠ ⊤ := by
      simpa [priorMoment] using hE
    have hcont : ContinuousOn (fun x : ℝ => x ^ (t + (s:ℝ) - 1)) (Set.Ioi (0:ℝ)) :=
      (continuous_id.continuousOn : ContinuousOn (fun x : ℝ => x) (Set.Ioi (0:ℝ))).rpow_const
        (fun x hx => Or.inl (ne_of_gt hx))
    have hmeas_pow : AEStronglyMeasurable (fun x : ℝ => x ^ (t + (s:ℝ) - 1))
        (volume.restrict (Set.Ioi (0:ℝ))) :=
      hcont.aestronglyMeasurable measurableSet_Ioi
    have hmeasF : AEStronglyMeasurable (fun α : ℝ => α ^ (t + (s:ℝ) - 1) * π α)
        (volume.restrict (Set.Ioi (0:ℝ))) :=
      hmeas_pow.mul hπ_meas.aestronglyMeasurable
    have hnnF : 0 ≤ᶠ[ae (volume.restrict (Set.Ioi (0:ℝ)))]
        (fun α : ℝ => α ^ (t + (s:ℝ) - 1) * π α) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with α hα
      exact mul_nonneg (Real.rpow_nonneg (le_of_lt hα) _) (hπ_nonneg α hα)
    have hInt : IntegrableOn (fun α : ℝ => α ^ (t + (s:ℝ) - 1) * π α) (Set.Ioi (0:ℝ)) :=
      (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hmeasF hnnF).mp hE'
    have htoReal : (priorMoment π (t + (s:ℝ) - 1)).toReal
        = ∫ α in Set.Ioi (0:ℝ), α ^ (t + (s:ℝ) - 1) * π α :=
      Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.lintegral_toReal_eq_integral_of_nonneg
        hnnF hInt
    have hle_toReal : ε ^ (t + (s:ℝ) - 1) / 2 ≤ (priorMoment π (t + (s:ℝ) - 1)).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal hE).mp hmoment
    simpa [htoReal] using hle_toReal
  /- @proof-region region.target-node.session.cace72e46d830a27 end -/

end Statlib.Imported
end
