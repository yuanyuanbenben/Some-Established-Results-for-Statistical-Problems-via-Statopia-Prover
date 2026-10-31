import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.Vocabulary
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.Base
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.ProvedNodes.Node_1445702134_3c8d3810_8f7a15fe

open MeasureTheory
open Statlib.Imported

noncomputable section
open MeasureTheory
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_3788355289_2a3e6b7e : ∀ (t : ℝ) (ht : 1 ≤ t)
    (π : ℝ → ℝ) (hπ_meas : Measurable π)
    (hπ_nonneg : ∀ α ∈ Set.Ioi (0 : ℝ), 0 ≤ π α)
    (hπ_prob : ∫⁻ α in Set.Ioi (0 : ℝ), ENNReal.ofReal (π α) = 1)
    (ε δ β : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hβ : 0 < β)
    (hA2 : ∀ α ∈ Set.Ioo (0 : ℝ) ε, δ⁻¹ * α ^ β ≤ π α ∧ π α ≤ δ * α ^ β)
    (n s : ℕ) (hs : 1 ≤ s) (hns : (s : ℝ) + t ≤ (n : ℝ)),
    IntegrableOn (fun α : ℝ => α ^ (t + (s : ℝ)) / risingFac α n * π α) (Set.Ioo (0 : ℝ) ε) ∧
    0 < ∫ α in Set.Ioo (0 : ℝ) ε, α ^ (t + (s : ℝ)) / risingFac α n * π α ∧
    IntegrableOn (fun α : ℝ => α ^ t / risingFac α n * π α) (Set.Ioo (0 : ℝ) ε) ∧
    0 < ∫ α in Set.Ioo (0 : ℝ) ε, α ^ t / risingFac α n * π α ∧
    IntegrableOn (fun α : ℝ => α ^ (t + (s : ℝ)) / risingFac α n * π α) (Set.Ioi ε) ∧
    0 ≤ ∫ α in Set.Ioi ε, α ^ (t + (s : ℝ)) / risingFac α n * π α ∧
    IntegrableOn (fun α : ℝ => α ^ t / risingFac α n * π α) (Set.Ioi ε) ∧
    0 ≤ ∫ α in Set.Ioi ε, α ^ t / risingFac α n * π α ∧
    (0 < ((∫ α in Set.Ioo (0 : ℝ) ε, α ^ (t + (s : ℝ)) / risingFac α n * π α) +
            (∫ α in Set.Ioi ε, α ^ (t + (s : ℝ)) / risingFac α n * π α)) /
          ((∫ α in Set.Ioo (0 : ℝ) ε, α ^ t / risingFac α n * π α) +
            (∫ α in Set.Ioi ε, α ^ t / risingFac α n * π α))) := by
  /- @proof-region region.target-node.session.f28d30e0867a6dbc begin -/
  intro t ht π hπ_meas hπ_nonneg hπ_prob ε δ β hε hδ hβ hA2 n s hs hns
  obtain ⟨haf0, hbf0, hcf, _hdf, _hef⟩ := statopia_math_node_1445702134_3c8d3810
  have haf : ∀ (a : ℝ), 0 < a → ∀ (n : ℕ), 0 < risingFac a n := fun a ha n => haf0 a n ha
  have hbf : ∀ (a : ℝ), 0 < a → ∀ (n : ℕ), a ^ n ≤ risingFac a n := fun a ha n => hbf0 a n ha
  have hsR : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have h2n : (2 : ℝ) ≤ (n : ℝ) := by linarith [hns, ht, hsR]
  have hn2 : 2 ≤ n := by exact_mod_cast h2n
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn2
  have hπ_ae_nonneg : 0 ≤ᶠ[ae (volume.restrict (Set.Ioi (0 : ℝ)))] π := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with a ha
    exact hπ_nonneg a ha
  have hπ_ae_meas : AEStronglyMeasurable π (volume.restrict (Set.Ioi (0 : ℝ))) :=
    hπ_meas.aestronglyMeasurable
  have hπ_int : IntegrableOn π (Set.Ioi (0 : ℝ)) := by
    refine ⟨hπ_ae_meas, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_ofReal hπ_ae_nonneg, hπ_prob]
    simp
  have gbound : ∀ (p : ℝ), 1 ≤ p → p ≤ (n : ℝ) →
      ∀ a ∈ Set.Ioi (0 : ℝ), a ^ p / risingFac a n ≤ 1 := by
    intro p hp1 hpn a ha
    have hα0 : 0 < a := ha
    have hrise_pos : 0 < risingFac a n := haf a hα0 n
    have key : a ^ p ≤ risingFac a n → a ^ p / risingFac a n ≤ 1 := by
      intro hle_pow
      have h := (div_le_div_iff_of_pos_right (a := a ^ p) (b := risingFac a n)
        (c := risingFac a n) hrise_pos).mpr hle_pow
      rwa [div_self (ne_of_gt hrise_pos)] at h
    apply key
    by_cases hle : a ≤ 1
    · have hfac1 : (1 : ℝ) ≤ ((n - 1).factorial : ℝ) := by
        have h1 : (1 : ℕ) ≤ (n - 1).factorial := by
          have hpos := Nat.factorial_pos (n - 1); omega
        exact_mod_cast h1
      have hrise_ge : a * ((n - 1).factorial : ℝ) ≤ risingFac a n := hcf a n hα0 hle hn1
      have hpge0 : (0 : ℝ) ≤ p - 1 := by linarith
      have hpow_le : a ^ (p - 1) ≤ 1 := by
        have h := Real.rpow_le_rpow_of_exponent_ge (x := a) (y := p - 1) (z := 0) hα0 hle hpge0
        rwa [Real.rpow_zero] at h
      have ha_p : a ^ p = a ^ (p - 1) * a := by
        have h := Real.rpow_add_natCast (ne_of_gt hα0) (p - 1) 1
        rw [show (p - 1) + ((1 : ℕ) : ℝ) = p by push_cast; ring, pow_one] at h
        exact h
      have step1 : a ^ p ≤ a := by
        rw [ha_p]
        calc a ^ (p - 1) * a ≤ 1 * a := mul_le_mul_of_nonneg_right hpow_le (le_of_lt hα0)
          _ = a := one_mul a
      have step2 : a ≤ a * ((n - 1).factorial : ℝ) := by
        calc a = a * 1 := (mul_one a).symm
          _ ≤ a * ((n - 1).factorial : ℝ) := mul_le_mul_of_nonneg_left hfac1 (le_of_lt hα0)
      exact le_trans step1 (le_trans step2 hrise_ge)
    · have hgt : 1 < a := not_le.mp hle
      have hrise_ge : a ^ n ≤ risingFac a n := hbf a hα0 n
      have hpn' : p - (n : ℝ) ≤ 0 := by linarith
      have hpn_le : a ^ (p - (n : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (x := a) (z := p - (n : ℝ)) (le_of_lt hgt) hpn'
      have ha_p : a ^ p = a ^ (p - (n : ℝ)) * a ^ n := by
        have h := Real.rpow_add_natCast (ne_of_gt hα0) (p - (n : ℝ)) n
        rw [show (p - (n : ℝ)) + (n : ℝ) = p by ring] at h
        exact h
      have step1 : a ^ p ≤ a ^ n := by
        rw [ha_p]
        calc a ^ (p - (n : ℝ)) * a ^ n ≤ 1 * a ^ n :=
              mul_le_mul_of_nonneg_right hpn_le (pow_nonneg (le_of_lt hα0) n)
          _ = a ^ n := one_mul _
      exact le_trans step1 hrise_ge
  have hintg : ∀ (p : ℝ), 1 ≤ p → p ≤ (n : ℝ) →
      IntegrableOn (fun a : ℝ => a ^ p / risingFac a n * π a) (Set.Ioi (0 : ℝ)) := by
    intro p hp1 hpn
    have hboundp : ∀ a ∈ Set.Ioi (0 : ℝ), a ^ p / risingFac a n * π a ≤ π a := by
      intro a ha
      have hg1 : a ^ p / risingFac a n ≤ 1 := gbound p hp1 hpn a ha
      calc a ^ p / risingFac a n * π a ≤ 1 * π a := mul_le_mul_of_nonneg_right hg1 (hπ_nonneg a ha)
        _ = π a := one_mul _
    have hfin : HasFiniteIntegral (fun a : ℝ => a ^ p / risingFac a n * π a)
        (volume.restrict (Set.Ioi (0 : ℝ))) := by
      apply MeasureTheory.HasFiniteIntegral.mono' hπ_int.2
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with a ha
      have hnonneg : 0 ≤ a ^ p / risingFac a n * π a :=
        mul_nonneg (le_of_lt (div_pos (Real.rpow_pos_of_pos ha p) (haf a ha n))) (hπ_nonneg a ha)
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      exact hboundp a ha
    have hmeas : AEStronglyMeasurable (fun a : ℝ => a ^ p / risingFac a n * π a)
        (volume.restrict (Set.Ioi (0 : ℝ))) := by
      have hp_cont : ContinuousOn (fun a : ℝ => a ^ p) (Set.Ioi (0 : ℝ)) := by
        have h := ContinuousOn.rpow_const (f := id) (s := Set.Ioi (0 : ℝ)) (p := p)
          continuous_id.continuousOn (fun x hx => Or.inl (ne_of_gt hx))
        simpa using h
      have hr_cont : Continuous (fun a : ℝ => risingFac a n) := by
        unfold risingFac
        continuity
      have hquot : AEStronglyMeasurable (fun a : ℝ => a ^ p / risingFac a n)
          (volume.restrict (Set.Ioi (0 : ℝ))) := by
        have hc : ContinuousOn (fun a : ℝ => a ^ p * (risingFac a n)⁻¹) (Set.Ioi (0 : ℝ)) :=
          hp_cont.mul (hr_cont.continuousOn.inv₀ (fun x hx => ne_of_gt (haf x hx n)))
        exact hc.aestronglyMeasurable measurableSet_Ioi
      exact hquot.mul hπ_meas.aestronglyMeasurable
    exact ⟨hmeas, hfin⟩
  have hf_nonneg : ∀ (p : ℝ), ∀ a ∈ Set.Ioi (0 : ℝ), 0 ≤ a ^ p / risingFac a n * π a := by
    intro p a ha
    exact mul_nonneg (le_of_lt (div_pos (Real.rpow_pos_of_pos ha p) (haf a ha n))) (hπ_nonneg a ha)
  have hfin_lint : ∀ (p : ℝ), 1 ≤ p → p ≤ (n : ℝ) → ∀ (s0 : Set ℝ), MeasurableSet s0 →
      s0 ⊆ Set.Ioi (0 : ℝ) →
      (∫⁻ a in s0, ENNReal.ofReal (a ^ p / risingFac a n * π a)) < ⊤ := by
    intro p hp1 hpn s0 hs0meas hs0sub
    have hint : IntegrableOn (fun a : ℝ => a ^ p / risingFac a n * π a) s0 :=
      (hintg p hp1 hpn).mono_set hs0sub
    have hnn : 0 ≤ᶠ[ae (volume.restrict s0)] (fun a : ℝ => a ^ p / risingFac a n * π a) := by
      filter_upwards [MeasureTheory.ae_restrict_mem hs0meas] with a ha
      exact hf_nonneg p a (hs0sub ha)
    exact (MeasureTheory.hasFiniteIntegral_iff_ofReal hnn).mp hint.2
  have hpos_int : ∀ (p : ℝ), 1 ≤ p → p ≤ (n : ℝ) →
      0 < ∫ a in Set.Ioo (0 : ℝ) ε, a ^ p / risingFac a n * π a := by
    intro p hp1 hpn
    have hint : IntegrableOn (fun a : ℝ => a ^ p / risingFac a n * π a) (Set.Ioo (0 : ℝ) ε) :=
      (hintg p hp1 hpn).mono_set (fun a ha => ha.1)
    have hnn : 0 ≤ᶠ[ae (volume.restrict (Set.Ioo (0 : ℝ) ε))]
        (fun a : ℝ => a ^ p / risingFac a n * π a) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with a ha
      exact hf_nonneg p a ha.1
    rw [MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae hnn hint]
    have hsub : Set.Ioo (0 : ℝ) ε ⊆
        Function.support (fun a : ℝ => a ^ p / risingFac a n * π a) := by
      intro a ha
      simp only [Function.mem_support]
      have hπpos : 0 < π a := by
        have hlower : 0 < δ⁻¹ * a ^ β := mul_pos (inv_pos.mpr hδ) (Real.rpow_pos_of_pos ha.1 β)
        exact lt_of_lt_of_le hlower (hA2 a ha).1
      have hgpos : 0 < a ^ p / risingFac a n :=
        div_pos (Real.rpow_pos_of_pos ha.1 p) (haf a ha.1 n)
      exact ne_of_gt (mul_pos hgpos hπpos)
    have hvol : volume (Function.support (fun a : ℝ => a ^ p / risingFac a n * π a) ∩
        Set.Ioo (0 : ℝ) ε) = volume (Set.Ioo (0 : ℝ) ε) := by
      apply le_antisymm
      · exact measure_mono Set.inter_subset_right
      · exact measure_mono (fun a ha => ⟨hsub ha, ha⟩)
    rw [hvol, Real.volume_Ioo, sub_zero]
    exact ENNReal.ofReal_pos.mpr hε
  have htail_nonneg : ∀ (p : ℝ), 1 ≤ p → p ≤ (n : ℝ) →
      0 ≤ ∫ a in Set.Ioi ε, a ^ p / risingFac a n * π a := by
    intro p hp1 hpn
    apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
    intro a ha
    exact hf_nonneg p a (lt_trans hε ha)
  have hns' : t + (s : ℝ) ≤ (n : ℝ) := by linarith [hns]
  have hpt1 : (1 : ℝ) ≤ t + (s : ℝ) := by linarith [ht, hsR]
  have htn : t ≤ (n : ℝ) := by linarith [hns, hsR]
  have hAs : 0 < ∫ a in Set.Ioo (0 : ℝ) ε, a ^ (t + (s : ℝ)) / risingFac a n * π a :=
    hpos_int (t + (s : ℝ)) hpt1 hns'
  have hB : 0 < ∫ a in Set.Ioo (0 : ℝ) ε, a ^ t / risingFac a n * π a := hpos_int t ht htn
  have hAs_tail : 0 ≤ ∫ a in Set.Ioi ε, a ^ (t + (s : ℝ)) / risingFac a n * π a :=
    htail_nonneg (t + (s : ℝ)) hpt1 hns'
  have hB_tail : 0 ≤ ∫ a in Set.Ioi ε, a ^ t / risingFac a n * π a := htail_nonneg t ht htn
  refine ⟨?_, hAs, ?_, hB, ?_, hAs_tail, ?_, hB_tail, ?_⟩
  · exact (hintg (t + (s : ℝ)) hpt1 hns').mono_set (fun a ha => ha.1)
  · exact (hintg t ht htn).mono_set (fun a ha => ha.1)
  · exact (hintg (t + (s : ℝ)) hpt1 hns').mono_set (fun a ha => lt_trans hε ha)
  · exact (hintg t ht htn).mono_set (fun a ha => lt_trans hε ha)
  · exact div_pos (lt_of_lt_of_le hAs (le_add_of_nonneg_right hAs_tail))
      (lt_of_lt_of_le hB (le_add_of_nonneg_right hB_tail))
  /- @proof-region region.target-node.session.f28d30e0867a6dbc end -/

end Statlib.Imported
end
