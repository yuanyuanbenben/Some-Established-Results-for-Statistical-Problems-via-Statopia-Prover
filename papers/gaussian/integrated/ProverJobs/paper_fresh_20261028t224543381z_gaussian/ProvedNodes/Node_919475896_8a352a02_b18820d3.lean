import ProverJobs.paper_fresh_20261028t224543381z_gaussian.Vocabulary
import ProverJobs.paper_fresh_20261028t224543381z_gaussian.Base

namespace PaperProofTasks.paper_fresh_20261028t224543381z_gaussian

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open _root_.PaperProofTasks.paper_fresh_20261028t224543381z_gaussian.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace Statlib.Imported
open _root_.Statlib

set_option autoImplicit false in
theorem statopia_math_node_919475896_8a352a02 : ∀ (Omega : Type) [MeasurableSpace Omega] (mu : Measure Omega) [IsProbabilityMeasure mu]
    (xi : Omega → ℝ) (c0 : ℝ)
    (hxi : Measurable xi) (hc0 : 0 < c0)
    (hnorm : Statlib.StatFoundation.Vocabulary.subexponentialOrliczNorm xi mu ≤ ENNReal.ofReal c0),
    ∃ t : ℝ, 0 < t ∧ t ≤ c0 ∧
      Integrable (fun omega : Omega => Real.exp (|xi omega| / t)) mu ∧
      ∫ omega, Real.exp (|xi omega| / t) ∂mu ≤ 2 := by
  /- @proof-region region.target-node.session.cf851123db404a72 begin -/
  intro Omega instOm mu instP xi c0 hxi hc0 hnorm
  have hpsi : ∀ z : ℝ, 0 ≤ z → Statlib.StatFoundation.Vocabulary.psiOrlicz 1 z = Real.exp z - 1 := by
    intro z hz
    simp only [Statlib.StatFoundation.Vocabulary.psiOrlicz, Real.rpow_one]
  set S : Set ℝ≥0∞ := {t : ℝ≥0∞ | 0 < t ∧ ∫⁻ omega, ENNReal.ofReal (Statlib.StatFoundation.Vocabulary.psiOrlicz 1 (|xi omega| / t.toReal)) ∂mu ≤ 1} with hS
  have hnorm' : sInf S ≤ ENNReal.ofReal c0 := by
    simp only [hS, Statlib.StatFoundation.Vocabulary.subexponentialOrliczNorm, Statlib.StatFoundation.Vocabulary.orliczNorm] at hnorm ⊢
    exact hnorm
  have hSbd : BddBelow S := ⟨0, fun t _ => zero_le t⟩
  have hStop : (⊤ : ℝ≥0∞) ∈ S := by
    have htop : (⊤ : ℝ≥0∞).toReal = 0 := by simp
    have hpt0 : ∀ omega : Omega, ENNReal.ofReal (Statlib.StatFoundation.Vocabulary.psiOrlicz 1 (|xi omega| / (⊤ : ℝ≥0∞).toReal)) = 0 := by
      intro omega
      rw [htop, div_zero, hpsi 0 le_rfl]
      simp
    refine ⟨by simp, ?_⟩
    rw [MeasureTheory.lintegral_congr hpt0]
    simp
  have hupper : ∀ t t' : ℝ≥0∞, t ∈ S → t ≤ t' → 0 < t' → t' ∈ S := by
    intro t t' ht htle ht'pos
    refine ⟨ht'pos, ?_⟩
    refine le_trans (MeasureTheory.lintegral_mono ?_) ht.2
    intro omega
    apply ENNReal.ofReal_le_ofReal
    have harg : |xi omega| / t'.toReal ≤ |xi omega| / t.toReal := by
      rcases eq_or_ne t' ⊤ with h | h
      · rw [h]
        have h0 : (⊤ : ℝ≥0∞).toReal = 0 := by simp
        rw [h0, div_zero]
        exact div_nonneg (abs_nonneg _) ENNReal.toReal_nonneg
      · have htne : t ≠ ⊤ := by
          intro htT
          exact h (top_le_iff.mp (htT ▸ htle))
        have htpos : 0 < t.toReal := ENNReal.toReal_pos ht.1.ne' htne
        have hle : t.toReal ≤ t'.toReal := (ENNReal.toReal_le_toReal htne h).mpr htle
        exact div_le_div_of_nonneg_left (abs_nonneg _) htpos hle
    rw [hpsi (|xi omega| / t'.toReal) (div_nonneg (abs_nonneg _) ENNReal.toReal_nonneg),
      hpsi (|xi omega| / t.toReal) (div_nonneg (abs_nonneg _) ENNReal.toReal_nonneg)]
    linarith [Real.exp_le_exp.mpr harg]
  have hmem : ENNReal.ofReal c0 ∈ S := by
    have han : ENNReal.ofReal c0 ≠ ⊤ := ENNReal.ofReal_ne_top
    have hapos : 0 < ENNReal.ofReal c0 := ENNReal.ofReal_pos.mpr hc0
    rcases lt_or_ge (sInf S) (ENNReal.ofReal c0) with hlt | hge
    · obtain ⟨t, htS, hta⟩ := (csInf_lt_iff hSbd ⟨⊤, hStop⟩).mp hlt
      exact hupper t _ htS (le_of_lt hta) hapos
    · have hsInf : sInf S = ENNReal.ofReal c0 := le_antisymm hnorm' hge
      have hb : ∀ k : ℕ, (ENNReal.ofReal c0 + ENNReal.ofReal (((k : ℝ) + 1)⁻¹)).toReal = c0 + ((k : ℝ) + 1)⁻¹ := by
        intro k
        have hk : (0 : ℝ) < ((k : ℝ) + 1)⁻¹ := by positivity
        rw [ENNReal.toReal_add han ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (le_of_lt hc0),
          ENNReal.toReal_ofReal (le_of_lt hk)]
      have hmemk : ∀ k : ℕ, (ENNReal.ofReal c0 + ENNReal.ofReal (((k : ℝ) + 1)⁻¹)) ∈ S := by
        intro k
        have hk : (0 : ℝ) < ((k : ℝ) + 1)⁻¹ := by positivity
        have hne : ENNReal.ofReal (((k : ℝ) + 1)⁻¹) ≠ 0 := (ENNReal.ofReal_pos.mpr hk).ne'
        have hlt : sInf S < ENNReal.ofReal c0 + ENNReal.ofReal (((k : ℝ) + 1)⁻¹) := by
          rw [hsInf]
          exact ENNReal.lt_add_right han hne
        obtain ⟨t, htS, htlt⟩ := (csInf_lt_iff hSbd ⟨⊤, hStop⟩).mp hlt
        exact hupper t _ htS (le_of_lt htlt) (lt_of_lt_of_le hapos (hge.trans (le_of_lt hlt)))
      set F : ℕ → Omega → ℝ≥0∞ := fun k omega =>
        ENNReal.ofReal (Real.exp (|xi omega| / (c0 + ((k : ℝ) + 1)⁻¹)) - 1) with hF
      have hmonoF : ∀ omega : Omega, Monotone fun k : ℕ => F k omega := by
        intro omega m n hmn
        show ENNReal.ofReal (Real.exp (|xi omega| / (c0 + ((m : ℝ) + 1)⁻¹)) - 1)
          ≤ ENNReal.ofReal (Real.exp (|xi omega| / (c0 + ((n : ℝ) + 1)⁻¹)) - 1)
        have hmn' : ((m : ℝ) + 1) ≤ ((n : ℝ) + 1) := by
          have hcast : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
          linarith
        have hden : c0 + ((n : ℝ) + 1)⁻¹ ≤ c0 + ((m : ℝ) + 1)⁻¹ := by
          have h2 := one_div_le_one_div_of_le (a := (m : ℝ) + 1) (b := (n : ℝ) + 1) (by positivity) hmn'
          simpa using h2
        have hposn : (0 : ℝ) < c0 + ((n : ℝ) + 1)⁻¹ := by
          have hnn : (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹ := by positivity
          linarith
        have harg : |xi omega| / (c0 + ((m : ℝ) + 1)⁻¹) ≤ |xi omega| / (c0 + ((n : ℝ) + 1)⁻¹) :=
          div_le_div_of_nonneg_left (abs_nonneg _) hposn hden
        have hexp := Real.exp_le_exp.mpr harg
        exact ENNReal.ofReal_le_ofReal (by linarith)
      have hmeasF : ∀ k : ℕ, Measurable (F k) := by
        intro k
        show Measurable (fun omega : Omega => ENNReal.ofReal (Real.exp (|xi omega| / (c0 + ((k : ℝ) + 1)⁻¹)) - 1))
        exact Measurable.ennreal_ofReal ((Real.measurable_exp.comp (hxi.abs.div_const _)).sub_const 1)
      have hFle : ∀ k : ℕ, ∫⁻ omega : Omega, F k omega ∂mu ≤ 1 := by
        intro k
        have h := (hmemk k).2
        rw [hb k] at h
        show ∫⁻ omega : Omega, ENNReal.ofReal (Real.exp (|xi omega| / (c0 + ((k : ℝ) + 1)⁻¹)) - 1) ∂mu ≤ 1
        have hstep : ∫⁻ omega : Omega, ENNReal.ofReal (Statlib.StatFoundation.Vocabulary.psiOrlicz 1 (|xi omega| / (c0 + ((k : ℝ) + 1)⁻¹))) ∂mu
            = ∫⁻ omega : Omega, ENNReal.ofReal (Real.exp (|xi omega| / (c0 + ((k : ℝ) + 1)⁻¹)) - 1) ∂mu := by
          apply MeasureTheory.lintegral_congr
          intro omega
          rw [hpsi _ (div_nonneg (abs_nonneg _) (by positivity))]
        rw [hstep] at h
        exact h
      have hconv : ∀ omega : Omega, Filter.Tendsto (fun k : ℕ => F k omega) Filter.atTop
          (nhds (ENNReal.ofReal (Real.exp (|xi omega| / c0) - 1))) := by
        intro omega
        show Filter.Tendsto (fun k : ℕ => ENNReal.ofReal (Real.exp (|xi omega| / (c0 + ((k : ℝ) + 1)⁻¹)) - 1))
          Filter.atTop (nhds (ENNReal.ofReal (Real.exp (|xi omega| / c0) - 1)))
        have hreal : Filter.Tendsto (fun k : ℕ => Real.exp (|xi omega| / (c0 + ((k : ℝ) + 1)⁻¹)) - 1) Filter.atTop
            (nhds (Real.exp (|xi omega| / c0) - 1)) := by
          have hinv : Filter.Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) Filter.atTop (nhds 0) := by
            have h1 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
            simpa [one_div] using h1
          have hu : Filter.Tendsto (fun k : ℕ => c0 + ((k : ℝ) + 1)⁻¹) Filter.atTop (nhds c0) := by
            simpa using tendsto_const_nhds.add hinv
          have hdiv : Filter.Tendsto (fun k : ℕ => |xi omega| / (c0 + ((k : ℝ) + 1)⁻¹)) Filter.atTop
              (nhds (|xi omega| / c0)) :=
            Filter.Tendsto.div tendsto_const_nhds hu (ne_of_gt hc0)
          have hexp : Filter.Tendsto (fun k : ℕ => Real.exp (|xi omega| / (c0 + ((k : ℝ) + 1)⁻¹))) Filter.atTop
              (nhds (Real.exp (|xi omega| / c0))) :=
            (Real.continuous_exp.tendsto (|xi omega| / c0)).comp hdiv
          exact hexp.sub tendsto_const_nhds
        exact (ENNReal.continuous_ofReal.tendsto (Real.exp (|xi omega| / c0) - 1)).comp hreal
      have hcont := MeasureTheory.lintegral_tendsto_of_tendsto_of_monotone
        (μ := mu) (f := F) (F := fun omega : Omega => ENNReal.ofReal (Real.exp (|xi omega| / c0) - 1))
        (fun k => (hmeasF k).aemeasurable) (Filter.Eventually.of_forall hmonoF) (Filter.Eventually.of_forall hconv)
      have hgoal : ∫⁻ omega : Omega, ENNReal.ofReal (Real.exp (|xi omega| / c0) - 1) ∂mu ≤ 1 :=
        le_of_tendsto hcont (Filter.Eventually.of_forall hFle)
      refine ⟨hapos, ?_⟩
      show ∫⁻ omega : Omega, ENNReal.ofReal (Statlib.StatFoundation.Vocabulary.psiOrlicz 1 (|xi omega| / (ENNReal.ofReal c0).toReal)) ∂mu ≤ 1
      have hstep2 : ∫⁻ omega : Omega, ENNReal.ofReal (Statlib.StatFoundation.Vocabulary.psiOrlicz 1 (|xi omega| / (ENNReal.ofReal c0).toReal)) ∂mu
          = ∫⁻ omega : Omega, ENNReal.ofReal (Real.exp (|xi omega| / c0) - 1) ∂mu := by
        apply MeasureTheory.lintegral_congr
        intro omega
        rw [ENNReal.toReal_ofReal (le_of_lt hc0), hpsi _ (div_nonneg (abs_nonneg _) (le_of_lt hc0))]
      rw [hstep2]
      exact hgoal
  have hconvt : ∫⁻ omega : Omega, ENNReal.ofReal (Statlib.StatFoundation.Vocabulary.psiOrlicz 1 (|xi omega| / (ENNReal.ofReal c0).toReal)) ∂mu
      = ∫⁻ omega : Omega, ENNReal.ofReal (Real.exp (|xi omega| / c0) - 1) ∂mu := by
    apply MeasureTheory.lintegral_congr
    intro omega
    rw [ENNReal.toReal_ofReal (le_of_lt hc0), hpsi _ (div_nonneg (abs_nonneg _) (le_of_lt hc0))]
  have hH : ∫⁻ omega : Omega, ENNReal.ofReal (Real.exp (|xi omega| / c0) - 1) ∂mu ≤ 1 := by
    have h2 := hmem.2
    rw [hconvt] at h2
    exact h2
  have hpt : ∀ omega : Omega, ENNReal.ofReal (Real.exp (|xi omega| / c0)) = ENNReal.ofReal (Real.exp (|xi omega| / c0) - 1) + 1 := by
    intro omega
    have h1 : 0 ≤ Real.exp (|xi omega| / c0) - 1 := by
      have hge1 : 1 ≤ Real.exp (|xi omega| / c0) :=
        Real.one_le_exp (x := |xi omega| / c0) (div_nonneg (abs_nonneg _) (le_of_lt hc0))
      linarith
    have hone : ENNReal.ofReal (1 : ℝ) = 1 := by simp
    rw [← hone, ← ENNReal.ofReal_add h1 zero_le_one, sub_add_cancel]
  have hmeas : Measurable (fun omega : Omega => ENNReal.ofReal (Real.exp (|xi omega| / c0) - 1)) := by
    exact Measurable.ennreal_ofReal ((Real.measurable_exp.comp (hxi.abs.div_const c0)).sub_const 1)
  have hmain : ∫⁻ omega : Omega, ENNReal.ofReal (Real.exp (|xi omega| / c0)) ∂mu ≤ 2 := by
    have hsplit : ∫⁻ omega : Omega, ENNReal.ofReal (Real.exp (|xi omega| / c0)) ∂mu
        = ∫⁻ omega : Omega, (ENNReal.ofReal (Real.exp (|xi omega| / c0) - 1) + 1) ∂mu := by
      apply MeasureTheory.lintegral_congr
      intro omega
      exact hpt omega
    rw [hsplit, MeasureTheory.lintegral_add_left hmeas (fun _ => (1 : ℝ≥0∞))]
    have hconst : ∫⁻ omega : Omega, (1 : ℝ≥0∞) ∂mu = 1 := by
      rw [MeasureTheory.lintegral_const, measure_univ, mul_one]
    rw [hconst]
    calc ∫⁻ omega : Omega, ENNReal.ofReal (Real.exp (|xi omega| / c0) - 1) ∂mu + 1 ≤ 1 + 1 := add_le_add hH le_rfl
      _ = 2 := by norm_num
  have hne_top : ∫⁻ omega : Omega, ENNReal.ofReal (Real.exp (|xi omega| / c0)) ∂mu ≠ ⊤ := by
    intro hh
    rw [hh] at hmain
    exact absurd hmain (by simp)
  have hnn : 0 ≤ᶠ[ae mu] (fun omega : Omega => Real.exp (|xi omega| / c0)) :=
    Filter.Eventually.of_forall (fun omega => (Real.exp_pos _).le)
  have hint : Integrable (fun omega : Omega => Real.exp (|xi omega| / c0)) mu := by
    have hae : AEStronglyMeasurable (fun omega : Omega => Real.exp (|xi omega| / c0)) mu :=
      (Real.measurable_exp.comp (hxi.abs.div_const c0)).aestronglyMeasurable
    exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hae hnn).mp hne_top
  have hfin : ∫ omega : Omega, Real.exp (|xi omega| / c0) ∂mu ≤ 2 := by
    have hI := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn
    have htwo : (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) := by norm_num
    have hle : ENNReal.ofReal (∫ omega : Omega, Real.exp (|xi omega| / c0) ∂mu) ≤ ENNReal.ofReal (2 : ℝ) := by
      rw [hI, ← htwo]
      exact hmain
    exact (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 2)).mp hle
  exact ⟨c0, hc0, le_rfl, hint, hfin⟩
  /- @proof-region region.target-node.session.cf851123db404a72 end -/

end Statlib.Imported
end

