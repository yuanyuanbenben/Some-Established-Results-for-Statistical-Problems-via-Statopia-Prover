import ProverJobs.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Vocabulary
import ProverJobs.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Base

namespace PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed

open _root_.PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Statlib.Imported
open _root_.Statlib
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
universe u₀ u₁

set_option autoImplicit false in
theorem statopia_math_node_128714905_89e34666 : ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : Ω → ℝ) (hξ : Measurable ξ) (c0 : ℝ) (hc0 : 0 < c0)
    (h : Statlib.StatFoundation.Vocabulary.orliczNorm 1 ξ P ≤ ENNReal.ofReal c0),
    ∫⁻ ω, ENNReal.ofReal (Real.exp (|ξ ω| / c0)) ∂P ≤ (2 : ENNReal) := by
  /- @proof-region region.target-node.session.9904c10a99c8fa71 begin -/
  intro Ω _ P _ ξ hξ c0 hc0 h
  unfold Statlib.StatFoundation.Vocabulary.orliczNorm at h
  set S : Set ℝ≥0∞ :=
    {t | 0 < t ∧
      ∫⁻ ω, ENNReal.ofReal (Statlib.StatFoundation.Vocabulary.psiOrlicz 1 (|ξ ω| / t.toReal)) ∂P ≤ 1}
    with hSdef
  have hh : sInf S ≤ ENNReal.ofReal c0 := by
    rw [hSdef]
    exact h
  have hdivmono : ∀ (y e d : ℝ), 0 ≤ y → 0 < e → e ≤ d → y / d ≤ y / e := by
    intro y e d hy he hed
    have hinv : d⁻¹ ≤ e⁻¹ := by
      simpa using one_div_le_one_div_of_le he hed
    calc y / d = y * d⁻¹ := div_eq_mul_inv y d
      _ ≤ y * e⁻¹ := mul_le_mul_of_nonneg_left hinv hy
      _ = y / e := (div_eq_mul_inv y e).symm
  have hpsi_mono : ∀ a b : ℝ, a ≤ b →
      Statlib.StatFoundation.Vocabulary.psiOrlicz 1 a ≤
        Statlib.StatFoundation.Vocabulary.psiOrlicz 1 b := by
    intro a b hab
    show Real.exp (a ^ 1) - 1 ≤ Real.exp (b ^ 1) - 1
    exact sub_le_sub_right (Real.exp_le_exp.mpr (by simpa [pow_one] using hab)) 1
  have hexp_of_psi : ∀ y : ℝ, 0 ≤ y →
      ENNReal.ofReal (Real.exp y)
        = ENNReal.ofReal (Statlib.StatFoundation.Vocabulary.psiOrlicz 1 y) + 1 := by
    intro y hy
    have h1 : (0:ℝ) ≤ Real.exp y - 1 := by
      have h2 : Real.exp 0 ≤ Real.exp y := Real.exp_le_exp.mpr hy
      rw [Real.exp_zero] at h2
      linarith
    have hpsi : Statlib.StatFoundation.Vocabulary.psiOrlicz 1 y = Real.exp y - 1 := by
      simp [Statlib.StatFoundation.Vocabulary.psiOrlicz]
    rw [show Real.exp y = (Real.exp y - 1) + 1 from by ring]
    rw [ENNReal.ofReal_add h1 zero_le_one, ENNReal.ofReal_one]
    rw [hpsi]
  have hup : ∀ {s t : ℝ≥0∞}, s ∈ S → s ≤ t → t ∈ S := by
    intro s t hs hst
    obtain ⟨hs0, hsint⟩ := hs
    refine ⟨lt_of_lt_of_le hs0 hst, ?_⟩
    by_cases htt : t = ⊤
    · rw [htt]
      have hz : ∀ ω : Ω, ENNReal.ofReal
          (Statlib.StatFoundation.Vocabulary.psiOrlicz 1 (|ξ ω| / (⊤ : ℝ≥0∞).toReal)) = 0 := by
        intro ω
        simp [Statlib.StatFoundation.Vocabulary.psiOrlicz]
      simp only [hz]
      simp
    · have hstop : s ≠ ⊤ := by
        intro htop
        exact htt (le_antisymm le_top (htop ▸ hst))
      have hspos : 0 < s.toReal := ENNReal.toReal_pos hs0.ne' hstop
      have htole : s.toReal ≤ t.toReal := ENNReal.toReal_mono htt hst
      refine le_trans (lintegral_mono ?_) hsint
      intro ω
      exact ENNReal.ofReal_le_ofReal
        (hpsi_mono _ _ (hdivmono |ξ ω| s.toReal t.toReal (abs_nonneg _) hspos htole))
  have hmem : ∀ t : ℝ≥0∞, ENNReal.ofReal c0 < t → t ∈ S := by
    intro t ht
    by_contra hnot
    have hlower : t ≤ sInf S :=
      le_sInf fun s hs => by
        by_contra hcon
        exact hnot (hup hs (le_of_lt (not_le.mp hcon)))
    exact absurd (le_trans hlower hh) (not_le.mpr ht)
  have hbound : ∀ n : ℕ, ∫⁻ ω, ENNReal.ofReal
      (Real.exp (|ξ ω| / (c0 + 1 / ((n:ℝ) + 1)))) ∂P ≤ 2 := by
    intro n
    have hpos : 0 < c0 + 1 / ((n:ℝ) + 1) := by positivity
    have hlt : ENNReal.ofReal c0 < ENNReal.ofReal (c0 + 1 / ((n:ℝ) + 1)) := by
      rw [ENNReal.ofReal_lt_ofReal_iff hpos]
      have h1 : 0 < 1 / ((n:ℝ) + 1) := by positivity
      linarith
    have hmem_n : ENNReal.ofReal (c0 + 1 / ((n:ℝ) + 1)) ∈ S := hmem _ hlt
    have hreal : (ENNReal.ofReal (c0 + 1 / ((n:ℝ) + 1))).toReal = c0 + 1 / ((n:ℝ) + 1) :=
      ENNReal.toReal_ofReal (le_of_lt hpos)
    have h2 : ∫⁻ ω, ENNReal.ofReal (Statlib.StatFoundation.Vocabulary.psiOrlicz 1
        (|ξ ω| / (c0 + 1 / ((n:ℝ) + 1)))) ∂P ≤ 1 := by
      have h3 := hmem_n.2
      rwa [hreal] at h3
    have hpw : ∀ ω : Ω, ENNReal.ofReal (Real.exp (|ξ ω| / (c0 + 1 / ((n:ℝ) + 1))))
        = ENNReal.ofReal (Statlib.StatFoundation.Vocabulary.psiOrlicz 1
            (|ξ ω| / (c0 + 1 / ((n:ℝ) + 1)))) + 1 :=
      fun ω => hexp_of_psi _ (div_nonneg (abs_nonneg _) (le_of_lt hpos))
    simp only [hpw]
    rw [lintegral_add_right _ measurable_const, lintegral_one, measure_univ]
    have htwo : (2:ℝ≥0∞) = 1 + 1 := by norm_num
    rw [htwo]
    exact le_trans (le_of_eq (add_comm _ _)) (add_le_add_right h2 1)
  have hden : Filter.Tendsto (fun n : ℕ => c0 + 1 / ((n:ℝ) + 1)) Filter.atTop (nhds c0) := by
    have h1 : Filter.Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using h1.const_add c0
  have hquot : ∀ y : ℝ,
      Filter.Tendsto (fun n : ℕ => y / (c0 + 1 / ((n:ℝ) + 1))) Filter.atTop (nhds (y / c0)) := by
    intro y
    exact tendsto_const_nhds.div hden (ne_of_gt hc0)
  have hexp_tend : ∀ y : ℝ, Filter.Tendsto
      (fun n : ℕ => Real.exp (y / (c0 + 1 / ((n:ℝ) + 1)))) Filter.atTop
        (nhds (Real.exp (y / c0))) := by
    intro y
    exact (Real.continuous_exp.tendsto _).comp (hquot y)
  have hofReal_tend : ∀ y : ℝ, Filter.Tendsto
      (fun n : ℕ => ENNReal.ofReal (Real.exp (y / (c0 + 1 / ((n:ℝ) + 1))))) Filter.atTop
        (nhds (ENNReal.ofReal (Real.exp (y / c0)))) := by
    intro y
    exact (ENNReal.continuous_ofReal.tendsto _).comp (hexp_tend y)
  have hmono_in : ∀ ω : Ω, Monotone (fun n : ℕ =>
      ENNReal.ofReal (Real.exp (|ξ ω| / (c0 + 1 / ((n:ℝ) + 1))))) := by
    intro ω n m hnm
    have hnm' : (n:ℝ) ≤ (m:ℝ) := by exact_mod_cast hnm
    have hdm : 0 < c0 + 1 / ((m:ℝ) + 1) := by positivity
    have hle : c0 + 1 / ((m:ℝ) + 1) ≤ c0 + 1 / ((n:ℝ) + 1) := by
      have h1 : 1 / ((m:ℝ) + 1) ≤ 1 / ((n:ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      linarith
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
    exact hdivmono |ξ ω| _ _ (abs_nonneg _) hdm hle
  have htend_in : ∀ ω : Ω, Filter.Tendsto (fun n : ℕ =>
      ENNReal.ofReal (Real.exp (|ξ ω| / (c0 + 1 / ((n:ℝ) + 1))))) Filter.atTop
      (nhds (ENNReal.ofReal (Real.exp (|ξ ω| / c0)))) :=
    fun ω => hofReal_tend |ξ ω|
  have hlim : Filter.Tendsto (fun n : ℕ => ∫⁻ ω, ENNReal.ofReal
      (Real.exp (|ξ ω| / (c0 + 1 / ((n:ℝ) + 1)))) ∂P) Filter.atTop
      (nhds (∫⁻ ω, ENNReal.ofReal (Real.exp (|ξ ω| / c0)) ∂P)) :=
    MeasureTheory.lintegral_tendsto_of_tendsto_of_monotone
      (fun n => show AEMeasurable (fun ω : Ω =>
          ENNReal.ofReal (Real.exp (|ξ ω| / (c0 + 1 / ((n:ℝ) + 1))))) P from
        (ENNReal.measurable_ofReal.comp
          (((continuous_abs.measurable.comp hξ).div_const _).exp)).aemeasurable)
      (Filter.Eventually.of_forall hmono_in)
      (Filter.Eventually.of_forall htend_in)
  exact le_of_tendsto_of_tendsto' hlim tendsto_const_nhds hbound
  /- @proof-region region.target-node.session.9904c10a99c8fa71 end -/

end
end Statlib.Imported

