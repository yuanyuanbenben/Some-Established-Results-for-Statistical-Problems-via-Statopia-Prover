import ProverJobs.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Vocabulary
import ProverJobs.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Base
import ProverJobs.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.ProvedNodes.Node_128714905_89e34666_a1dd6029

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
theorem statopia_math_node_2747529702_f88a4914 : ∀ (Om : Type*) [MeasurableSpace Om] (P : Measure Om) [IsProbabilityMeasure P]
    (xi : Om → ℝ) (hxi : Measurable xi) (c0 : ℝ) (hc0 : 0 < c0)
    (horlicz : Statlib.StatFoundation.Vocabulary.orliczNorm 1 xi P
      ≤ ENNReal.ofReal c0),
    MemLp xi 4 P ∧
      ∫ om, xi om ^ 4 ∂P ≤ 2 * (4 / Real.exp 1) ^ 4 * c0 ^ 4 := by
  /- @proof-region region.target-node.session.ae5e1329fbd7ac7d begin -/
  intro Om _ P _ xi hxi c0 hc0 horlicz
  have hA : ∫⁻ om, ENNReal.ofReal (Real.exp (|xi om| / c0)) ∂P ≤ 2 :=
    statopia_math_node_128714905_89e34666 P xi hxi c0 hc0 horlicz
  have hx4 : ∀ x : ℝ, 0 ≤ x → x ^ 4 ≤ (4 / Real.exp 1) ^ 4 * Real.exp x := by
    intro x hx
    have h1 : x / 4 ≤ Real.exp (x / 4 - 1) := by
      have h := Real.add_one_le_exp (x / 4 - 1)
      linarith
    have h2 : (x / 4) ^ 4 ≤ Real.exp (x / 4 - 1) ^ 4 := pow_le_pow_left₀ (by positivity) h1 4
    have h3 : Real.exp (x / 4 - 1) ^ 4 = Real.exp (x - 4) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    have h4 : x ^ 4 = 256 * (x / 4) ^ 4 := by
      rw [div_pow]
      ring
    have h6 : Real.exp 4 = Real.exp 1 ^ 4 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have h8 : (x / 4) ^ 4 * Real.exp 4 ≤ Real.exp x := by
      have hm := mul_le_mul_of_nonneg_right h2 (Real.exp_pos 4).le
      rw [h3, ← Real.exp_add] at hm
      have hx4' : x - 4 + 4 = x := by ring
      rw [hx4'] at hm
      exact hm
    have hE : (0:ℝ) < Real.exp 1 ^ 4 := by positivity
    have h7 : (4 / Real.exp 1) ^ 4 = 256 / Real.exp 1 ^ 4 := by
      rw [div_pow]
      norm_num
    rw [h7, div_mul_eq_mul_div, le_div_iff₀ hE, ← h6, h4, mul_assoc]
    exact mul_le_mul_of_nonneg_left h8 (by norm_num : (0:ℝ) ≤ 256)
  have hExpInt : Integrable (fun om => Real.exp (|xi om| / c0)) P := by
    refine ⟨?_, ?_⟩
    · exact (Real.continuous_exp.measurable.comp (hxi.abs.div_const c0)).aestronglyMeasurable
    · rw [MeasureTheory.hasFiniteIntegral_iff_ofReal
        (Filter.Eventually.of_forall fun om => (Real.exp_pos _).le)]
      exact lt_of_le_of_lt hA (by simp)
  have hExpLe : ∫ om, Real.exp (|xi om| / c0) ∂P ≤ 2 := by
    have h1 : ENNReal.ofReal (∫ om, Real.exp (|xi om| / c0) ∂P)
        = ∫⁻ om, ENNReal.ofReal (Real.exp (|xi om| / c0)) ∂P :=
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal hExpInt
        (Filter.Eventually.of_forall fun om => (Real.exp_pos _).le)
    have h2 : ENNReal.ofReal (∫ om, Real.exp (|xi om| / c0) ∂P) ≤ ENNReal.ofReal (2 : ℝ) := by
      rw [h1]
      simpa using hA
    exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp h2
  have hc0ne : c0 ≠ 0 := ne_of_gt hc0
  have hpt : ∀ om, (xi om) ^ 4 ≤ c0 ^ 4 * (4 / Real.exp 1) ^ 4 * Real.exp (|xi om| / c0) := by
    intro om
    have hu : 0 ≤ |xi om| / c0 := by positivity
    have hstep : (|xi om| / c0) ^ 4 ≤ (4 / Real.exp 1) ^ 4 * Real.exp (|xi om| / c0) := hx4 _ hu
    have hmul : c0 ^ 4 * (|xi om| / c0) ^ 4 ≤
        c0 ^ 4 * ((4 / Real.exp 1) ^ 4 * Real.exp (|xi om| / c0)) :=
      mul_le_mul_of_nonneg_left hstep (by positivity)
    have hxm : (|xi om|) ^ 4 = c0 ^ 4 * (|xi om| / c0) ^ 4 := by
      rw [div_pow]
      field_simp
    have habs : (xi om) ^ 4 = (|xi om|) ^ 4 := by
      rw [← abs_pow, abs_of_nonneg (by positivity)]
    rw [habs, hxm]
    calc c0 ^ 4 * (|xi om| / c0) ^ 4
        ≤ c0 ^ 4 * ((4 / Real.exp 1) ^ 4 * Real.exp (|xi om| / c0)) := hmul
      _ = c0 ^ 4 * (4 / Real.exp 1) ^ 4 * Real.exp (|xi om| / c0) := by ring
  have hint4 : Integrable (fun om => (xi om) ^ 4) P := by
    have hdom : Integrable (fun om => c0 ^ 4 * (4 / Real.exp 1) ^ 4 * Real.exp (|xi om| / c0)) P :=
      hExpInt.const_mul (c0 ^ 4 * (4 / Real.exp 1) ^ 4)
    have hmeas4 : AEStronglyMeasurable (fun om => (xi om) ^ 4) P :=
      (hxi.pow_const 4).aestronglyMeasurable
    refine hdom.mono' hmeas4 ?_
    filter_upwards with om
    rw [Real.norm_of_nonneg (by positivity)]
    exact hpt om
  have hpt' : ∀ om, (|xi om|) ^ 4 ≤ c0 ^ 4 * (4 / Real.exp 1) ^ 4 * Real.exp (|xi om| / c0) := by
    intro om
    rw [← abs_pow, abs_of_nonneg (by positivity)]
    exact hpt om
  have hnorm : ∀ om, ‖xi om‖ₑ ^ (4 : ℝ) ≤
      ENNReal.ofReal (c0 ^ 4 * (4 / Real.exp 1) ^ 4) * ENNReal.ofReal (Real.exp (|xi om| / c0)) := by
    intro om
    have h1 : ‖xi om‖ₑ = ENNReal.ofReal (|xi om|) := Real.enorm_eq_ofReal_abs (xi om)
    rw [h1, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg (xi om)) (by norm_num : (0:ℝ) ≤ 4)]
    rw [show |xi om| ^ (4 : ℝ) = |xi om| ^ (4 : ℕ) by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]]
    refine le_trans (ENNReal.ofReal_le_ofReal (hpt' om)) ?_
    rw [ENNReal.ofReal_mul (by positivity)]
  have hfin : ∫⁻ om, ‖xi om‖ₑ ^ (4 : ℝ) ∂P < ⊤ := by
    have hle : ∫⁻ om, ‖xi om‖ₑ ^ (4 : ℝ) ∂P ≤
        ENNReal.ofReal (c0 ^ 4 * (4 / Real.exp 1) ^ 4) *
          ∫⁻ om, ENNReal.ofReal (Real.exp (|xi om| / c0)) ∂P := by
      have hmeasE : Measurable fun a => ENNReal.ofReal (Real.exp (|xi a| / c0)) :=
        (Real.continuous_exp.measurable.comp (hxi.abs.div_const c0)).ennreal_ofReal
      refine le_trans (MeasureTheory.lintegral_mono hnorm) ?_
      rw [MeasureTheory.lintegral_const_mul]
      exact hmeasE
    have hA' : ∫⁻ om, ENNReal.ofReal (Real.exp (|xi om| / c0)) ∂P ≤ ENNReal.ofReal (2 : ℝ) := by
      simpa using hA
    refine lt_of_le_of_lt (le_trans hle (mul_le_mul_of_nonneg_left hA' (zero_le _))) ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_lt_top
  have hmem : MemLp xi 4 P := by
    refine ⟨hxi.aestronglyMeasurable, ?_⟩
    refine (MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (p := (4 : ENNReal))
      (by norm_num) (by norm_num)).mpr ?_
    simpa using hfin
  refine ⟨hmem, ?_⟩
  have h0 : 0 ≤ c0 ^ 4 * (4 / Real.exp 1) ^ 4 := by positivity
  calc ∫ om, (xi om) ^ 4 ∂P
      ≤ ∫ om, c0 ^ 4 * (4 / Real.exp 1) ^ 4 * Real.exp (|xi om| / c0) ∂P :=
        MeasureTheory.integral_mono hint4 (hExpInt.const_mul _) hpt
    _ = c0 ^ 4 * (4 / Real.exp 1) ^ 4 * ∫ om, Real.exp (|xi om| / c0) ∂P := by
        rw [MeasureTheory.integral_const_mul]
    _ ≤ c0 ^ 4 * (4 / Real.exp 1) ^ 4 * 2 := mul_le_mul_of_nonneg_left hExpLe h0
    _ = 2 * (4 / Real.exp 1) ^ 4 * c0 ^ 4 := by ring_nf
  /- @proof-region region.target-node.session.ae5e1329fbd7ac7d end -/

end
end Statlib.Imported

