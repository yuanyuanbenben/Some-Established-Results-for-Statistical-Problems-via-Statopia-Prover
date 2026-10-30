import ProverJobs.job_paper_d731a49b3997405b944f72bca5b16eab.Vocabulary
import ProverJobs.job_paper_d731a49b3997405b944f72bca5b16eab.Base

namespace PaperProofTasks.job_paper_d731a49b3997405b944f72bca5b16eab

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open _root_.PaperProofTasks.job_paper_d731a49b3997405b944f72bca5b16eab.Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace Statlib.Imported
open _root_.Statlib

set_option autoImplicit false in
theorem statopia_math_node_2727738868_45cbd6a3 : ∀ (delta : ℝ) (hdelta_pos : 0 < delta)
    (hdelta_lt_one : delta < 1),
    ∃ s1 : ℝ, 1 < s1 ∧ ∀ s : ℝ, s1 ≤ s →
      (gaussianReal 0 1 (Set.Iic (Real.sqrt ((2 - delta) * Real.log s)))).toReal ≤
        1 - 1 / s := by
  /- @proof-region region.target-node.session.d50690c482e3f038 begin -/
  intro delta hdelta_pos hdelta_lt_one
  have h2d : 0 < 2 - delta := by linarith
  have hA : 0 < Real.sqrt (2 * Real.pi) := by positivity
  set C : ℝ := Real.log (Real.sqrt (2 * Real.pi)) + 1 / 2 with hCdef
  set T0 : ℝ := max 1 (max (16 * (2 - delta) / delta ^ 2) (4 * C / delta)) with hT0def
  have hT0_ge1 : 1 ≤ T0 := by rw [hT0def]; exact le_max_left _ _
  have hT0_ge16 : 16 * (2 - delta) / delta ^ 2 ≤ T0 :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hT0_geC : 4 * C / delta ≤ T0 :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨Real.exp T0, ?_, ?_⟩
  · have hpos : 0 < T0 := lt_of_lt_of_le one_pos hT0_ge1
    simpa using Real.exp_lt_exp.mpr hpos
  · intro s hs
    have hs1pos : 0 < Real.exp T0 := Real.exp_pos T0
    have hlogs : T0 ≤ Real.log s := by
      have h := Real.log_le_log hs1pos hs
      simpa using h
    have hT1 : 1 ≤ Real.log s := le_trans hT0_ge1 hlogs
    have hTpos : 0 < Real.log s := lt_of_lt_of_le one_pos hT1
    have hs_pos : 0 < s := lt_of_lt_of_le hs1pos hs
    have hTbig : 16 * (2 - delta) / delta ^ 2 ≤ Real.log s := le_trans hT0_ge16 hlogs
    have hTbigC : 4 * C / delta ≤ Real.log s := le_trans hT0_geC hlogs
    set x : ℝ := Real.sqrt ((2 - delta) * Real.log s) with hxdef
    have hx_nonneg : 0 ≤ x := by rw [hxdef]; exact Real.sqrt_nonneg _
    have hx_sq : x ^ 2 = (2 - delta) * Real.log s := by
      rw [hxdef, Real.sq_sqrt (le_of_lt (mul_pos h2d hTpos))]
    have hx_le : x ≤ delta / 4 * Real.log s := by
      have hδ2 : (0 : ℝ) < delta ^ 2 := by positivity
      have hkey : 16 * (2 - delta) ≤ delta ^ 2 * Real.log s := by
        have hm := mul_le_mul_of_nonneg_left hTbig (le_of_lt hδ2)
        have heq : delta ^ 2 * (16 * (2 - delta) / delta ^ 2) = 16 * (2 - delta) := by
          rw [mul_comm, div_mul_cancel₀ (16 * (2 - delta)) (ne_of_gt hδ2)]
        linarith [hm, heq]
      have hsq : x ^ 2 ≤ (delta / 4 * Real.log s) ^ 2 := by
        rw [hx_sq]
        nlinarith [hkey, hδ2, hTpos]
      have hy : 0 ≤ delta / 4 * Real.log s := by
        have h4 : (0 : ℝ) < delta / 4 := by linarith
        exact mul_nonneg (le_of_lt h4) (le_of_lt hTpos)
      have habs := sq_le_sq.mp hsq
      rwa [abs_of_nonneg hx_nonneg, abs_of_nonneg hy] at habs
    have hC_le : C ≤ delta / 4 * Real.log s := by
      have h4 : (0 : ℝ) < delta / 4 := by linarith
      have hm := mul_le_mul_of_nonneg_left hTbigC (le_of_lt h4)
      have hne : (delta : ℝ) ≠ 0 := ne_of_gt hdelta_pos
      have heq : delta / 4 * (4 * C / delta) = C := by
        field_simp
      linarith [hm, heq]
    set K' : ℝ := (√(2 * Real.pi))⁻¹ * Real.exp (-(1 / 2)) with hK'def
    have hK'pos : 0 < K' := by
      rw [hK'def]
      exact mul_pos (inv_pos.mpr hA) (Real.exp_pos _)
    have hφform : ∀ u : ℝ, gaussianPDFReal 0 1 u = (√(2 * Real.pi))⁻¹ * Real.exp (-(u ^ 2) / 2) := by
      intro u
      simp only [ProbabilityTheory.gaussianPDFReal_def, NNReal.coe_one, sub_zero, mul_one]
    have hφ_K : gaussianPDFReal 0 1 (x + 1) = K' * Real.exp (-(x ^ 2) / 2) * Real.exp (-x) := by
      rw [hφform (x + 1), hK'def]
      rw [show -((x + 1) ^ 2) / 2 = -(x ^ 2) / 2 + -x + -(1 / 2) by ring]
      rw [Real.exp_add, Real.exp_add]
      ring
    have hlog_K : Real.log (gaussianPDFReal 0 1 (x + 1)) = Real.log K' - x ^ 2 / 2 - x := by
      rw [hφ_K, Real.log_mul (mul_ne_zero hK'pos.ne' (Real.exp_pos _).ne') (Real.exp_pos _).ne',
        Real.log_mul hK'pos.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp]
      ring
    have hphi_pos : 0 < gaussianPDFReal 0 1 (x + 1) := by
      rw [hφ_K]
      exact mul_pos (mul_pos hK'pos (Real.exp_pos _)) (Real.exp_pos _)
    have hphi_exp : Real.exp (Real.log K' - x ^ 2 / 2 - x) = gaussianPDFReal 0 1 (x + 1) := by
      rw [← hlog_K, Real.exp_log hphi_pos]
    have h_target : 1 / s ≤ gaussianPDFReal 0 1 (x + 1) := by
      have h1exp : 1 / s = Real.exp (-Real.log s) := by
        have h2 : Real.exp (-Real.log s) = 1 / s := by
          rw [Real.exp_neg, one_div, Real.exp_log hs_pos]
        exact h2.symm
      have hK'le : -Real.log K' ≤ delta / 4 * Real.log s := by
        have hlogK' : -Real.log K' = C := by
          rw [hK'def, Real.log_mul (inv_ne_zero hA.ne') (Real.exp_pos _).ne', Real.log_inv,
            Real.log_exp, hCdef]
          ring
        linarith [hlogK', hC_le]
      rw [h1exp, ← hphi_exp, Real.exp_le_exp, hx_sq]
      linarith [hx_le, hK'le]
    have hcompl : ((gaussianReal 0 1) (Set.Iic x)).toReal + ((gaussianReal 0 1) (Set.Ioi x)).toReal = 1 := by
      have hsum : (gaussianReal 0 1) (Set.Iic x) + (gaussianReal 0 1) (Set.Ioi x) = 1 := by
        have h := MeasureTheory.measure_add_measure_compl (μ := gaussianReal 0 1) (s := Set.Iic x) measurableSet_Iic
        rw [Set.compl_Iic] at h
        rwa [MeasureTheory.measure_univ] at h
      calc ((gaussianReal 0 1) (Set.Iic x)).toReal + ((gaussianReal 0 1) (Set.Ioi x)).toReal
          = ((gaussianReal 0 1) (Set.Iic x) + (gaussianReal 0 1) (Set.Ioi x)).toReal := by
            rw [ENNReal.toReal_add (MeasureTheory.measure_ne_top _ _) (MeasureTheory.measure_ne_top _ _)]
        _ = (1 : ℝ≥0∞).toReal := by rw [hsum]
        _ = 1 := ENNReal.toReal_one
    have hAeq : ((gaussianReal 0 1) (Set.Iic x)).toReal = 1 - ((gaussianReal 0 1) (Set.Ioi x)).toReal := by
      linarith [hcompl]
    have hQ_ge : 1 / s ≤ ((gaussianReal 0 1) (Set.Ioi x)).toReal := by
      have hcont : Continuous (gaussianPDFReal 0 1) := by
        have hfun : gaussianPDFReal 0 1 = fun u : ℝ => (√(2 * Real.pi))⁻¹ * Real.exp (-(u ^ 2) / 2) :=
          funext hφform
        rw [hfun]
        fun_prop
      have hsub : Set.Ioc x (x + 1) ⊆ Set.Ioi x := fun u hu => hu.1
      have hmono : (gaussianReal 0 1) (Set.Ioc x (x + 1)) ≤ (gaussianReal 0 1) (Set.Ioi x) :=
        MeasureTheory.measure_mono hsub
      have hto : ((gaussianReal 0 1) (Set.Ioc x (x + 1))).toReal ≤ ((gaussianReal 0 1) (Set.Ioi x)).toReal :=
        ENNReal.toReal_mono (MeasureTheory.measure_ne_top _ _) hmono
      have hφle : ∀ u ∈ Set.Icc x (x + 1), gaussianPDFReal 0 1 (x + 1) ≤ gaussianPDFReal 0 1 u := by
        intro u hu
        obtain ⟨hu1, hu2⟩ := hu
        rw [hφform (x + 1), hφform u]
        refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (Real.sqrt_nonneg _))
        rw [Real.exp_le_exp]
        have h1 : u ^ 2 ≤ (x + 1) ^ 2 := by nlinarith
        linarith
      have hxle1 : x ≤ x + 1 := by linarith
      have hstep : ∫ u in x..(x + 1), gaussianPDFReal 0 1 (x + 1) ≤ ∫ u in x..(x + 1), gaussianPDFReal 0 1 u :=
        intervalIntegral.integral_mono_on hxle1 intervalIntegrable_const
          (hcont.intervalIntegrable x (x + 1)) hφle
      have hconst_int : ∫ u in x..(x + 1), gaussianPDFReal 0 1 (x + 1) = gaussianPDFReal 0 1 (x + 1) := by
        rw [intervalIntegral.integral_const, show x + 1 - x = 1 by ring, one_smul]
      have hI_ge : gaussianPDFReal 0 1 (x + 1) ≤ ∫ u in Set.Ioc x (x + 1), gaussianPDFReal 0 1 u := by
        rw [hconst_int] at hstep
        rwa [intervalIntegral.integral_of_le hxle1] at hstep
      have heq : (gaussianReal 0 1) (Set.Ioc x (x + 1)) =
          ENNReal.ofReal (∫ u in Set.Ioc x (x + 1), gaussianPDFReal 0 1 u) :=
        ProbabilityTheory.gaussianReal_apply_eq_integral 0 one_ne_zero _
      have hpos_int : 0 < ∫ u in Set.Ioc x (x + 1), gaussianPDFReal 0 1 u :=
        lt_of_lt_of_le hphi_pos hI_ge
      have hto2 : ((gaussianReal 0 1) (Set.Ioc x (x + 1))).toReal =
          ∫ u in Set.Ioc x (x + 1), gaussianPDFReal 0 1 u := by
        rw [heq, ENNReal.toReal_ofReal (le_of_lt hpos_int)]
      calc 1 / s ≤ gaussianPDFReal 0 1 (x + 1) := h_target
        _ ≤ ∫ u in Set.Ioc x (x + 1), gaussianPDFReal 0 1 u := hI_ge
        _ = ((gaussianReal 0 1) (Set.Ioc x (x + 1))).toReal := hto2.symm
        _ ≤ ((gaussianReal 0 1) (Set.Ioi x)).toReal := hto
    linarith [hAeq, hQ_ge]
  /- @proof-region region.target-node.session.d50690c482e3f038 end -/

end Statlib.Imported

