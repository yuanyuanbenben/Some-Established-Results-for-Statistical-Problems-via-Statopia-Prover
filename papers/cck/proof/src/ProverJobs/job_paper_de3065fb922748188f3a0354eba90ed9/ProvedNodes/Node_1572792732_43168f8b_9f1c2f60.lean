import Statlib.StatFoundation.Statistics.Asymptotic.ScoreCLT
import Statlib.StatFoundation.Convergence.Resampling.GaussianMaxComparison
import Statlib.StatFoundation.Convergence.AnalysisTools.GaussianMaxAnticoncentration
import Statlib.StatFoundation.Statistics.Asymptotic.LAN
import Statlib.StatFoundation.Convergence.AnalysisTools.SmoothMax
import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.Vocabulary
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.Base
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.ExternalNodes.Node_103826e30030eda123b2

namespace PaperProofTasks.job_paper_de3065fb922748188f3a0354eba90ed9

open _root_.PaperProofTasks.job_paper_de3065fb922748188f3a0354eba90ed9.Statlib.Imported
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

set_option autoImplicit false in
theorem statopia_math_node_1572792732_43168f8b : ∀ (c : ℝ) (hc : 0 ≤ c),
    ∫ u in Set.Iic (-c), ProbabilityTheory.gaussianPDFReal 0 1 u ≤ Real.exp (-(c ^ 2) / 2) := by
  /- @proof-region region.target-node.session.e78634964707dda2 begin -/
  intro c hc
  have evenφ : ∀ x : ℝ,
      ProbabilityTheory.gaussianPDFReal 0 1 (-x) = ProbabilityTheory.gaussianPDFReal 0 1 x := by
    intro x
    simp only [ProbabilityTheory.gaussianPDFReal_def, NNReal.coe_one]
    rw [show (-x - 0 : ℝ) ^ 2 = (x - 0 : ℝ) ^ 2 from by ring]
  have hrefl : ∀ d : ℝ, (∫ u in Set.Iic (-d), ProbabilityTheory.gaussianPDFReal 0 1 u)
      = ∫ u in Set.Ioi d, ProbabilityTheory.gaussianPDFReal 0 1 u := by
    intro d
    rw [← integral_comp_neg_Ioi d (ProbabilityTheory.gaussianPDFReal 0 1)]
    simp only [evenφ]
  by_cases hc1 : c < 1
  · have hmono : (∫ u in Set.Iic (-c), ProbabilityTheory.gaussianPDFReal 0 1 u)
        ≤ ∫ u in Set.Iic 0, ProbabilityTheory.gaussianPDFReal 0 1 u := by
      refine MeasureTheory.setIntegral_mono_set (μ := volume) ?_ ?_ ?_
      · exact (ProbabilityTheory.integrable_gaussianPDFReal 0 1).integrableOn
      · exact Filter.Eventually.of_forall (fun x => ProbabilityTheory.gaussianPDFReal_nonneg 0 1 x)
      · exact Filter.Eventually.of_forall (fun x (hx : x ∈ Set.Iic (-c)) =>
          le_trans (show x ≤ -c from hx) (by linarith))
    have hhalf : (∫ u in Set.Iic 0, ProbabilityTheory.gaussianPDFReal 0 1 u) = 1 / 2 := by
      have hsym0 : (∫ u in Set.Iic (0:ℝ), ProbabilityTheory.gaussianPDFReal 0 1 u)
          = ∫ u in Set.Ioi (0:ℝ), ProbabilityTheory.gaussianPDFReal 0 1 u := by
        simpa using hrefl 0
      have hsum : (∫ u in Set.Iic (0:ℝ), ProbabilityTheory.gaussianPDFReal 0 1 u)
          + (∫ u in Set.Ioi (0:ℝ), ProbabilityTheory.gaussianPDFReal 0 1 u) = 1 := by
        have h := MeasureTheory.integral_add_compl (μ := volume) (s := Set.Iic (0:ℝ))
          (f := ProbabilityTheory.gaussianPDFReal 0 1) measurableSet_Iic
          (ProbabilityTheory.integrable_gaussianPDFReal 0 1)
        rw [Set.compl_Iic, ProbabilityTheory.integral_gaussianPDFReal_eq_one 0 one_ne_zero] at h
        exact h
      linarith [hsym0, hsum]
    have hhalf_le : (1 / 2 : ℝ) ≤ Real.exp (-1 / 2) := by
      have h := Real.add_one_le_exp (-1 / 2)
      linarith
    have hexp_mono : Real.exp (-1 / 2) ≤ Real.exp (-(c ^ 2) / 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hc, hc1]
    calc ∫ u in Set.Iic (-c), ProbabilityTheory.gaussianPDFReal 0 1 u
        ≤ ∫ u in Set.Iic 0, ProbabilityTheory.gaussianPDFReal 0 1 u := hmono
      _ = 1 / 2 := hhalf
      _ ≤ Real.exp (-1 / 2) := hhalf_le
      _ ≤ Real.exp (-(c ^ 2) / 2) := hexp_mono
  · push_neg at hc1
    have hcpos : 0 < c := by linarith
    have hsymm : (∫ u in Set.Iic (-c), ProbabilityTheory.gaussianPDFReal 0 1 u)
        = ∫ u in Set.Ioi c, ProbabilityTheory.gaussianPDFReal 0 1 u := hrefl c
    have hcompl : (∫ u in Set.Iic c, ProbabilityTheory.gaussianPDFReal 0 1 u)
        + (∫ u in Set.Ioi c, ProbabilityTheory.gaussianPDFReal 0 1 u) = 1 := by
      have h := MeasureTheory.integral_add_compl (μ := volume) (s := Set.Iic c)
        (f := ProbabilityTheory.gaussianPDFReal 0 1) measurableSet_Iic
        (ProbabilityTheory.integrable_gaussianPDFReal 0 1)
      rw [Set.compl_Iic, ProbabilityTheory.integral_gaussianPDFReal_eq_one 0 one_ne_zero] at h
      exact h
    have hST : (1 - ∫ u in Set.Iic c, ProbabilityTheory.gaussianPDFReal 0 1 u)
        = ∫ u in Set.Ioi c, ProbabilityTheory.gaussianPDFReal 0 1 u := by linarith [hcompl]
    have hmill := (ext_model_4 c hcpos).1
    rw [hST] at hmill
    have hS_le_one : (∫ u in Set.Iic c, ProbabilityTheory.gaussianPDFReal 0 1 u) ≤ 1 := by
      have h := MeasureTheory.setIntegral_le_integral (s := Set.Iic c) (μ := volume)
        (ProbabilityTheory.integrable_gaussianPDFReal 0 1)
        (Filter.Eventually.of_forall (fun x => ProbabilityTheory.gaussianPDFReal_nonneg 0 1 x))
      rwa [ProbabilityTheory.integral_gaussianPDFReal_eq_one 0 one_ne_zero] at h
    have hT_nonneg : 0 ≤ ∫ u in Set.Ioi c, ProbabilityTheory.gaussianPDFReal 0 1 u := by
      linarith [hcompl, hS_le_one]
    have hT_pos : 0 < ∫ u in Set.Ioi c, ProbabilityTheory.gaussianPDFReal 0 1 u := by
      rcases lt_or_eq_of_le hT_nonneg with hh | hh
      · exact hh
      · exfalso
        rw [← hh, div_zero] at hmill
        linarith [hc1, hmill]
    have hkey : c * (∫ u in Set.Ioi c, ProbabilityTheory.gaussianPDFReal 0 1 u)
        ≤ ProbabilityTheory.gaussianPDFReal 0 1 c := by
      have hm := mul_le_mul_of_nonneg_right hmill (le_of_lt hT_pos)
      rwa [div_mul_cancel₀ _ (ne_of_gt hT_pos)] at hm
    have hTle : (∫ u in Set.Ioi c, ProbabilityTheory.gaussianPDFReal 0 1 u)
        ≤ ProbabilityTheory.gaussianPDFReal 0 1 c / c := by
      rw [le_div_iff₀ hcpos]
      nlinarith [hkey]
    have hphi : ProbabilityTheory.gaussianPDFReal 0 1 c
        = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(c ^ 2) / 2) := by
      rw [ProbabilityTheory.gaussianPDFReal_def]
      simp only [NNReal.coe_one, mul_one, sub_zero, neg_div]
    have hcoef : (Real.sqrt (2 * Real.pi))⁻¹ ≤ c := by
      have hsqrt_ge_one : (1:ℝ) ≤ Real.sqrt (2 * Real.pi) := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt (by nlinarith [Real.pi_gt_three])
      have hsqrt_pos : (0:ℝ) < Real.sqrt (2 * Real.pi) := by linarith
      rw [inv_eq_one_div, div_le_iff₀ hsqrt_pos]
      nlinarith [hsqrt_ge_one, hc1]
    have hexp_pos : 0 < Real.exp (-(c ^ 2) / 2) := Real.exp_pos _
    have hphi_diff : ProbabilityTheory.gaussianPDFReal 0 1 c / c ≤ Real.exp (-(c ^ 2) / 2) := by
      rw [hphi, div_le_iff₀ hcpos]
      have hh : Real.exp (-(c ^ 2) / 2) * (Real.sqrt (2 * Real.pi))⁻¹
          ≤ Real.exp (-(c ^ 2) / 2) * c :=
        mul_le_mul_of_nonneg_left hcoef (le_of_lt hexp_pos)
      calc (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(c ^ 2) / 2)
          = Real.exp (-(c ^ 2) / 2) * (Real.sqrt (2 * Real.pi))⁻¹ := by ring
        _ ≤ Real.exp (-(c ^ 2) / 2) * c := hh
    rw [hsymm]
    calc ∫ u in Set.Ioi c, ProbabilityTheory.gaussianPDFReal 0 1 u
        ≤ ProbabilityTheory.gaussianPDFReal 0 1 c / c := hTle
      _ ≤ Real.exp (-(c ^ 2) / 2) := hphi_diff
  /- @proof-region region.target-node.session.e78634964707dda2 end -/

end Statlib.Imported

