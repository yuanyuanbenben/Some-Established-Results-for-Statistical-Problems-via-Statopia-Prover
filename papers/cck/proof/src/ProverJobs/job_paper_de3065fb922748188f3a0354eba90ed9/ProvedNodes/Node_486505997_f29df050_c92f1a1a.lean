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
theorem statopia_math_node_486505997_f29df050 : (∀ z : ℝ,
        0 < 1 - ∫ u in Set.Iic z, ProbabilityTheory.gaussianPDFReal 0 1 u) ∧
      (∀ z : ℝ,
        ProbabilityTheory.gaussianPDFReal 0 1 z /
            (1 - ∫ u in Set.Iic z, ProbabilityTheory.gaussianPDFReal 0 1 u) ≤
          2 * max z 1) := by
  /- @proof-region region.target-node.session.229f92f3778371ef begin -/
  set φ : ℝ → ℝ := ProbabilityTheory.gaussianPDFReal 0 1 with hφ
  have hφpos : ∀ x : ℝ, 0 < φ x :=
    fun x => ProbabilityTheory.gaussianPDFReal_pos 0 1 x (by norm_num)
  have hφnonneg : ∀ x : ℝ, 0 ≤ φ x := fun x => (hφpos x).le
  have hφint : ∫ x, φ x = 1 := ProbabilityTheory.integral_gaussianPDFReal_eq_one 0 (by norm_num)
  have hφI : Integrable φ := ProbabilityTheory.integrable_gaussianPDFReal 0 1
  have hφform : ∀ x : ℝ, φ x = (√(2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) := by
    intro x
    rw [hφ, ProbabilityTheory.gaussianPDFReal_def]
    simp
  have hφanti : ∀ a b : ℝ, a ^ 2 ≤ b ^ 2 → φ b ≤ φ a := by
    intro a b hab
    rw [hφform, hφform]
    have hc : (0 : ℝ) < (√(2 * Real.pi))⁻¹ := by positivity
    have h2 : -b ^ 2 / 2 ≤ -a ^ 2 / 2 := by linarith
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h2) hc.le
  have hΦmono : ∀ a b : ℝ, a ≤ b → ∫ u in Set.Iic a, φ u ≤ ∫ u in Set.Iic b, φ u := by
    intro a b hab
    refine MeasureTheory.setIntegral_mono_set hφI.integrableOn ?_ ?_
    · exact Filter.Eventually.of_forall hφnonneg
    · filter_upwards with x hx
      exact le_trans hx hab
  have hpos1 : 0 < 1 - ∫ u in Set.Iic (1 : ℝ), φ u := by
    have hrat : 0 < φ 1 / (1 - ∫ u in Set.Iic (1 : ℝ), φ u) :=
      lt_of_lt_of_le one_pos (ext_model_4 1 one_pos).1
    by_cases hden : 1 - ∫ u in Set.Iic (1 : ℝ), φ u ≤ 0
    · have hle : φ 1 / (1 - ∫ u in Set.Iic (1 : ℝ), φ u) ≤ 0 :=
        div_nonpos_of_nonneg_of_nonpos (hφnonneg 1) hden
      linarith
    · exact not_le.mp hden
  have hΦ1le : 1 - ∫ u in Set.Iic (1 : ℝ), φ u ≤ φ 1 := by
    have h2 := (le_div_iff₀ hpos1).mp (ext_model_4 1 one_pos).1
    simpa using h2
  have hφeven : ∀ x : ℝ, φ (-x) = φ x := by
    intro x
    rw [hφform, hφform, neg_sq]
  have hΦ0 : ∫ u in Set.Iic (0 : ℝ), φ u = 1 / 2 := by
    set A := ∫ u in Set.Iic (0 : ℝ), φ u with hA
    set B := ∫ u in Set.Ioi (0 : ℝ), φ u with hB
    have keyA : A = B := by
      rw [hA, hB]
      have h2 : ∫ u in Set.Iic (0 : ℝ), φ (-u) = ∫ u in Set.Ioi (0 : ℝ), φ u := by
        simpa using integral_comp_neg_Iic (0 : ℝ) φ
      have h3 : ∫ u in Set.Iic (0 : ℝ), φ (-u) = ∫ u in Set.Iic (0 : ℝ), φ u := by
        rw [show (fun u : ℝ => φ (-u)) = φ from funext hφeven]
      exact h3.symm.trans h2
    have keySum : A + B = 1 := by
      rw [hA, hB]
      have hun : Set.Iic (0 : ℝ) ∪ Set.Ioi (0 : ℝ) = Set.univ := by
        ext x
        simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ioi, Set.mem_univ, iff_true]
        by_cases hx : x ≤ 0
        · exact Or.inl hx
        · exact Or.inr (not_le.mp hx)
      have hdisj : Disjoint (Set.Iic (0 : ℝ)) (Set.Ioi (0 : ℝ)) := by
        rw [Set.disjoint_left]
        intro a ha ha'
        rw [Set.mem_Iic] at ha
        rw [Set.mem_Ioi] at ha'
        linarith
      have h2 : ∫ u in Set.Iic (0 : ℝ) ∪ Set.Ioi (0 : ℝ), φ u
          = (∫ u in Set.Iic (0 : ℝ), φ u) + ∫ u in Set.Ioi (0 : ℝ), φ u := by
        refine MeasureTheory.setIntegral_union (f := φ) hdisj measurableSet_Ioi ?_ ?_
        · exact hφI.integrableOn
        · exact hφI.integrableOn
      rw [hun, setIntegral_univ] at h2
      rw [← h2, hφint]
    linarith
  have hmain : ∀ z : ℝ, 0 < 1 - ∫ u in Set.Iic z, φ u := by
    intro z
    by_cases hz : z ≤ 0
    · have h1 : ∫ u in Set.Iic z, φ u ≤ ∫ u in Set.Iic (1 : ℝ), φ u :=
        hΦmono z 1 (le_trans hz zero_le_one)
      linarith [hΦ1le, hφpos 1]
    · have hzpos : 0 < z := not_le.mp hz
      have hrat : 0 < φ z / (1 - ∫ u in Set.Iic z, φ u) :=
        lt_of_lt_of_le hzpos (ext_model_4 z hzpos).1
      by_cases hden : 1 - ∫ u in Set.Iic z, φ u ≤ 0
      · have hle : φ z / (1 - ∫ u in Set.Iic z, φ u) ≤ 0 :=
          div_nonpos_of_nonneg_of_nonpos (hφnonneg z) hden
        linarith
      · exact not_le.mp hden
  constructor
  · exact hmain
  · intro z
    by_cases hz1 : z ≤ 1
    · by_cases hz : z ≤ 0
      · have hmax : max z 1 = 1 := max_eq_right (le_trans hz zero_le_one)
        rw [hmax, mul_one]
        have hdenpos : 0 < 1 - ∫ u in Set.Iic z, φ u := hmain z
        have hdenhalf : (1 : ℝ) / 2 ≤ 1 - ∫ u in Set.Iic z, φ u := by
          have h1 : ∫ u in Set.Iic z, φ u ≤ ∫ u in Set.Iic (0 : ℝ), φ u := hΦmono z 0 hz
          rw [hΦ0] at h1
          linarith
        have hc0 : φ 0 = (√(2 * Real.pi))⁻¹ := by
          rw [hφform 0]
          simp
        have hnum : φ z ≤ (√(2 * Real.pi))⁻¹ := by
          have h := hφanti 0 z (by nlinarith [sq_nonneg z])
          rwa [hc0] at h
        have hc1 : (√(2 * Real.pi))⁻¹ ≤ 1 := by
          have hπ : (3 : ℝ) < Real.pi := Real.pi_gt_three
          have h0 : (0 : ℝ) < 2 * Real.pi := by linarith
          have hs : (0 : ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos_of_pos h0
          have h2 : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
            nlinarith [Real.sq_sqrt h0.le, hs, hπ]
          have hstep := mul_le_mul_of_nonneg_left h2 (le_of_lt (inv_pos.mpr hs))
          rwa [mul_one, inv_mul_cancel₀ (ne_of_gt hs)] at hstep
        rw [div_le_iff₀ hdenpos]
        linarith
      · have hzpos : (0 : ℝ) < z := not_le.mp hz
        have hmax : max z 1 = 1 := max_eq_right hz1
        rw [hmax, mul_one]
        have hdenpos : 0 < 1 - ∫ u in Set.Iic z, φ u := hmain z
        rw [div_le_iff₀ hdenpos]
        have hcomp : ∀ a : ℝ, (∫ u in Set.Iic a, φ u) + ∫ u in Set.Ioi a, φ u = 1 := by
          intro a
          have hun : Set.Iic a ∪ Set.Ioi a = Set.univ := by
            ext x
            simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ioi, Set.mem_univ, iff_true]
            by_cases hx : x ≤ a
            · exact Or.inl hx
            · exact Or.inr (not_le.mp hx)
          have hdisj : Disjoint (Set.Iic a) (Set.Ioi a) := by
            rw [Set.disjoint_left]
            intro b hb hb'
            rw [Set.mem_Iic] at hb
            rw [Set.mem_Ioi] at hb'
            linarith
          have h2 : ∫ u in Set.Iic a ∪ Set.Ioi a, φ u
              = (∫ u in Set.Iic a, φ u) + ∫ u in Set.Ioi a, φ u := by
            refine MeasureTheory.setIntegral_union (f := φ) hdisj measurableSet_Ioi ?_ ?_
            · exact hφI.integrableOn
            · exact hφI.integrableOn
          rw [hun, setIntegral_univ, hφint] at h2
          linarith
        have hsplit : ∫ u in Set.Ioi z, φ u
            = (∫ u in Set.Ioc z 1, φ u) + ∫ u in Set.Ioi (1 : ℝ), φ u := by
          have hun : Set.Ioc z 1 ∪ Set.Ioi (1 : ℝ) = Set.Ioi z := by
            ext x
            simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
            constructor
            · rintro (⟨h1, h2⟩ | h3)
              · exact h1
              · linarith
            · intro hx
              by_cases h : x ≤ 1
              · exact Or.inl ⟨hx, h⟩
              · exact Or.inr (not_le.mp h)
          have hdisj : Disjoint (Set.Ioc z 1) (Set.Ioi (1 : ℝ)) := by
            rw [Set.disjoint_left]
            intro b hb hb'
            rw [Set.mem_Ioc] at hb
            rw [Set.mem_Ioi] at hb'
            linarith
          have h2 : ∫ u in Set.Ioc z 1 ∪ Set.Ioi (1 : ℝ), φ u
              = (∫ u in Set.Ioc z 1, φ u) + ∫ u in Set.Ioi (1 : ℝ), φ u := by
            refine MeasureTheory.setIntegral_union (f := φ) hdisj measurableSet_Ioi ?_ ?_
            · exact hφI.integrableOn
            · exact hφI.integrableOn
          rw [hun] at h2
          exact h2
        have hA : φ 1 * (1 - z) ≤ ∫ u in Set.Ioc z 1, φ u := by
          have hcI : IntegrableOn (fun _ : ℝ => φ 1) (Set.Ioc z 1) := by
            haveI := Real.isFiniteMeasure_restrict_Ioc z 1
            exact MeasureTheory.integrable_const (φ 1)
          have hpt : ∀ u ∈ Set.Ioc z 1, (fun _ : ℝ => φ 1) u ≤ φ u := by
            intro u hu
            rw [Set.mem_Ioc] at hu
            exact hφanti u 1 (by nlinarith [hu.1, hu.2])
          have hmono := MeasureTheory.setIntegral_mono_on (s := Set.Ioc z 1)
            (f := fun _ : ℝ => φ 1) (g := φ) hcI hφI.integrableOn measurableSet_Ioc hpt
          rw [MeasureTheory.setIntegral_const] at hmono
          have hreal : volume.real (Set.Ioc z 1) = 1 - z := by
            show (volume (Set.Ioc z 1)).toReal = 1 - z
            rw [Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ 1 - z)]
          rw [hreal, smul_eq_mul] at hmono
          linarith
        have hB : φ 1 / 2 ≤ ∫ u in Set.Ioi (1 : ℝ), φ u := by
          have h' : φ 1 ≤ 2 * (1 - ∫ u in Set.Iic (1 : ℝ), φ u) := by
            have h := (div_le_iff₀ hpos1).mp (ext_model_4 1 one_pos).2
            calc φ 1 ≤ (1 * ((1 + 1 ^ 2) / 1 ^ 2)) * (1 - ∫ u in Set.Iic (1 : ℝ), φ u) := h
              _ = 2 * (1 - ∫ u in Set.Iic (1 : ℝ), φ u) := by norm_num
          have h2 := hcomp 1
          linarith
        have hexp_le : Real.exp ((1 - z ^ 2) / 2) ≤ 3 - 2 * z := by
          have hpos : (0 : ℝ) < 3 - 2 * z := by linarith
          have hlog : (1 - z) - (1 - z) ^ 2 / 2 ≤ Real.log (3 - 2 * z) := by
            have h1 := Real.one_sub_inv_le_log_of_pos hpos
            have h2 : (1 - z) - (1 - z) ^ 2 / 2 ≤ 1 - (3 - 2 * z)⁻¹ := by
              have h3 : (0 : ℝ) < 3 - 2 * z := hpos
              have hkey : (3 - 2 * z)⁻¹ ≤ z + (1 - z) ^ 2 / 2 := by
                rw [← one_div, div_le_iff₀ h3]
                have hw : (0 : ℝ) ≤ 1 - z := by linarith
                have hq : (0 : ℝ) ≤ (1 - z - 3 / 4) ^ 2 + 7 / 16 := by
                  nlinarith [sq_nonneg (1 - z - 3 / 4)]
                have hprod : (0 : ℝ) ≤ (1 - z) * ((1 - z - 3 / 4) ^ 2 + 7 / 16) :=
                  mul_nonneg hw hq
                nlinarith [hprod]
              linarith
            linarith
          calc Real.exp ((1 - z ^ 2) / 2) = Real.exp ((1 - z) - (1 - z) ^ 2 / 2) := by
                congr 1
                ring
            _ ≤ Real.exp (Real.log (3 - 2 * z)) := Real.exp_le_exp.mpr hlog
            _ = 3 - 2 * z := Real.exp_log hpos
        have hφzle : φ z ≤ φ 1 * (3 - 2 * z) := by
          rw [hφform, hφform]
          have hkey : Real.exp (-z ^ 2 / 2)
              = Real.exp (-1 ^ 2 / 2) * Real.exp ((1 - z ^ 2) / 2) := by
            rw [← Real.exp_add]
            congr 1
            ring
          rw [hkey]
          calc (√(2 * Real.pi))⁻¹ * (Real.exp (-1 ^ 2 / 2) * Real.exp ((1 - z ^ 2) / 2))
              = (√(2 * Real.pi))⁻¹ * Real.exp (-1 ^ 2 / 2) * Real.exp ((1 - z ^ 2) / 2) := by ring
            _ ≤ (√(2 * Real.pi))⁻¹ * Real.exp (-1 ^ 2 / 2) * (3 - 2 * z) := by
                have hpos : (0 : ℝ) < (√(2 * Real.pi))⁻¹ * Real.exp (-1 ^ 2 / 2) := by positivity
                exact mul_le_mul_of_nonneg_left hexp_le hpos.le
        have hsz := hcomp z
        have h1 := hsplit
        linarith
    · have hzgt : 1 < z := not_le.mp hz1
      have hzpos : (0 : ℝ) < z := by linarith
      have hmax : max z 1 = z := max_eq_left (le_of_lt hzgt)
      rw [hmax]
      have hle1 := (ext_model_4 z hzpos).2
      have hEq : z * ((1 + z ^ 2) / z ^ 2) = z + 1 / z := by
        field_simp
        ring
      have hle2 : z + 1 / z ≤ 2 * z := by
        have h1 : 1 / z ≤ z := by
          field_simp
          nlinarith
        linarith
      calc φ z / (1 - ∫ u in Set.Iic z, φ u) ≤ z * ((1 + z ^ 2) / z ^ 2) := hle1
        _ = z + 1 / z := hEq
        _ ≤ 2 * z := hle2
  /- @proof-region region.target-node.session.229f92f3778371ef end -/

end Statlib.Imported

