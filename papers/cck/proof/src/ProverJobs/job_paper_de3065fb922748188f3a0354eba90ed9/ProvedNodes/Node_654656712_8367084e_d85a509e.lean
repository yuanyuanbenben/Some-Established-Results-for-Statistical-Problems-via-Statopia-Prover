import Statlib.StatFoundation.Statistics.Asymptotic.ScoreCLT
import Statlib.StatFoundation.Convergence.Resampling.GaussianMaxComparison
import Statlib.StatFoundation.Convergence.AnalysisTools.GaussianMaxAnticoncentration
import Statlib.StatFoundation.Statistics.Asymptotic.LAN
import Statlib.StatFoundation.Convergence.AnalysisTools.SmoothMax
import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.Vocabulary
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.Base

namespace PaperProofTasks.job_paper_de3065fb922748188f3a0354eba90ed9

open _root_.PaperProofTasks.job_paper_de3065fb922748188f3a0354eba90ed9.Statlib.Imported
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

set_option autoImplicit false in
theorem statopia_math_node_654656712_8367084e : ∀ (s t : ℝ) (hs : 0 < s) (hst : s ≤ t),
    (let C0 : ℝ := t / s + (t / s - 1) * Real.sqrt 2 + (2 - s / t)
     let C : ℝ := (4 * C0 + 1) / s
     0 < C ∧ C * s = 4 * C0 + 1 ∧ 1 ≤ 4 * C0 + 1 ∧ 1 / s ≤ C) ∧
    (∀ (a L ε : ℝ), 0 ≤ a → 0 ≤ L → 0 < ε → ε ≤ s →
      let delta : ℝ := 1 / s - 1 / t
      let sigma : ℝ := Real.sqrt (2 * L)
      let R : ℝ := Real.sqrt (max 1 L)
      let T0 : ℝ := ε + t * (a + sigma)
      let C0 : ℝ := t / s + (t / s - 1) * Real.sqrt 2 + (2 - s / t)
      1 ≤ R ∧ sigma ≤ Real.sqrt 2 * R ∧ 0 ≤ delta ∧
        delta * T0 + a + 1 ≤ C0 * (a + R)) := by
  /- @proof-region region.target-node.session.db666e2494ed3b90 begin -/
  intro s t hs hst
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have hs0 : s ≠ 0 := ne_of_gt hs
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt2 : 0 < Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg 2]
  constructor
  · dsimp only
    have hx1 : 0 ≤ t / s - 1 := by
      have h : (t - s) / s = t / s - 1 := by rw [sub_div, div_self hs0]
      rw [← h]
      exact div_nonneg (by linarith) (le_of_lt hs)
    have hy1 : 0 ≤ 1 - s / t := by
      have h : (t - s) / t = 1 - s / t := by rw [sub_div, div_self ht0]
      rw [← h]
      exact div_nonneg (by linarith) (le_of_lt ht)
    have hC0 : 2 ≤ t / s + (t / s - 1) * Real.sqrt 2 + (2 - s / t) := by
      have hmul : 0 ≤ (t / s - 1) * Real.sqrt 2 := mul_nonneg hx1 (le_of_lt hsqrt2)
      linarith
    have hnum : 0 < 4 * (t / s + (t / s - 1) * Real.sqrt 2 + (2 - s / t)) + 1 := by linarith
    refine ⟨div_pos hnum hs, ?_, ?_, ?_⟩
    · field_simp
    · linarith
    · have hd : (4 * (t / s + (t / s - 1) * Real.sqrt 2 + (2 - s / t)) + 1) / s - 1 / s
          = 4 * (t / s + (t / s - 1) * Real.sqrt 2 + (2 - s / t)) / s := by
        rw [← sub_div]
        ring
      have h4 : 0 ≤ 4 * (t / s + (t / s - 1) * Real.sqrt 2 + (2 - s / t)) / s :=
        div_nonneg (by linarith) (le_of_lt hs)
      linarith
  · intro a L ε ha hL hε hεs
    dsimp only
    set x : ℝ := t / s with hx
    set y : ℝ := s / t with hy
    set sg : ℝ := Real.sqrt (2 * L) with hsg
    set R : ℝ := Real.sqrt (max 1 L) with hR
    have hxpos : 0 < x := by rw [hx]; exact div_pos ht hs
    have hR1 : 1 ≤ R := by
      rw [hR]
      simpa using Real.sqrt_le_sqrt (le_max_left (1 : ℝ) L)
    have hsgR : sg ≤ Real.sqrt 2 * R := by
      rw [hsg, hR]
      by_cases hL1 : L ≤ 1
      · rw [max_eq_left hL1]
        have h2 : Real.sqrt (2 * L) ≤ Real.sqrt 2 := Real.sqrt_le_sqrt (by linarith)
        simpa using h2
      · rw [max_eq_right (le_of_lt (not_le.mp hL1))]
        exact le_of_eq (Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) L)
    have hδ : 0 ≤ 1 / s - 1 / t := by
      have h : (t - s) / (s * t) = 1 / s - 1 / t := by
        field_simp
      rw [← h]
      exact div_nonneg (by linarith) (le_of_lt (mul_pos hs ht))
    refine ⟨hR1, hsgR, hδ, ?_⟩
    have hdt : 0 ≤ x - 1 := by
      rw [hx]
      have h : (t - s) / s = t / s - 1 := by rw [sub_div, div_self hs0]
      rw [← h]
      exact div_nonneg (by linarith) (le_of_lt hs)
    have hdy : 0 ≤ 2 - y := by
      rw [hy]
      have h2 : (t - s) / t = 1 - s / t := by rw [sub_div, div_self ht0]
      have h3 : 0 ≤ (t - s) / t := div_nonneg (by linarith) (le_of_lt ht)
      linarith
    have hes1 : ε / s ≤ 1 := by
      have h2 : (s - ε) / s = 1 - ε / s := by rw [sub_div, div_self hs0]
      have h3 : 0 ≤ (s - ε) / s := div_nonneg (by linarith) (le_of_lt hs)
      linarith
    have het : ε / t ≤ y := by
      rw [hy]
      have h2 : (s - ε) / t = s / t - ε / t := by rw [sub_div]
      have h3 : 0 ≤ (s - ε) / t := div_nonneg (by linarith) (le_of_lt ht)
      linarith
    have hA : (1 / s - 1 / t) * t = x - 1 := by
      rw [hx]
      field_simp
    have hde : (1 / s - 1 / t) * ε = ε / s - ε / t := by ring
    have hdT0 : (1 / s - 1 / t) * (ε + t * (a + sg)) ≤
        (1 - y) + (x - 1) * (a + Real.sqrt 2 * R) := by
      have h1 : (1 / s - 1 / t) * ε ≤ 1 - y := by
        have hkey : 1 - y - (1 / s - 1 / t) * ε = (t - s) * (s - ε) / (t * s) := by
          rw [hy]
          field_simp
          try ring
        have hnn : 0 ≤ (t - s) * (s - ε) / (t * s) :=
          div_nonneg (mul_nonneg (by linarith) (by linarith)) (le_of_lt (mul_pos ht hs))
        linarith
      have h2 : ((1 / s - 1 / t) * t) * (a + sg) ≤ (x - 1) * (a + Real.sqrt 2 * R) := by
        rw [hA]
        exact mul_le_mul_of_nonneg_left (by linarith) hdt
      have h3 : (1 / s - 1 / t) * (ε + t * (a + sg))
          = (1 / s - 1 / t) * ε + ((1 / s - 1 / t) * t) * (a + sg) := by ring
      linarith
    have hstep : (1 / s - 1 / t) * (ε + t * (a + sg)) + a + 1
        ≤ (x - 1) * (a + Real.sqrt 2 * R) + (1 - y) + a + 1 := by linarith
    have hsimp : (x - 1) * (a + Real.sqrt 2 * R) + (1 - y) + a + 1
        = x * a + (x - 1) * Real.sqrt 2 * R + (2 - y) := by ring
    have hA1 : x * a ≤ x * (a + R) :=
      mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hxpos)
    have hB1 : (x - 1) * Real.sqrt 2 * R ≤ (x - 1) * Real.sqrt 2 * (a + R) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hdt (le_of_lt hsqrt2))
    have hC1 : 2 - y ≤ (2 - y) * (a + R) := by
      calc 2 - y = (2 - y) * 1 := by ring
        _ ≤ (2 - y) * (a + R) := mul_le_mul_of_nonneg_left (by linarith) hdy
    have hsum : x * (a + R) + (x - 1) * Real.sqrt 2 * (a + R) + (2 - y) * (a + R)
        = (x + (x - 1) * Real.sqrt 2 + (2 - y)) * (a + R) := by ring
    have hfinal : x * a + (x - 1) * Real.sqrt 2 * R + (2 - y)
        ≤ (x + (x - 1) * Real.sqrt 2 + (2 - y)) * (a + R) := by linarith
    linarith
  /- @proof-region region.target-node.session.db666e2494ed3b90 end -/

end Statlib.Imported

