import ProverJobs.job_paper_df5fdc450bf24d85b08215e07b20fdad.Vocabulary
import ProverJobs.job_paper_df5fdc450bf24d85b08215e07b20fdad.Base

namespace PaperProofTasks.job_paper_df5fdc450bf24d85b08215e07b20fdad

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology BigOperators
open _root_.PaperProofTasks.job_paper_df5fdc450bf24d85b08215e07b20fdad.Statlib.Imported

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology BigOperators
namespace Statlib.Imported
open _root_.Statlib

set_option autoImplicit false in
theorem statopia_math_node_3045670844_0a1a6b78 : ∀ (n : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hq2 : 2 ≤ q) (hq : q ≤ Real.sqrt (n : ℝ)),
    (q / max (Real.log q) 1) * (n : ℝ) ^ (-(1 / 2 : ℝ) + 1 / q) ≤ 3 := by
  /- @proof-region region.target-node.session.35662e256e5a3131 begin -/
  intro n q hn hq hqn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hqpos : (0 : ℝ) < q := by linarith
  have hq2le : q ^ 2 ≤ (n : ℝ) := by
    have hs : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (le_of_lt hnpos)
    have hsnn : (0 : ℝ) ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
    nlinarith
  have hE : -(1 / 2 : ℝ) + 1 / q ≤ 0 := by
    have h : (1 : ℝ) / q ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hq
    linarith
  have hq2pos : (0 : ℝ) < q ^ 2 := by nlinarith
  have step1 : (n : ℝ) ^ (-(1 / 2 : ℝ) + 1 / q) ≤ (q ^ 2) ^ (-(1 / 2 : ℝ) + 1 / q) :=
    Real.rpow_le_rpow_of_nonpos hq2pos hq2le hE
  have hq2eq : (q ^ 2 : ℝ) ^ (-(1 / 2 : ℝ) + 1 / q) = q ^ (-1 + 2 / q) := by
    rw [← Real.rpow_natCast_mul (le_of_lt hqpos) 2 (-(1 / 2 : ℝ) + 1 / q)]
    refine congrArg (fun r => q ^ r) ?_
    push_cast
    ring
  have step2 : (n : ℝ) ^ (-(1 / 2 : ℝ) + 1 / q) ≤ q ^ (-1 + 2 / q) :=
    le_trans step1 (le_of_eq hq2eq)
  have hMpos : (0 : ℝ) < max (Real.log q) 1 := by
    have h : (1 : ℝ) ≤ max (Real.log q) 1 := le_max_right _ _
    linarith
  have hfac : q / max (Real.log q) 1 ≤ q := by
    rw [div_le_iff₀ hMpos]
    have hprod : (0 : ℝ) ≤ q * (max (Real.log q) 1 - 1) :=
      mul_nonneg (le_of_lt hqpos) (by linarith [le_max_right (Real.log q) (1 : ℝ)])
    nlinarith
  have step3 : (q / max (Real.log q) 1) * (n : ℝ) ^ (-(1 / 2 : ℝ) + 1 / q)
      ≤ q * (n : ℝ) ^ (-(1 / 2 : ℝ) + 1 / q) :=
    mul_le_mul_of_nonneg_right hfac (Real.rpow_nonneg (le_of_lt hnpos) _)
  have step4 : q * (n : ℝ) ^ (-(1 / 2 : ℝ) + 1 / q) ≤ q * q ^ (-1 + 2 / q) :=
    mul_le_mul_of_nonneg_left step2 (le_of_lt hqpos)
  have hlog : Real.log q ≤ q / 2 := by
    have hsqpos : (0 : ℝ) < Real.sqrt q := Real.sqrt_pos.mpr hqpos
    have hlogsqrt : Real.log (Real.sqrt q) = Real.log q / 2 := Real.log_sqrt (le_of_lt hqpos)
    have h1 : Real.log (Real.sqrt q) ≤ Real.sqrt q - 1 := Real.log_le_sub_one_of_pos hsqpos
    have hsq : Real.sqrt q ^ 2 = q := Real.sq_sqrt (le_of_lt hqpos)
    have h2 : 2 * Real.sqrt q - 2 ≤ q / 2 := by
      nlinarith [sq_nonneg (Real.sqrt q - 2)]
    linarith
  have hqne : q ≠ 0 := ne_of_gt hqpos
  have harg : Real.log q * (2 / q) ≤ 1 := by
    have h2 : (0 : ℝ) ≤ 2 / q := div_nonneg (by norm_num) (le_of_lt hqpos)
    have hmul : Real.log q * (2 / q) ≤ (q / 2) * (2 / q) :=
      mul_le_mul_of_nonneg_right hlog h2
    have hone : (q / 2) * (2 / q) = 1 := by
      field_simp
    linarith
  have hq23 : q ^ (2 / q) ≤ 3 := by
    rw [Real.rpow_def_of_pos hqpos (2 / q)]
    calc Real.exp (Real.log q * (2 / q)) ≤ Real.exp 1 := Real.exp_le_exp.mpr harg
      _ ≤ 3 := le_of_lt Real.exp_one_lt_three
  have hqadd : q * q ^ (-1 + 2 / q) = q ^ (2 / q) := by
    have h := Real.rpow_add hqpos (1 : ℝ) (-1 + 2 / q)
    rw [Real.rpow_one] at h
    have h1 : (1 : ℝ) + (-1 + 2 / q) = 2 / q := by ring
    rw [h1] at h
    exact h.symm
  calc (q / max (Real.log q) 1) * (n : ℝ) ^ (-(1 / 2 : ℝ) + 1 / q)
      ≤ q * (n : ℝ) ^ (-(1 / 2 : ℝ) + 1 / q) := step3
    _ ≤ q * q ^ (-1 + 2 / q) := step4
    _ = q ^ (2 / q) := hqadd
    _ ≤ 3 := hq23
  /- @proof-region region.target-node.session.35662e256e5a3131 end -/

end Statlib.Imported

