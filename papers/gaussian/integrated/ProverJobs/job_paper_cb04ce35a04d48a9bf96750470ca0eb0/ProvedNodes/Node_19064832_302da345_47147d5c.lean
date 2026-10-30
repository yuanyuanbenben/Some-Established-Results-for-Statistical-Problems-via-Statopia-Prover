import ProverJobs.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.Vocabulary
import ProverJobs.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.Base

namespace PaperProofTasks.job_paper_cb04ce35a04d48a9bf96750470ca0eb0

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal
open _root_.PaperProofTasks.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.Statlib.Imported

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal
namespace Statlib.Imported
open _root_.Statlib
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_19064832_302da345 : ∀ (C1 C2 c_Sn C3 qn : ℝ) (k : ℕ → ℕ) (beta : ℕ → ℝ) (n : ℕ)
    (hC1 : (1 : ℝ) ≤ C1)
    (hc_Sn : 0 < c_Sn)
    (hC2 : (1 : ℝ) ≤ C2)
    (hC1cSn : 2 * C1 * c_Sn ≤ C2)
    (hC3 : (8 : ℝ) ≤ C3)
    (hk1 : 1 ≤ k n)
    (hlogn : (0 : ℝ) < Real.log (n : ℝ))
    (hsqrtsq : (3 : ℝ) ≤ Real.sqrt (n : ℝ))
    (hq2 : 2 ≤ qn)
    (hqC3log : qn ≤ C3 * Real.log (n : ℝ))
    (hqlog : Real.log (n : ℝ) + 4 ≤ qn)
    (hbeta_pos : 0 < beta n)
    (hqbeta2 : 2 ≤ qn * beta n)
    (hkexp : (k n : ℝ) ≤ Real.exp 2 * Real.sqrt (n : ℝ)),
    Real.rpow C1 qn * Real.rpow (k n : ℝ) (1 - qn * beta n) * (c_Sn * qn) ^ qn
        / (Real.exp 1 * C2 * C3 *
            (Real.rpow (k n : ℝ) (-(beta n)) * Real.log (n : ℝ))) ^ qn
      ≤ C2 * Real.rpow (n : ℝ) (-1) := by
  /- @proof-region region.target-node.session.0eddba7740873759 begin -/
  intro C1 C2 c_Sn C3 qn k beta n hC1 hc_Sn hC2 hC1cSn hC3 hk1 hlogn hsqrtsq hq2 hqC3log hqlog
    hbeta_pos hqbeta2 hkexp
  have hL : (0 : ℝ) < Real.log (n : ℝ) := hlogn
  have hq0 : (0 : ℝ) < qn := by linarith
  have hkn1 : (1 : ℝ) ≤ (k n : ℝ) := by exact_mod_cast hk1
  have hkn0 : (0 : ℝ) < (k n : ℝ) := by linarith
  have hC1pos : (0 : ℝ) < C1 := by linarith
  have hC2pos : (0 : ℝ) < C2 := by linarith
  have hC3pos : (0 : ℝ) < C3 := by linarith
  have hcqpos : (0 : ℝ) < c_Sn * qn := by positivity
  have hEpos : (0 : ℝ) < Real.exp 1 * C2 * C3 := by positivity
  have hkbp : (0 : ℝ) < Real.rpow (k n : ℝ) (-(beta n)) := Real.rpow_pos_of_pos hkn0 _
  have hDpos : (0 : ℝ) < Real.rpow (k n : ℝ) (-(beta n)) * Real.log (n : ℝ) := by positivity
  have hnp : (0 : ℝ) < (n : ℝ) := Real.sqrt_pos.mp (by linarith)
  have hratio :
      C1 * (c_Sn * qn) / (Real.exp 1 * C2 * C3 * Real.log (n : ℝ)) ≤ 1 / (2 * Real.exp 1) := by
    have hexp1pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    have hcross : 2 * C1 * c_Sn * qn ≤ C2 * C3 * Real.log (n : ℝ) := by
      have h1 : 2 * C1 * c_Sn * qn ≤ C2 * qn := by nlinarith [hC1cSn, hq0]
      have h2 : C2 * qn ≤ C2 * C3 * Real.log (n : ℝ) := by nlinarith [hqC3log, hC2pos]
      linarith
    have heq :
        1 / (2 * Real.exp 1) - C1 * (c_Sn * qn) / (Real.exp 1 * C2 * C3 * Real.log (n : ℝ))
          = (Real.exp 1 * C2 * C3 * Real.log (n : ℝ) - 2 * Real.exp 1 * (C1 * (c_Sn * qn)))
              / (2 * Real.exp 1 * (Real.exp 1 * C2 * C3 * Real.log (n : ℝ))) := by
      have h1 : Real.exp 1 ≠ 0 := ne_of_gt hexp1pos
      have h2 : C2 ≠ 0 := ne_of_gt hC2pos
      have h3 : C3 ≠ 0 := ne_of_gt hC3pos
      have h4 : Real.log (n : ℝ) ≠ 0 := ne_of_gt hL
      field_simp
    have hnum :
        (0 : ℝ) ≤ Real.exp 1 * C2 * C3 * Real.log (n : ℝ) - 2 * Real.exp 1 * (C1 * (c_Sn * qn)) := by
      have hstep : (0 : ℝ) ≤ Real.exp 1 * (C2 * C3 * Real.log (n : ℝ) - 2 * C1 * c_Sn * qn) :=
        mul_nonneg hexp1pos.le (by linarith [hcross])
      nlinarith [hstep]
    have hden : (0 : ℝ) ≤ 2 * Real.exp 1 * (Real.exp 1 * C2 * C3 * Real.log (n : ℝ)) := by
      positivity
    rw [← sub_nonneg]
    rw [heq]
    exact div_nonneg hnum hden
  have key :
      Real.rpow C1 qn * Real.rpow (k n : ℝ) (1 - qn * beta n) * (c_Sn * qn) ^ qn
          / (Real.exp 1 * C2 * C3 *
              (Real.rpow (k n : ℝ) (-(beta n)) * Real.log (n : ℝ))) ^ qn
        = (C1 * (c_Sn * qn) / (Real.exp 1 * C2 * C3 * Real.log (n : ℝ))) ^ qn * (k n : ℝ) := by
    have hkn_eq : Real.rpow (k n : ℝ) (1 - qn * beta n)
        = (k n : ℝ) * Real.rpow (k n : ℝ) (-(qn * beta n)) := by
      have h := Real.rpow_add hkn0 1 (-(qn * beta n))
      rw [Real.rpow_one] at h
      rw [show (1 : ℝ) - qn * beta n = 1 + -(qn * beta n) by ring]
      exact h
    have hpow_mul : (Real.rpow (k n : ℝ) (-(beta n))) ^ qn
        = Real.rpow (k n : ℝ) (-(qn * beta n)) := by
      have h := Real.rpow_mul hkn0.le (-(beta n)) qn
      rw [show -(beta n) * qn = -(qn * beta n) by ring] at h
      exact h.symm
    have hnum_eq : Real.rpow C1 qn * (c_Sn * qn) ^ qn = (C1 * (c_Sn * qn)) ^ qn :=
      (Real.mul_rpow hC1pos.le hcqpos.le).symm
    have hden_eq :
        (Real.exp 1 * C2 * C3 * (Real.rpow (k n : ℝ) (-(beta n)) * Real.log (n : ℝ))) ^ qn
          = (Real.exp 1 * C2 * C3) ^ qn *
              (Real.rpow (k n : ℝ) (-(qn * beta n)) * (Real.log (n : ℝ)) ^ qn) := by
      rw [Real.mul_rpow hEpos.le hDpos.le, Real.mul_rpow hkbp.le hL.le, hpow_mul]
    have hRHS :
        (C1 * (c_Sn * qn) / (Real.exp 1 * C2 * C3 * Real.log (n : ℝ))) ^ qn
          = (C1 * (c_Sn * qn)) ^ qn /
              ((Real.exp 1 * C2 * C3) ^ qn * (Real.log (n : ℝ)) ^ qn) := by
      rw [Real.div_rpow (by positivity) (by positivity), Real.mul_rpow hEpos.le hL.le]
    rw [hRHS, hden_eq, hkn_eq]
    have hnum2 :
        Real.rpow C1 qn * ((k n : ℝ) * Real.rpow (k n : ℝ) (-(qn * beta n))) * (c_Sn * qn) ^ qn
          = (Real.rpow C1 qn * (c_Sn * qn) ^ qn) *
              ((k n : ℝ) * Real.rpow (k n : ℝ) (-(qn * beta n))) := by ring
    rw [hnum2, hnum_eq]
    have hF : (Real.exp 1 * C2 * C3) ^ qn ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos hEpos qn)
    have hH : (Real.log (n : ℝ)) ^ qn ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hL qn)
    have hG : Real.rpow (k n : ℝ) (-(qn * beta n)) ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos hkn0 _)
    have hFH : (Real.exp 1 * C2 * C3) ^ qn * (Real.log (n : ℝ)) ^ qn ≠ 0 := by positivity
    have hFGH :
        (Real.exp 1 * C2 * C3) ^ qn *
            (Real.rpow (k n : ℝ) (-(qn * beta n)) * (Real.log (n : ℝ)) ^ qn) ≠ 0 := by
      positivity
    field_simp
    try ring
  rw [key]
  have hbase_nonneg :
      (0 : ℝ) ≤ C1 * (c_Sn * qn) / (Real.exp 1 * C2 * C3 * Real.log (n : ℝ)) := by positivity
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
    have h := Real.log_two_gt_d9
    linarith
  have hlogC2 : (0 : ℝ) ≤ Real.log C2 := Real.log_nonneg hC2
  have hbase1 :
      (1 / (2 * Real.exp 1)) ^ qn = Real.exp (-(qn * (1 + Real.log 2))) := by
    have hlogbase : Real.log (1 / (2 * Real.exp 1)) = -(1 + Real.log 2) := by
      rw [Real.log_div (by norm_num) (by positivity)]
      rw [Real.log_one]
      rw [Real.log_mul (by norm_num) (ne_of_gt (Real.exp_pos 1))]
      rw [Real.log_exp]
      ring
    rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.exp 1)), hlogbase]
    congr 1
    ring
  have hsqrt : Real.sqrt (n : ℝ) = Real.exp (Real.log (n : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hnp]
    congr 1
    ring
  have hknb : (k n : ℝ) ≤ Real.exp (2 + Real.log (n : ℝ) / 2) := by
    have h := hkexp
    rw [hsqrt] at h
    rw [← Real.exp_add] at h
    exact h
  have hexp_bound :
      -(qn * (1 + Real.log 2)) + (2 + Real.log (n : ℝ) / 2)
        ≤ Real.log C2 - Real.log (n : ℝ) := by
    nlinarith [hqlog, hlog2, hL, hlogC2]
  calc (C1 * (c_Sn * qn) / (Real.exp 1 * C2 * C3 * Real.log (n : ℝ))) ^ qn * (k n : ℝ)
      ≤ (1 / (2 * Real.exp 1)) ^ qn * (k n : ℝ) := by
        have h := Real.rpow_le_rpow hbase_nonneg hratio (le_of_lt hq0)
        exact mul_le_mul_of_nonneg_right h (by positivity)
    _ ≤ Real.exp (-(qn * (1 + Real.log 2))) * Real.exp (2 + Real.log (n : ℝ) / 2) := by
        rw [hbase1]
        exact mul_le_mul_of_nonneg_left hknb (by positivity)
    _ = Real.exp (-(qn * (1 + Real.log 2)) + (2 + Real.log (n : ℝ) / 2)) :=
        (Real.exp_add _ _).symm
    _ ≤ Real.exp (Real.log C2 - Real.log (n : ℝ)) := Real.exp_le_exp_of_le hexp_bound
    _ = C2 * Real.rpow (n : ℝ) (-1) := by
        have h2 : Real.rpow (n : ℝ) (-1) = ((n : ℝ))⁻¹ := Real.rpow_neg_one (n : ℝ)
        rw [Real.exp_sub, Real.exp_log hC2pos, Real.exp_log hnp, h2, div_eq_mul_inv]
  /- @proof-region region.target-node.session.0eddba7740873759 end -/

end

end Statlib.Imported

