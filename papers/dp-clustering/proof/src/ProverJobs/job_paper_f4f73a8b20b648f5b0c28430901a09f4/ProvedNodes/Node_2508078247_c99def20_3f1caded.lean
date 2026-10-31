import ProverJobs.job_paper_f4f73a8b20b648f5b0c28430901a09f4.Vocabulary
import ProverJobs.job_paper_f4f73a8b20b648f5b0c28430901a09f4.Base

open MeasureTheory
open scoped BigOperators
open Classical
open Statlib.Imported

open MeasureTheory
open scoped BigOperators
open Classical
noncomputable section
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_2508078247_c99def20 : ∀ (t n : ℕ) (hn : 0 < n) (X : Fin n → ℝ) (g q0 : ℝ → ℝ) (θstarj c : ℝ)
    (K : ℝ) (hK : 0 < K) (Nj : ℕ) (hNj : 1 ≤ Nj)
    (hN : Nj ≤ paperNcard X θstarj c)
    (hY : paperY t X θstarj c ∈ Set.Icc (1 / 2 : ℝ) 1)
    (hden :
      K ^ ((1 : ℝ) / (t : ℝ)) * paperY t X θstarj c ≤
        (paperNcard X θstarj c : ℝ) * (Real.log (n : ℝ)) ^ ((1 : ℝ) / (2 * (t : ℝ))) *
          paperBlockIntegralT g q0 X θstarj (paperCblock X θstarj c)),
    0 < paperBlockIntegralT g q0 X θstarj (paperCblock X θstarj c) ∧
      (paperBlockIntegralT g q0 X θstarj (paperCblock X θstarj c))⁻¹ ≤
        2 * (paperNcard X θstarj c : ℝ) * (Real.log (n : ℝ)) ^ ((1 : ℝ) / (2 * (t : ℝ))) /
          K ^ ((1 : ℝ) / (t : ℝ)) := by
  /- @proof-region region.target-node.session.92cbcf814451c12d begin -/
  intro t n hn X g q0 θstarj c K hK Nj hNj hN hY hden
  obtain ⟨hY1, hY2⟩ := hY
  have hKp : (0 : ℝ) < K ^ ((1 : ℝ) / (t : ℝ)) := Real.rpow_pos_of_pos hK _
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    have h1 : (1 : ℕ) ≤ n := Nat.succ_le_of_lt hn
    exact_mod_cast h1
  have hlog : (0 : ℝ) ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hLnn : (0 : ℝ) ≤ (Real.log (n : ℝ)) ^ ((1 : ℝ) / (2 * (t : ℝ))) :=
    Real.rpow_nonneg hlog _
  have hYpos : (0 : ℝ) < paperY t X θstarj c := by linarith
  have hnjn : (0 : ℝ) < (paperNcard X θstarj c : ℝ) := by
    have h1 : (1 : ℝ) ≤ (paperNcard X θstarj c : ℝ) := by
      exact_mod_cast le_trans hNj hN
    linarith
  have hnjL : (0 : ℝ) ≤
      (paperNcard X θstarj c : ℝ) * (Real.log (n : ℝ)) ^ ((1 : ℝ) / (2 * (t : ℝ))) :=
    mul_nonneg (le_of_lt hnjn) hLnn
  have hLHS : (0 : ℝ) < K ^ ((1 : ℝ) / (t : ℝ)) * paperY t X θstarj c :=
    mul_pos hKp hYpos
  have hprod : (0 : ℝ) <
      (paperNcard X θstarj c : ℝ) * (Real.log (n : ℝ)) ^ ((1 : ℝ) / (2 * (t : ℝ))) *
        paperBlockIntegralT g q0 X θstarj (paperCblock X θstarj c) :=
    lt_of_lt_of_le hLHS hden
  have hJpos : (0 : ℝ) < paperBlockIntegralT g q0 X θstarj (paperCblock X θstarj c) := by
    by_contra hcon
    push_neg at hcon
    have hle : (paperNcard X θstarj c : ℝ) * (Real.log (n : ℝ)) ^ ((1 : ℝ) / (2 * (t : ℝ))) *
        paperBlockIntegralT g q0 X θstarj (paperCblock X θstarj c) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hnjL hcon
    linarith
  refine ⟨hJpos, ?_⟩
  have hstep : K ^ ((1 : ℝ) / (t : ℝ)) * (1 / 2) ≤
      (paperNcard X θstarj c : ℝ) * (Real.log (n : ℝ)) ^ ((1 : ℝ) / (2 * (t : ℝ))) *
        paperBlockIntegralT g q0 X θstarj (paperCblock X θstarj c) :=
    le_trans (mul_le_mul_of_nonneg_left hY1 (le_of_lt hKp)) hden
  have key : K ^ ((1 : ℝ) / (t : ℝ)) ≤
      2 * (paperNcard X θstarj c : ℝ) * (Real.log (n : ℝ)) ^ ((1 : ℝ) / (2 * (t : ℝ))) *
        paperBlockIntegralT g q0 X θstarj (paperCblock X θstarj c) := by
    linarith
  rw [le_div_iff₀ hKp]
  have hmul : (paperBlockIntegralT g q0 X θstarj (paperCblock X θstarj c))⁻¹ *
        K ^ ((1 : ℝ) / (t : ℝ)) ≤
      (paperBlockIntegralT g q0 X θstarj (paperCblock X θstarj c))⁻¹ *
        (2 * (paperNcard X θstarj c : ℝ) * (Real.log (n : ℝ)) ^ ((1 : ℝ) / (2 * (t : ℝ))) *
          paperBlockIntegralT g q0 X θstarj (paperCblock X θstarj c)) :=
    mul_le_mul_of_nonneg_left key (le_of_lt (inv_pos.mpr hJpos))
  have hcalc : (paperBlockIntegralT g q0 X θstarj (paperCblock X θstarj c))⁻¹ *
        (2 * (paperNcard X θstarj c : ℝ) * (Real.log (n : ℝ)) ^ ((1 : ℝ) / (2 * (t : ℝ))) *
          paperBlockIntegralT g q0 X θstarj (paperCblock X θstarj c)) =
      2 * (paperNcard X θstarj c : ℝ) * (Real.log (n : ℝ)) ^ ((1 : ℝ) / (2 * (t : ℝ))) := by
    rw [mul_comm ((paperBlockIntegralT g q0 X θstarj (paperCblock X θstarj c))⁻¹), mul_assoc,
      mul_inv_cancel₀ (ne_of_gt hJpos), mul_one]
  rw [← hcalc]
  exact hmul
  /- @proof-region region.target-node.session.92cbcf814451c12d end -/

end Statlib.Imported
end
