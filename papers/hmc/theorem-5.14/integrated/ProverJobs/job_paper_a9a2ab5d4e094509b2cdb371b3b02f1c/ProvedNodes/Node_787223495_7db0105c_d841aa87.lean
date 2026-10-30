import ProverJobs.job_paper_a9a2ab5d4e094509b2cdb371b3b02f1c.Vocabulary
import ProverJobs.job_paper_a9a2ab5d4e094509b2cdb371b3b02f1c.Base

namespace PaperProofTasks.job_paper_a9a2ab5d4e094509b2cdb371b3b02f1c

open _root_.PaperProofTasks.job_paper_a9a2ab5d4e094509b2cdb371b3b02f1c.Statlib.Imported
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Statlib.Imported
open _root_.Statlib
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_787223495_7db0105c : ∀ (rho c r : ℝ) (hrho : rho < 1) (hc : 0 ≤ c) (hr : 0 ≤ r)
    (hbound : ∀ n : ℕ, 1 ≤ n → r ^ n ≤ c * rho ^ n),
    r ≤ max rho 0 := by
  /- @proof-region region.target-node.session.e20fdfdb3ce738a7 begin -/
  intro rho c r hrho hc hr hbound
  by_cases hcase : rho ≤ 0
  · rw [max_eq_right hcase]
    have h1 : r ≤ c * rho := by simpa using hbound 1 le_rfl
    have h2 : c * rho ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc hcase
    have hr0 : r = 0 := le_antisymm (h1.trans h2) hr
    linarith
  · have hrp0 : 0 < rho := not_le.mp hcase
    rw [max_eq_left hrp0.le]
    by_contra hcon
    have hcon' : rho < r := not_le.mp hcon
    set t : ℝ := r / rho with ht_def
    have htr : t * rho = r := by
      rw [ht_def]
      exact div_mul_cancel₀ r hrp0.ne'
    have ht_gt_one : 1 < t := by nlinarith [hrp0, htr, hcon']
    have ht_pos : 0 < t := lt_trans zero_lt_one ht_gt_one
    have hbnd : ∀ n : ℕ, 1 ≤ n → t ^ n ≤ c := by
      intro n hn
      have hpow : (0 : ℝ) < rho ^ n := pow_pos hrp0 n
      have htn : t ^ n * rho ^ n = r ^ n := by
        rw [← mul_pow, htr]
      by_contra hlt
      have hclt : c < t ^ n := not_le.mp hlt
      have hlt2 : c * rho ^ n < t ^ n * rho ^ n := mul_lt_mul_of_pos_right hclt hpow
      have hb := hbound n hn
      rw [← htn] at hb
      linarith
    have htend : Tendsto (fun n : ℕ => t ^ n) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt ht_gt_one
    have hev : ∀ᶠ n : ℕ in atTop, c < t ^ n := htend.eventually (eventually_gt_atTop c)
    obtain ⟨k, hk⟩ := hev.exists
    have hstep : t ^ k ≤ t ^ (k + 1) := by
      rw [pow_succ]
      nlinarith [pow_pos ht_pos k, ht_gt_one]
    have hk' : c < t ^ (k + 1) := by linarith
    have hfin := hbnd (k + 1) (by omega)
    linarith
  /- @proof-region region.target-node.session.e20fdfdb3ce738a7 end -/

end
end Statlib.Imported

