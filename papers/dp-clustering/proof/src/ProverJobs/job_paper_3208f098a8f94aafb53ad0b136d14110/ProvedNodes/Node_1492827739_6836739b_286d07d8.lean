import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.Vocabulary
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.Base
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.ProvedNodes.Node_1445702134_3c8d3810_8f7a15fe
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.ProvedNodes.Node_3224678180_5a630a9f_7124eef7


open MeasureTheory
open Statlib.Imported

noncomputable section
open MeasureTheory
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_1492827739_6836739b : ∀ (t eps delta beta : ℝ) (n s : ℕ)
    (ht : 1 ≤ t) (heps : 0 < eps) (heps_lt : eps < 1 / 2)
    (hdelta : 0 < delta) (hbeta : 0 < beta) (hs : 1 ≤ s)
    (hns : (s : ℝ) + t ≤ (n : ℝ)),
    0 < Gconst t eps delta beta * (s : ℝ) / eps ^ s *
      (lowerGamma (t + (s : ℝ) + beta) (eps * Real.log (n : ℝ)) /
        (Real.log ((n : ℝ) / (1 + eps))) ^ s) := by
  /- @proof-region region.target-node.session.9dc6638bcbb70ef0 begin -/
  intro t eps delta beta n s ht heps heps_lt hdelta hbeta hs hns
  have hlg : ∀ x y : ℝ, 0 < x → 0 < y → 0 < lowerGamma x y :=
    statopia_math_node_3224678180_5a630a9f.1
  have hpowpos : 0 < eps ^ (t + beta) := Real.rpow_pos_of_pos heps _
  have htb : 0 < t + beta := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hepslog2 : 0 < eps * Real.log 2 := mul_pos heps hlog2
  have hlg1 : 0 < lowerGamma (t + beta) (eps * Real.log 2) := hlg _ _ htb hepslog2
  have h4d : 0 < 4 * delta ^ 2 := mul_pos (by norm_num) (pow_pos hdelta 2)
  have hG : 0 < Gconst t eps delta beta := by
    unfold Gconst
    exact div_pos h4d (mul_pos hpowpos hlg1)
  have hs1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hspos : (0 : ℝ) < (s : ℝ) := by linarith
  have hepss : 0 < eps ^ s := pow_pos heps s
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by linarith
  have hn1 : (1 : ℝ) < (n : ℝ) := by linarith
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  have hepslogn : 0 < eps * Real.log (n : ℝ) := mul_pos heps hlogn
  have htsb : 0 < t + (s : ℝ) + beta := by linarith
  have hlg2 : 0 < lowerGamma (t + (s : ℝ) + beta) (eps * Real.log (n : ℝ)) :=
    hlg _ _ htsb hepslogn
  have h1eps : (0 : ℝ) < 1 + eps := by linarith
  have hnum : (0 : ℝ) < (n : ℝ) - (1 + eps) := by linarith
  have heq : (n : ℝ) / (1 + eps) - 1 = ((n : ℝ) - (1 + eps)) / (1 + eps) := by
    field_simp
  have hratio : (1 : ℝ) < (n : ℝ) / (1 + eps) := by
    have hpos : (0 : ℝ) < (n : ℝ) / (1 + eps) - 1 := by
      rw [heq]
      exact div_pos hnum h1eps
    linarith
  have hlogratio : 0 < Real.log ((n : ℝ) / (1 + eps)) := Real.log_pos hratio
  have hlogpow : 0 < (Real.log ((n : ℝ) / (1 + eps))) ^ s := pow_pos hlogratio s
  exact mul_pos (div_pos (mul_pos hG hspos) hepss) (div_pos hlg2 hlogpow)
  /- @proof-region region.target-node.session.9dc6638bcbb70ef0 end -/

end Statlib.Imported
end
