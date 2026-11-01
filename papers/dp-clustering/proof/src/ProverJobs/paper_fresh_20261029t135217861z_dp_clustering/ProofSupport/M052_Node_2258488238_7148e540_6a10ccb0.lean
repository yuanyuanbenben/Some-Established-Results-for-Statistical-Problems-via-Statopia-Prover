import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.Definitions
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M031_Vocabulary
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M032_Base

/- Original module ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.ProvedNodes.Node_2258488238_7148e540_6a10ccb0; genuine source relocated, namespace-isolated only. -/
namespace DPCompletedProof
open _root_.Statlib.Imported

open MeasureTheory
open Statlib.Imported

noncomputable section
open MeasureTheory
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_2258488238_7148e540 : ∀ (t : ℝ) (ht : 1 ≤ t) (eps0 delta beta : ℝ)
    (heps0 : 0 < eps0) (hdelta : 0 < delta) (hbeta : 0 < beta),
    ∃ eps : ℝ, 0 < eps ∧ eps < 1 / 2 ∧ eps ≤ eps0 ∧
      delta * eps ^ (beta + 1) / (beta + 1) ≤ 1 / 2 ∧
      2 * delta ^ 2 * (Real.exp 1)⁻¹ * (t + beta) / (t + 1 + beta) *
          eps ^ (-(beta + 1)) ≥ 2 ∧
      2 * delta ^ 2 * (Real.exp 1)⁻¹ * (t + beta) /
          ((t + 1 + beta) * (Real.log 2) ^ (t + beta)) *
          eps ^ (-(t + 2 * beta + 1)) ≥ 2 := by
  /- @proof-region region.target-node.session.8b727227d0925bd3 begin -/
  intro t ht eps0 delta beta heps0 hdelta hbeta
  have hb1 : (0 : ℝ) < beta + 1 := by linarith
  have htb : (0 : ℝ) < t + beta := by linarith
  have hd1 : (0 : ℝ) < t + 1 + beta := by linarith
  have hd3 : (0 : ℝ) < t + 2 * beta + 1 := by linarith
  have he : (0 : ℝ) < Real.exp (-1) := Real.exp_pos (-1)
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hl2p : (0 : ℝ) < (Real.log 2) ^ (t + beta) := Real.rpow_pos_of_pos hl2 _
  set A : ℝ := (beta + 1) / (2 * delta) with hA
  set B : ℝ := delta ^ 2 * Real.exp (-1) * (t + beta) / (t + 1 + beta) with hB
  set C : ℝ := delta ^ 2 * Real.exp (-1) * (t + beta) / ((t + 1 + beta) * (Real.log 2) ^ (t + beta)) with hC
  have hApos : 0 < A := by rw [hA]; exact div_pos hb1 (by linarith)
  have hBpos : 0 < B := by rw [hB]; exact div_pos (mul_pos (mul_pos (pow_pos hdelta 2) he) htb) hd1
  have hCpos : 0 < C := by rw [hC]; exact div_pos (mul_pos (mul_pos (pow_pos hdelta 2) he) htb) (mul_pos hd1 hl2p)
  set e1 : ℝ := A ^ ((beta + 1)⁻¹) with he1
  set e2 : ℝ := B ^ ((beta + 1)⁻¹) with he2
  set e3 : ℝ := C ^ ((t + 2 * beta + 1)⁻¹) with he3
  have he1pos : 0 < e1 := by rw [he1]; exact Real.rpow_pos_of_pos hApos _
  have he2pos : 0 < e2 := by rw [he2]; exact Real.rpow_pos_of_pos hBpos _
  have he3pos : 0 < e3 := by rw [he3]; exact Real.rpow_pos_of_pos hCpos _
  set m : ℝ := min (min eps0 e1) (min e2 (min e3 (1 / 2))) with hm
  have hmpos : 0 < m := by
    rw [hm]
    exact lt_min (lt_min heps0 he1pos) (lt_min he2pos (lt_min he3pos (by norm_num)))
  have hm0 : m ≤ eps0 := by rw [hm]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hm1 : m ≤ e1 := by rw [hm]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hm2 : m ≤ e2 := by rw [hm]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hm3 : m ≤ e3 := by rw [hm]; exact le_trans (le_trans (min_le_right _ _) (min_le_right _ _)) (min_le_left _ _)
  have hmh : m ≤ 1 / 2 := by rw [hm]; exact le_trans (le_trans (min_le_right _ _) (min_le_right _ _)) (min_le_right _ _)
  set eps : ℝ := m / 2 with heps
  have hepspos : 0 < eps := by rw [heps]; exact div_pos hmpos (by norm_num)
  have hepsltm : eps < m := by rw [heps]; exact half_lt_self hmpos
  have heps_le_eps0 : eps ≤ eps0 := le_of_lt (lt_of_lt_of_le hepsltm hm0)
  have heps_lt_half : eps < 1 / 2 := lt_of_lt_of_le hepsltm hmh
  have heps_le_e1 : eps ≤ e1 := le_of_lt (lt_of_lt_of_le hepsltm hm1)
  have heps_le_e2 : eps ≤ e2 := le_of_lt (lt_of_lt_of_le hepsltm hm2)
  have heps_le_e3 : eps ≤ e3 := le_of_lt (lt_of_lt_of_le hepsltm hm3)
  have he1val : e1 ^ (beta + 1) = A := by rw [he1]; exact Real.rpow_inv_rpow (le_of_lt hApos) (ne_of_gt hb1)
  have he2val : e2 ^ (beta + 1) = B := by rw [he2]; exact Real.rpow_inv_rpow (le_of_lt hBpos) (ne_of_gt hb1)
  have he3val : e3 ^ (t + 2 * beta + 1) = C := by rw [he3]; exact Real.rpow_inv_rpow (le_of_lt hCpos) (ne_of_gt hd3)
  have heps1 : eps ^ (beta + 1) ≤ A := by
    have h := Real.rpow_le_rpow (le_of_lt hepspos) heps_le_e1 (le_of_lt hb1)
    rwa [he1val] at h
  have heps2 : eps ^ (beta + 1) ≤ B := by
    have h := Real.rpow_le_rpow (le_of_lt hepspos) heps_le_e2 (le_of_lt hb1)
    rwa [he2val] at h
  have heps3 : eps ^ (t + 2 * beta + 1) ≤ C := by
    have h := Real.rpow_le_rpow (le_of_lt hepspos) heps_le_e3 (le_of_lt hd3)
    rwa [he3val] at h
  refine ⟨eps, hepspos, heps_lt_half, heps_le_eps0, ?_, ?_, ?_⟩
  · rw [hA] at heps1
    have key : eps ^ (beta + 1) * (2 * delta) ≤ beta + 1 :=
      (le_div_iff₀ (by linarith : (0 : ℝ) < 2 * delta)).mp heps1
    rw [div_le_iff₀ hb1]
    nlinarith [key]
  · have hBform : 2 * B = 2 * delta ^ 2 * (Real.exp 1)⁻¹ * (t + beta) / (t + 1 + beta) := by
      rw [hB, Real.exp_neg]; ring
    have hinv : B⁻¹ ≤ eps ^ (-(beta + 1)) := by
      rw [Real.rpow_neg (le_of_lt hepspos)]
      exact inv_anti₀ (Real.rpow_pos_of_pos hepspos (beta + 1)) heps2
    have h2B : 2 * B * B⁻¹ = 2 := by
      rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hBpos), mul_one]
    have hle : 2 * B * B⁻¹ ≤ 2 * B * eps ^ (-(beta + 1)) :=
      mul_le_mul_of_nonneg_left hinv (by linarith [hBpos] : (0 : ℝ) ≤ 2 * B)
    have hge : (2 : ℝ) ≤ 2 * B * eps ^ (-(beta + 1)) := by
      linarith [hle, h2B]
    rw [← hBform]
    exact hge
  · have hCform : 2 * C = 2 * delta ^ 2 * (Real.exp 1)⁻¹ * (t + beta) / ((t + 1 + beta) * (Real.log 2) ^ (t + beta)) := by
      rw [hC, Real.exp_neg]; ring
    have hinv : C⁻¹ ≤ eps ^ (-(t + 2 * beta + 1)) := by
      rw [Real.rpow_neg (le_of_lt hepspos)]
      exact inv_anti₀ (Real.rpow_pos_of_pos hepspos (t + 2 * beta + 1)) heps3
    have h2C : 2 * C * C⁻¹ = 2 := by
      rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hCpos), mul_one]
    have hle : 2 * C * C⁻¹ ≤ 2 * C * eps ^ (-(t + 2 * beta + 1)) :=
      mul_le_mul_of_nonneg_left hinv (by linarith [hCpos] : (0 : ℝ) ≤ 2 * C)
    have hge : (2 : ℝ) ≤ 2 * C * eps ^ (-(t + 2 * beta + 1)) := by
      linarith [hle, h2C]
    rw [← hCform]
    exact hge
  /- @proof-region region.target-node.session.8b727227d0925bd3 end -/

end Statlib.Imported
end
end DPCompletedProof
