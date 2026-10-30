import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q04.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q04.Base

open MeasureTheory ProbabilityTheory
open Msc62GroundTruth

open MeasureTheory ProbabilityTheory
namespace Msc62GroundTruth

set_option autoImplicit false in
theorem statopia_math_node_570887230_87c93162 : ∀ (m n : ℕ) (hm : 1 ≤ m)
    (X : Fin m → Fin n → ℝ)
    (sigmaHat : Matrix (Fin n) (Fin n) ℝ)
    (hSigmaHat : ∀ j k : Fin n,
      sigmaHat j k = (1 / (m : ℝ)) * ∑ i : Fin m, X i j * X i k)
    (Lambda B : ℝ)
    (hscale : (m : ℝ) * Lambda ≤ B ^ 2)
    (hUpper : ∀ v : Fin n → ℝ,
      (∑ j : Fin n, ∑ k : Fin n, v j * sigmaHat j k * v k) ≤
        Lambda * ∑ j : Fin n, (v j) ^ 2),
    ∀ j : Fin n,
      (∑ i : Fin m, (X i j) ^ 2 ≤ (m : ℝ) * Lambda) ∧
        (∑ i : Fin m, (X i j) ^ 2 ≤ B ^ 2) := by
  /- @proof-region region.target-node.session.a8b96b4922487205 begin -/
  intro m n hm X sigmaHat hSigmaHat Lambda B hscale hUpper j
  set v : Fin n → ℝ := fun k => if k = j then 1 else 0 with hv
  have hvj : v j = 1 := by simp [hv]
  have hsum_sq : (∑ k : Fin n, (v k) ^ 2) = 1 := by
    have h : (∑ k : Fin n, (v k) ^ 2) = (v j) ^ 2 :=
      Finset.sum_eq_single (a := j)
        (fun k _ hk => by simp [hv, hk])
        (fun hmem => absurd (Finset.mem_univ j) hmem)
    rw [h, hvj]
    norm_num
  have hLHS : (∑ a : Fin n, ∑ k : Fin n, v a * sigmaHat a k * v k) = sigmaHat j j := by
    have houter : (∑ a : Fin n, ∑ k : Fin n, v a * sigmaHat a k * v k)
        = ∑ k : Fin n, v j * sigmaHat j k * v k :=
      Finset.sum_eq_single (a := j)
        (fun a _ ha => by
          have hva : v a = 0 := by simp [hv, ha]
          exact Finset.sum_eq_zero (fun k _ => by simp [hva]))
        (fun hmem => absurd (Finset.mem_univ j) hmem)
    have hinner : (∑ k : Fin n, v j * sigmaHat j k * v k) = sigmaHat j j := by
      have h : (∑ k : Fin n, v j * sigmaHat j k * v k) = v j * sigmaHat j j * v j :=
        Finset.sum_eq_single (a := j)
          (fun k _ hk => by simp [hv, hk])
          (fun hmem => absurd (Finset.mem_univ j) hmem)
      rw [h, hvj]
      ring
    rw [houter, hinner]
  have hjj : sigmaHat j j ≤ Lambda := by
    have h := hUpper v
    rw [hLHS, hsum_sq] at h
    simpa using h
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hentry : sigmaHat j j = (1 / (m : ℝ)) * ∑ i : Fin m, (X i j) ^ 2 := by
    rw [hSigmaHat j j]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hmain : (∑ i : Fin m, (X i j) ^ 2) ≤ (m : ℝ) * Lambda := by
    have h1 : (1 / (m : ℝ)) * (∑ i : Fin m, (X i j) ^ 2) ≤ Lambda := by
      rw [← hentry]
      exact hjj
    have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt hmpos)
    have hmul : (m : ℝ) * (1 / (m : ℝ)) = 1 := by
      have h : (m : ℝ) * (1 / (m : ℝ)) = (m : ℝ) / (m : ℝ) := by ring
      rw [h, div_self (ne_of_gt hmpos)]
    have h3 : (m : ℝ) * ((1 / (m : ℝ)) * (∑ i : Fin m, (X i j) ^ 2))
        = ∑ i : Fin m, (X i j) ^ 2 := by
      rw [← mul_assoc, hmul, one_mul]
    linarith [h2, h3]
  exact ⟨hmain, hmain.trans hscale⟩
  /- @proof-region region.target-node.session.a8b96b4922487205 end -/

end Msc62GroundTruth
