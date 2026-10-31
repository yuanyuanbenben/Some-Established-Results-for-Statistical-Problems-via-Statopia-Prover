import ProverJobs.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.Vocabulary
import ProverJobs.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.Base
import ProverJobs.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.ProvedNodes.Node_506797512_86da7323_457a4a60

namespace PaperProofTasks.job_paper_cb04ce35a04d48a9bf96750470ca0eb0
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal
open _root_.PaperProofTasks.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.Statlib.Imported

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal
namespace Statlib.Imported

noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_4214122249_d32c5e83 : ∀ (C1 C_sigma alpha qn : ℝ) (p : ℕ → ℕ)
    (Sig : (n : ℕ) → Matrix (Fin (p n)) (Fin (p n)) ℝ)
    (piPerm : (n : ℕ) → Equiv.Perm (Fin (p n)))
    (tau : ℕ → ℝ) (beta : ℕ → ℝ) (k : ℕ → ℕ) (n : ℕ)
    (hC_sigma : 0 < C_sigma)
    (hC_sigma_le_C1 : C_sigma ≤ C1)
    (hC1_ge_one : (1 : ℝ) ≤ C1)
    (hsigma_upper : ∀ i : Fin (p n), k n ≤ (i : ℕ) + 1 →
      Real.sqrt (Sig n (piPerm n i) (piPerm n i)) ≤
        C_sigma * Real.rpow (((i : ℕ) + 1 : ℕ) : ℝ) (-alpha))
    (htau_nonneg : 0 ≤ tau n)
    (htau_le_one : 0 ≤ 1 - tau n)
    (hbeta_def : beta n = alpha * (1 - tau n))
    (hqn_nonneg : 0 ≤ qn)
    (hqn_beta_ge_two : 2 ≤ qn * beta n)
    (hk_ge_one : 1 ≤ k n),
    (∑ j ∈ Finset.univ.filter (fun j : Fin (p n) => ¬ (((piPerm n).symm j : ℕ) < k n)),
        Real.rpow (Real.sqrt (Sig n j j)) (qn * (1 - tau n)))
      ≤ Real.rpow C1 qn * Real.rpow (k n : ℝ) (1 - qn * beta n) := by
  /- @proof-region region.target-node.session.73a71ee9210e3f49 begin -/
  intro C1 C_sigma alpha qn p Sig piPerm tau beta k n hC_sigma hC_sigma_le_C1 hC1_ge_one
    hsigma_upper htau_nonneg htau_le_one hbeta_def hqn_nonneg hqn_beta_ge_two hk_ge_one
  have hC1nn : (0 : ℝ) ≤ C1 := le_trans (le_of_lt hC_sigma) hC_sigma_le_C1
  have hqne : 0 ≤ qn * (1 - tau n) := mul_nonneg hqn_nonneg htau_le_one
  have hqne_le : qn * (1 - tau n) ≤ qn := by
    have h1 : (1 : ℝ) - tau n ≤ 1 := by linarith
    nlinarith [hqn_nonneg, h1]
  have hterm : ∀ j ∈ Finset.univ.filter (fun j : Fin (p n) => ¬ (((piPerm n).symm j : ℕ) < k n)),
      Real.rpow (Real.sqrt (Sig n j j)) (qn * (1 - tau n)) ≤
        Real.rpow C1 qn * Real.rpow ((((piPerm n).symm j : ℕ) + 1 : ℕ) : ℝ) (-(qn * beta n)) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    have hkj : k n ≤ (((piPerm n).symm j : ℕ)) + 1 := by omega
    have hsig : Real.sqrt (Sig n j j) ≤
        C_sigma * Real.rpow ((((piPerm n).symm j : ℕ) + 1 : ℕ) : ℝ) (-alpha) := by
      have h := hsigma_upper ((piPerm n).symm j) hkj
      rw [Equiv.apply_symm_apply] at h
      exact h
    have hnn : (0 : ℝ) ≤ Real.rpow ((((piPerm n).symm j : ℕ) + 1 : ℕ) : ℝ) (-alpha) :=
      Real.rpow_nonneg (by positivity) _
    have hbase : Real.sqrt (Sig n j j) ≤
        C1 * Real.rpow ((((piPerm n).symm j : ℕ) + 1 : ℕ) : ℝ) (-alpha) :=
      le_trans hsig (mul_le_mul_of_nonneg_right hC_sigma_le_C1 hnn)
    have hraise : Real.rpow (Real.sqrt (Sig n j j)) (qn * (1 - tau n)) ≤
        Real.rpow (C1 * Real.rpow ((((piPerm n).symm j : ℕ) + 1 : ℕ) : ℝ) (-alpha)) (qn * (1 - tau n)) :=
      Real.rpow_le_rpow (Real.sqrt_nonneg _) hbase hqne
    have hmul : Real.rpow (C1 * Real.rpow ((((piPerm n).symm j : ℕ) + 1 : ℕ) : ℝ) (-alpha)) (qn * (1 - tau n))
        = Real.rpow C1 (qn * (1 - tau n)) *
          Real.rpow (Real.rpow ((((piPerm n).symm j : ℕ) + 1 : ℕ) : ℝ) (-alpha)) (qn * (1 - tau n)) :=
      Real.mul_rpow hC1nn hnn
    have hpos : (0 : ℝ) ≤ ((((piPerm n).symm j : ℕ) + 1 : ℕ) : ℝ) := by positivity
    have h1 : Real.rpow ((((piPerm n).symm j : ℕ) + 1 : ℕ) : ℝ) (-alpha * (qn * (1 - tau n)))
        = Real.rpow (Real.rpow ((((piPerm n).symm j : ℕ) + 1 : ℕ) : ℝ) (-alpha)) (qn * (1 - tau n)) :=
      Real.rpow_mul hpos (-alpha) (qn * (1 - tau n))
    have h2 : Real.rpow ((((piPerm n).symm j : ℕ) + 1 : ℕ) : ℝ) (-alpha * (qn * (1 - tau n)))
        = Real.rpow ((((piPerm n).symm j : ℕ) + 1 : ℕ) : ℝ) (-(qn * beta n)) := by
      congr 1
      rw [hbeta_def]
      ring
    have hexp : Real.rpow (Real.rpow ((((piPerm n).symm j : ℕ) + 1 : ℕ) : ℝ) (-alpha)) (qn * (1 - tau n))
        = Real.rpow ((((piPerm n).symm j : ℕ) + 1 : ℕ) : ℝ) (-(qn * beta n)) := by
      rw [← h1]
      exact h2
    have hexp_le : Real.rpow C1 (qn * (1 - tau n)) ≤ Real.rpow C1 qn :=
      Real.rpow_le_rpow_of_exponent_le hC1_ge_one hqne_le
    calc Real.rpow (Real.sqrt (Sig n j j)) (qn * (1 - tau n))
        ≤ Real.rpow (C1 * Real.rpow ((((piPerm n).symm j : ℕ) + 1 : ℕ) : ℝ) (-alpha)) (qn * (1 - tau n)) := hraise
      _ = Real.rpow C1 (qn * (1 - tau n)) * Real.rpow ((((piPerm n).symm j : ℕ) + 1 : ℕ) : ℝ) (-(qn * beta n)) := by
            rw [hmul, hexp]
      _ ≤ Real.rpow C1 qn * Real.rpow ((((piPerm n).symm j : ℕ) + 1 : ℕ) : ℝ) (-(qn * beta n)) :=
            mul_le_mul_of_nonneg_right hexp_le (Real.rpow_nonneg (by positivity) _)
  have hbound : (∑ i ∈ Finset.univ.filter (fun i : Fin (p n) => k n ≤ (i : ℕ)),
        Real.rpow ((((i : ℕ) + 1 : ℕ)) : ℝ) (-(qn * beta n)))
      ≤ Real.rpow (k n : ℝ) (1 - qn * beta n) := by
    exact statopia_math_node_506797512_86da7323 (qn * beta n) (p n) (k n) hqn_beta_ge_two hk_ge_one
  have hreindex : (∑ j ∈ Finset.univ.filter (fun j : Fin (p n) => ¬ (((piPerm n).symm j : ℕ) < k n)),
        Real.rpow ((((piPerm n).symm j : ℕ) + 1 : ℕ) : ℝ) (-(qn * beta n)))
      = (∑ i ∈ Finset.univ.filter (fun i : Fin (p n) => k n ≤ (i : ℕ)),
        Real.rpow ((((i : ℕ) + 1 : ℕ)) : ℝ) (-(qn * beta n))) := by
    have himageFin : (Finset.univ.filter (fun i : Fin (p n) => k n ≤ (i : ℕ))).image (piPerm n)
        = Finset.univ.filter (fun j : Fin (p n) => ¬ (((piPerm n).symm j : ℕ) < k n)) := by
      ext j
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, hki, hji⟩
        rw [← hji, Equiv.symm_apply_apply]
        omega
      · intro hj
        exact ⟨(piPerm n).symm j, Nat.le_of_not_lt hj, Equiv.apply_symm_apply _ _⟩
    rw [Finset.sum_filter, Finset.sum_filter]
    calc (∑ a : Fin (p n),
          (if ¬ ((piPerm n).symm a : ℕ) < k n then
            Real.rpow ((((piPerm n).symm a : ℕ) + 1 : ℕ) : ℝ) (-(qn * beta n)) else 0))
        = (∑ a : Fin (p n),
            (fun y : Fin (p n) =>
              if ¬ (y : ℕ) < k n then Real.rpow ((((y : ℕ) + 1 : ℕ)) : ℝ) (-(qn * beta n)) else 0)
            ((piPerm n).symm a)) :=
          Finset.sum_congr rfl (fun a _ => rfl)
      _ = (∑ a : Fin (p n),
            (fun y : Fin (p n) =>
              if ¬ (y : ℕ) < k n then Real.rpow ((((y : ℕ) + 1 : ℕ)) : ℝ) (-(qn * beta n)) else 0) a) :=
          Equiv.sum_comp ((piPerm n).symm)
            (fun y : Fin (p n) =>
              if ¬ (y : ℕ) < k n then Real.rpow ((((y : ℕ) + 1 : ℕ)) : ℝ) (-(qn * beta n)) else 0)
      _ = (∑ a : Fin (p n),
            if k n ≤ (a : ℕ) then Real.rpow ((((a : ℕ) + 1 : ℕ)) : ℝ) (-(qn * beta n)) else 0) := by
          apply Finset.sum_congr rfl
          intro a _
          dsimp only
          by_cases h : (a : ℕ) < k n
          · rw [if_neg (fun hh => hh h), if_neg (by omega)]
          · rw [if_pos h, if_pos (Nat.le_of_not_lt h)]
  have hsum : (∑ j ∈ Finset.univ.filter (fun j : Fin (p n) => ¬ (((piPerm n).symm j : ℕ) < k n)),
        Real.rpow (Real.sqrt (Sig n j j)) (qn * (1 - tau n)))
      ≤ Real.rpow C1 qn * (∑ j ∈ Finset.univ.filter (fun j : Fin (p n) => ¬ (((piPerm n).symm j : ℕ) < k n)),
        Real.rpow ((((piPerm n).symm j : ℕ) + 1 : ℕ) : ℝ) (-(qn * beta n))) := by
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.mul_sum]
  calc (∑ j ∈ Finset.univ.filter (fun j : Fin (p n) => ¬ (((piPerm n).symm j : ℕ) < k n)),
        Real.rpow (Real.sqrt (Sig n j j)) (qn * (1 - tau n)))
      ≤ Real.rpow C1 qn * (∑ j ∈ Finset.univ.filter (fun j : Fin (p n) => ¬ (((piPerm n).symm j : ℕ) < k n)),
        Real.rpow ((((piPerm n).symm j : ℕ) + 1 : ℕ) : ℝ) (-(qn * beta n))) := hsum
    _ = Real.rpow C1 qn * (∑ i ∈ Finset.univ.filter (fun i : Fin (p n) => k n ≤ (i : ℕ)),
        Real.rpow ((((i : ℕ) + 1 : ℕ)) : ℝ) (-(qn * beta n))) := by rw [hreindex]
    _ ≤ Real.rpow C1 qn * Real.rpow (k n : ℝ) (1 - qn * beta n) :=
        mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg hC1nn qn)
  /- @proof-region region.target-node.session.73a71ee9210e3f49 end -/

end

end Statlib.Imported

