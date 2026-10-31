import ProverJobs.real_V_eq_15312944933b.Vocabulary
import ProverJobs.real_V_eq_15312944933b.Base
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_247222274_f4a96af6_4b656963
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_2695346019_c5493af6_1c088893
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_2798148667_8bcde5b0_9857b7f6
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_3200008108_17e56165_e20ae208
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_4221689064_d3ddf0ec_fbe161c8
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_934911440_5487385c_6cfc3bfb
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_951219948_a078b303_8e27ca79
open scoped BigOperators
open LiuBangXiangYu

open scoped BigOperators
namespace LiuBangXiangYu

set_option autoImplicit false in
theorem statopia_math_node_3886798737_08bdef52 : ∀ (n : ℕ) (hn : 1 ≤ n) (A : Finset ℝ)
    (hA : AdmissibleMark n A) (hcard : A.card = n),
    ∃ B : Finset ℝ, AdmissibleMark n B ∧ Disjoint A B ∧
      L A B ≤ (1 + (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 1)) / 2 := by
  /- @proof-region region.target-node.session.5f339b1238541be4 begin -/
  intro n hn A hA hcard
  obtain ⟨s, hs0, hs1, hs_mono, hs_int⟩ := statopia_math_node_951219948_a078b303 A hA.1
  obtain ⟨hpL_eq, hpL_len, hpL_pos, hpL_sum, hpL_ref, hpL_chain⟩ :=
    statopia_math_node_4221689064_d3ddf0ec A hA.1 s hs0 hs1 hs_mono hs_int
  let a : Fin (A.card + 1) → ℝ := fun i => s ((i : ℕ) + 1) - s (i : ℕ)
  have ha_pos : ∀ i, 0 < a i := by
    intro i
    have hi : (i : ℕ) ∈ Set.Icc (0 : ℕ) (A.card + 1) :=
      ⟨Nat.zero_le _, le_of_lt i.isLt⟩
    have hi' : (i : ℕ) + 1 ∈ Set.Icc (0 : ℕ) (A.card + 1) :=
      ⟨Nat.zero_le _, Nat.succ_le_of_lt i.isLt⟩
    have h := hs_mono hi hi' (Nat.lt_succ_self (i : ℕ))
    show 0 < s ((i : ℕ) + 1) - s (i : ℕ)
    exact sub_pos.mpr h
  have ha_sum : ∑ i : Fin (A.card + 1), a i = 1 := by
    have h1 : (List.map (fun i => s (i + 1) - s i) (List.range (A.card + 1))).sum = 1 := by
      rw [← hpL_eq]
      exact hpL_sum
    have h2 : ∑ i : Fin (A.card + 1), a i
        = (List.map (fun i => s (i + 1) - s i) (List.range (A.card + 1))).sum := by
      rw [Finset.sum_fin_eq_sum_range (fun i => a i)]
      trans (∑ x ∈ Finset.range (A.card + 1), (s (x + 1) - s x))
      · exact Finset.sum_congr rfl (fun x hx => by
          split_ifs with h
          · simp [a]
          · exfalso
            have hx' := Finset.mem_range.mp hx
            omega)
      · first | rfl | simp
    rw [h2, h1]
  obtain ⟨I, J, hIJ, hne, hbound⟩ :=
    statopia_math_node_2798148667_8bcde5b0 (A.card + 1) (by omega) a ha_pos ha_sum
  have key : ∀ (I J : Finset (Fin (A.card + 1))), Disjoint I J → I ∪ J ≠ ∅ →
      (∑ j ∈ J, a j) ≤ ∑ i ∈ I, a i →
      (∑ i ∈ I, a i) - (∑ j ∈ J, a j) ≤ 1 / ((2 : ℝ) ^ (n + 1) - 1) →
      ∃ B : Finset ℝ, AdmissibleMark n B ∧ Disjoint A B ∧
        L A B ≤ (1 + (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 1)) / 2 := by
    intro I J hIJ hne hUW hbound'
    exact statopia_math_node_934911440_5487385c n hn A hA hcard s hs0 hs1 hs_mono hs_int
      I J hIJ hne hUW hbound'
  have hden : (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 1) = 1 / ((2 : ℝ) ^ (A.card + 1) - 1) := by
    rw [hcard]
  by_cases hle : (∑ j ∈ J, a j) ≤ ∑ i ∈ I, a i
  · refine key I J hIJ hne hle ?_
    have h2 : (∑ i ∈ I, a i) - (∑ j ∈ J, a j) ≤ 1 / ((2 : ℝ) ^ (A.card + 1) - 1) :=
      (abs_le.mp hbound).2
    rw [hden]
    exact h2
  · have hUW' : (∑ j ∈ I, a j) ≤ ∑ i ∈ J, a i := le_of_lt (not_le.mp hle)
    refine key J I hIJ.symm (by simpa [Finset.union_comm] using hne) hUW' ?_
    have h2 : (∑ i ∈ J, a i) - (∑ j ∈ I, a j) ≤ 1 / ((2 : ℝ) ^ (A.card + 1) - 1) := by
      have h1 : -(1 / ((2 : ℝ) ^ (A.card + 1) - 1)) ≤ (∑ i ∈ I, a i) - (∑ j ∈ J, a j) :=
        (abs_le.mp hbound).1
      have h1' := neg_le_neg h1
      simpa only [neg_sub, neg_neg] using h1'
    rw [hden]
    exact h2

  /- @proof-region region.target-node.session.5f339b1238541be4 end -/

end LiuBangXiangYu
