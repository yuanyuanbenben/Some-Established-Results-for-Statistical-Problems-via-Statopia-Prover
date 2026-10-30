import ProverJobs.real_V_eq_15312944933b.Vocabulary
import ProverJobs.real_V_eq_15312944933b.Base
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_1937137240_45ae93aa_d1366699
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_247222274_f4a96af6_4b656963
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_2695346019_c5493af6_1c088893
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_3200008108_17e56165_e20ae208
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_3723013110_f47aad67_7cd68bc9
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_4221689064_d3ddf0ec_fbe161c8
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_951219948_a078b303_8e27ca79
open scoped BigOperators
open LiuBangXiangYu

open scoped BigOperators
namespace LiuBangXiangYu

set_option autoImplicit false in
theorem statopia_math_node_934911440_5487385c : ∀ (n : ℕ) (hn : 1 ≤ n) (A : Finset ℝ) (hA : AdmissibleMark n A) (hcard : A.card = n)
    (s : ℕ → ℝ) (hs0 : s 0 = 0) (hs1 : s (A.card + 1) = 1)
    (hs_mono : StrictMonoOn s (Set.Icc 0 (A.card + 1)))
    (hs_int : (A : Set ℝ) = s '' Set.Icc 1 A.card)
    (I J : Finset (Fin (A.card + 1))) (hIJ : Disjoint I J) (hne : I ∪ J ≠ ∅)
    (hUW : (∑ j ∈ J, (s ((j : ℕ) + 1) - s (j : ℕ)))
        ≤ ∑ i ∈ I, (s ((i : ℕ) + 1) - s (i : ℕ)))
    (hbound : (∑ i ∈ I, (s ((i : ℕ) + 1) - s (i : ℕ)))
        - (∑ j ∈ J, (s ((j : ℕ) + 1) - s (j : ℕ)))
        ≤ 1 / ((2 : ℝ) ^ (n + 1) - 1)),
    ∃ B : Finset ℝ, AdmissibleMark n B ∧ Disjoint A B ∧
      L A B ≤ (1 + (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 1)) / 2 := by
  /- @proof-region region.target-node.session.875ac0f6738154c8 begin -/
  intro n hn A hA hcard s hs0 hs1 hs_mono hs_int I J hIJ hne hUW hbound
  have hq : 1 ≤ A.card + 1 := Nat.succ_pos _
  let a : Fin (A.card + 1) → ℝ := fun i => s ((i : ℕ) + 1) - s (i : ℕ)
  have ha_pos : ∀ i, 0 < a i := by
    intro i
    have h1 : (i : ℕ) ∈ Set.Icc 0 (A.card + 1) := ⟨Nat.zero_le _, le_of_lt i.isLt⟩
    have h2 : (i : ℕ) + 1 ∈ Set.Icc 0 (A.card + 1) := ⟨Nat.zero_le _, Nat.succ_le_of_lt i.isLt⟩
    have hlt : (i : ℕ) < (i : ℕ) + 1 := Nat.lt_succ_self _
    have hs := hs_mono h1 h2 hlt
    show 0 < s ((i : ℕ) + 1) - s (i : ℕ)
    linarith
  have ha_sum : ∑ i : Fin (A.card + 1), a i = 1 := by
    have hfin : ∑ i : Fin (A.card + 1), a i
        = ∑ i : Fin (A.card + 1), (fun k : ℕ => s (k + 1) - s k) (i : ℕ) := rfl
    have htel : ∀ m : ℕ, ∑ k ∈ Finset.range m, (s (k + 1) - s k) = s m - s 0 := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [Finset.sum_range_succ, ih]; ring
    rw [hfin]
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => s (k + 1) - s k)]
    rw [htel (A.card + 1), hs1, hs0]
    norm_num
  have htel : ∀ m : ℕ, ∑ k ∈ Finset.range m, (s (k + 1) - s k) = s m := by
    intro m
    have h0 : ∑ k ∈ Finset.range m, (s (k + 1) - s k) = s m - s 0 := by
      induction m with
      | zero => simp
      | succ m ih => rw [Finset.sum_range_succ, ih]; ring
    rw [h0, hs0, sub_zero]
  let b : ℕ → ℝ := fun k => ∑ i : Fin (A.card + 1), if (i : ℕ) < k then a i else 0
  have hb : ∀ k, b k = ∑ i : Fin (A.card + 1), (if (i : ℕ) < k then a i else 0) := fun k => rfl
  have hbs : ∀ k, k ≤ A.card + 1 → b k = s k := by
    intro k
    induction k with
    | zero =>
        intro _
        rw [hb 0, hs0]
        simp
    | succ k ih =>
        intro hk
        have hk' : k ≤ A.card + 1 := le_trans (Nat.le_succ k) hk
        have hks : k < A.card + 1 := Nat.succ_le_iff.mp hk
        have hsingle : (∑ i : Fin (A.card + 1), (if i = ⟨k, hks⟩ then a i else 0)) = a ⟨k, hks⟩ := by
          simp
        have hp : ∀ i : Fin (A.card + 1),
            (if (i : ℕ) < k + 1 then a i else 0)
              = (if (i : ℕ) < k then a i else 0) + (if i = ⟨k, hks⟩ then a i else 0) := by
          intro i
          by_cases h1 : (i : ℕ) < k
          · have h4 : (i : ℕ) < k + 1 := by omega
            have hnot : ¬ (i = ⟨k, hks⟩) := by
              intro h
              have hk_eq : (i : ℕ) = k := by rw [h]
              omega
            rw [if_pos h4, if_pos h1, if_neg hnot, add_zero]
          · by_cases h2 : (i : ℕ) = k
            · have hi : i = ⟨k, hks⟩ := Fin.ext h2
              have h4 : (i : ℕ) < k + 1 := by omega
              rw [if_pos h4, if_neg (by omega : ¬ (i : ℕ) < k), if_pos hi, zero_add]
            · have h4 : ¬ (i : ℕ) < k + 1 := by omega
              have hnot : ¬ (i = ⟨k, hks⟩) := by
                intro h
                have hk_eq : (i : ℕ) = k := by rw [h]
                exact h2 hk_eq
              rw [if_neg h4, if_neg h1, if_neg hnot, add_zero]
        have hrec : (∑ i : Fin (A.card + 1), (if (i : ℕ) < k + 1 then a i else 0))
            = (∑ i : Fin (A.card + 1), (if (i : ℕ) < k then a i else 0)) + a ⟨k, hks⟩ := by
          have h1 : (∑ i : Fin (A.card + 1), (if (i : ℕ) < k + 1 then a i else 0))
              = ∑ i : Fin (A.card + 1),
                  ((if (i : ℕ) < k then a i else 0) + (if i = ⟨k, hks⟩ then a i else 0)) :=
            Finset.sum_congr rfl (fun i _ => hp i)
          rw [h1, Finset.sum_add_distrib, hsingle]
        have hgoal : b (k + 1) = b k + a ⟨k, hks⟩ := by
          rw [hb (k + 1), hb k]
          exact hrec
        have haeq : a ⟨k, hks⟩ = s (k + 1) - s k := rfl
        rw [hgoal, ih hk', haeq]
        ring
  let M : Finset ℝ := (Finset.univ.filter (fun k : Fin (A.card + 1) => k ∉ I ∪ J)).image
    (fun k : Fin (A.card + 1) => (b (k : ℕ) + b ((k : ℕ) + 1)) / 2)
  obtain ⟨C, hC1, hC2, hC3, hC4, Ps, R, hPsR, hR⟩ :=
    statopia_math_node_3200008108_17e56165 (A.card + 1) hq a ha_pos ha_sum I J hIJ hne hUW
  have hd : (∑ i ∈ I, a i) - (∑ j ∈ J, a j) ≤ 1 / ((2 : ℝ) ^ (A.card + 1) - 1) := by
    have hpow : ((2 : ℝ) ^ (A.card + 1) - 1) = ((2 : ℝ) ^ (n + 1) - 1) := by rw [hcard]
    rw [hpow]
    exact hbound
  have hkey :=
    statopia_math_node_1937137240_45ae93aa (A.card + 1) hq a ha_pos ha_sum b hb I J hIJ hne C hC1 hC2 hC3 hC4
  obtain ⟨hAdm, hDis, hMult⟩ := hkey
  have hset : (Finset.univ.filter (fun k : Fin (A.card + 1) => 1 ≤ (k : ℕ))).image
      (fun k : Fin (A.card + 1) => b (k : ℕ)) = A := by
    apply Finset.ext
    intro x
    constructor
    · intro hx
      rw [Finset.mem_image] at hx
      obtain ⟨k, hk, hkx⟩ := hx
      have hk1 : 1 ≤ (k : ℕ) := (Finset.mem_filter.mp hk).2
      have hsk : s (k : ℕ) = x := by
        rw [← hkx]
        exact (hbs (k : ℕ) (by have := k.isLt; omega)).symm
      rw [← Finset.mem_coe, hs_int]
      exact ⟨(k : ℕ), ⟨hk1, by have := k.isLt; omega⟩, hsk⟩
    · intro hx
      rw [← Finset.mem_coe] at hx
      rw [hs_int] at hx
      obtain ⟨j, hj, hjx⟩ := hx
      rw [Set.mem_Icc] at hj
      obtain ⟨hj1, hj2⟩ := hj
      rw [Finset.mem_image]
      refine ⟨⟨j, by omega⟩, ?_, ?_⟩
      · rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hj1⟩
      · show b j = x
        rw [← hjx]
        exact hbs j (by omega)
  refine ⟨C ∪ M, ⟨hAdm.1, by rw [← hcard, ← hset]; exact hAdm.2⟩, ?_, ?_⟩
  · rw [hset] at hDis
    exact hDis
  · have hS : (↑(A ∪ (C ∪ M)) : Set ℝ) ⊆ Set.Ioo (0 : ℝ) 1 := by
      rw [Finset.coe_union]
      exact Set.union_subset hA.1 hAdm.1
    obtain ⟨s', hs'0, hs'1, hs'mono, hs'int⟩ :=
      statopia_math_node_951219948_a078b303 (A ∪ (C ∪ M)) hS
    have h422 :=
      statopia_math_node_4221689064_d3ddf0ec (A ∪ (C ∪ M)) hS s' hs'0 hs'1 hs'mono hs'int
    have hL : ∀ z ∈ pieceLengths (A ∪ (C ∪ M)), 0 ≤ z :=
      fun z hz => le_of_lt (h422.2.2.1 z hz)
    have hsum : (pieceLengths (A ∪ (C ∪ M))).sum = 1 := h422.2.2.2.1
    rw [hset] at hMult
    let P : Multiset ℝ :=
      (∑ k ∈ Finset.univ.filter (fun k : Fin (A.card + 1) => k ∉ I ∪ J),
        ({a k / 2} : Multiset ℝ)) + Ps
    have hpair : (∑ k ∈ Finset.univ.filter (fun k : Fin (A.card + 1) => k ∉ I ∪ J),
          ({a k / 2, a k / 2} : Multiset ℝ))
        = (∑ k ∈ Finset.univ.filter (fun k : Fin (A.card + 1) => k ∉ I ∪ J),
            ({a k / 2} : Multiset ℝ))
          + (∑ k ∈ Finset.univ.filter (fun k : Fin (A.card + 1) => k ∉ I ∪ J),
            ({a k / 2} : Multiset ℝ)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun k _ => by simp)
    have hdec : Multiset.ofList (pieceLengths (A ∪ (C ∪ M))) = P + P + R := by
      have hmid : Multiset.ofList (pieceLengths (A ∪ (C ∪ M)))
          = ((∑ k ∈ Finset.univ.filter (fun k : Fin (A.card + 1) => k ∉ I ∪ J),
                ({a k / 2} : Multiset ℝ))
              + (∑ k ∈ Finset.univ.filter (fun k : Fin (A.card + 1) => k ∉ I ∪ J),
                ({a k / 2} : Multiset ℝ))) + (Ps + Ps + R) := by
        rw [hMult, hpair, hPsR]
      rw [hmid]
      rw [show P = (∑ k ∈ Finset.univ.filter (fun k : Fin (A.card + 1) => k ∉ I ∪ J),
          ({a k / 2} : Multiset ℝ)) + Ps from rfl]
      simp only [add_assoc, add_comm, add_left_comm]
    have hd' : R.sum ≤ 1 / ((2 : ℝ) ^ (n + 1) - 1) := by
      have hpow : ((2 : ℝ) ^ (A.card + 1) - 1) = ((2 : ℝ) ^ (n + 1) - 1) := by rw [hcard]
      rw [hR, ← hpow]
      exact hd
    exact statopia_math_node_3723013110_f47aad67 (pieceLengths (A ∪ (C ∪ M))) hL P R hdec hsum
      (1 / ((2 : ℝ) ^ (n + 1) - 1)) hd'
  /- @proof-region region.target-node.session.875ac0f6738154c8 end -/

end LiuBangXiangYu
