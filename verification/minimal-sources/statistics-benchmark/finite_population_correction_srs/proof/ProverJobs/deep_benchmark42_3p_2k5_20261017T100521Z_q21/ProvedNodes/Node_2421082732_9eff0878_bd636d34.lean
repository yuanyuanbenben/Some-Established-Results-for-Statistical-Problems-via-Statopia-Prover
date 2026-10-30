import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q21.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q21.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q21.ProvedNodes.Node_1343175658_819cdf6e_f9605bef
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q21.ProvedNodes.Node_2596964945_1e623ff4_2e2b106e


open Finset
open Msc62GroundTruth

open Finset
namespace Msc62GroundTruth

set_option autoImplicit false in
theorem statopia_math_node_2421082732_9eff0878 : ∀ (N n : ℕ) (hN : 2 ≤ N) (hn_pos : 1 ≤ n) (hn_le : n ≤ N)
    (z : Fin N → ℝ) (hz : ∑ i : Fin N, z i = 0),
    ((Finset.univ : Finset (Fin N)).powersetCard n).sum
        (fun S => (S.sum (fun i => z i)) ^ 2)
      = ((N - 2).choose (n - 1) : ℝ) * ∑ i : Fin N, (z i) ^ 2 := by
  /- @proof-region region.target-node.session.d7058e9199f4bd9d begin -/
  intro N n hN hn_pos hn_le z hz
  set P : Finset (Finset (Fin N)) := (Finset.univ : Finset (Fin N)).powersetCard n with hP
  set C1 : ℕ := (N - 1).choose (n - 1) with hC1
  set C2 : ℕ := (N - 2).choose (n - 1) with hC2
  have hexp : ∀ S : Finset (Fin N), (S.sum (fun i => z i)) ^ 2 = S.sum (fun i => S.sum (fun j => z i * z j)) := by
    intro S
    rw [sq, Finset.sum_mul_sum]
  have hone : ∀ i : Fin N, (P.filter (fun S => i ∈ S)).card = C1 := by
    intro i
    have hmem : i ∈ (Finset.univ : Finset (Fin N)) := Finset.mem_univ i
    have key := statopia_math_node_1343175658_819cdf6e (Finset.univ : Finset (Fin N)) i hmem
      (∅ : Finset (Fin N)) (Finset.empty_subset _) n hn_pos
    rw [hP, hC1]
    have ef : ((Finset.univ : Finset (Fin N)).powersetCard n).filter (fun S => i ∈ S)
        = ((Finset.univ : Finset (Fin N)).powersetCard n).filter
            (fun S => i ∈ S ∧ S ∩ (∅ : Finset (Fin N)) = ∅) := by
      apply Finset.filter_congr
      intro S _
      simp
    rw [ef, key]
    congr 1
    have hs : ((Finset.univ : Finset (Fin N)).erase i \ (∅ : Finset (Fin N)))
        = (Finset.univ : Finset (Fin N)).erase i := by simp
    rw [hs, Finset.card_erase_of_mem hmem, Finset.card_univ, Fintype.card_fin]
  have hnotj : ∀ (i j : Fin N), i ≠ j → (P.filter (fun S => i ∈ S ∧ ¬ j ∈ S)).card = C2 := by
    intro i j hij
    have hmem : i ∈ (Finset.univ : Finset (Fin N)) := Finset.mem_univ i
    have hD : ({j} : Finset (Fin N)) ⊆ (Finset.univ : Finset (Fin N)).erase i := by
      intro x hx
      rw [Finset.mem_singleton] at hx
      rw [hx, Finset.mem_erase]
      exact ⟨Ne.symm hij, Finset.mem_univ j⟩
    have key := statopia_math_node_1343175658_819cdf6e (Finset.univ : Finset (Fin N)) i hmem
      ({j} : Finset (Fin N)) hD n hn_pos
    have hiff : ∀ S : Finset (Fin N), (S ∩ ({j} : Finset (Fin N)) = ∅) ↔ ¬ j ∈ S := by
      intro S
      constructor
      · intro h hj
        have h1 : j ∈ S ∩ ({j} : Finset (Fin N)) := by
          rw [Finset.mem_inter]
          exact ⟨hj, Finset.mem_singleton.mpr rfl⟩
        rw [h] at h1
        exact Finset.notMem_empty j h1
      · intro h
        exact Finset.inter_singleton_of_notMem h
    rw [hP, hC2]
    have ef : ((Finset.univ : Finset (Fin N)).powersetCard n).filter (fun S => i ∈ S ∧ ¬ j ∈ S)
        = ((Finset.univ : Finset (Fin N)).powersetCard n).filter
            (fun S => i ∈ S ∧ S ∩ ({j} : Finset (Fin N)) = ∅) := by
      apply Finset.filter_congr
      intro S _
      exact ⟨fun h => ⟨h.1, (hiff S).mpr h.2⟩, fun h => ⟨h.1, (hiff S).mp h.2⟩⟩
    rw [ef, key]
    congr 1
    have hcard2 : ((Finset.univ : Finset (Fin N)).erase i \ ({j} : Finset (Fin N))).card = N - 2 := by
      have h1 : ((Finset.univ : Finset (Fin N)).erase i \ ({j} : Finset (Fin N)))
          = ((Finset.univ : Finset (Fin N)).erase i).erase j := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_singleton, Finset.mem_univ,
          true_and]
        constructor
        · intro h; exact ⟨h.2, h.1⟩
        · intro h; exact ⟨h.2, h.1⟩
      rw [h1, Finset.card_erase_of_mem]
      · rw [Finset.card_erase_of_mem hmem, Finset.card_univ, Fintype.card_fin]
        omega
      · rw [Finset.mem_erase]
        exact ⟨Ne.symm hij, Finset.mem_univ j⟩
    rw [hcard2]
  have hdiagR : ∀ i : Fin N, (((P.filter (fun S => i ∈ S ∧ i ∈ S)).card : ℕ) : ℝ) = (C1 : ℝ) := by
    intro i
    have ef : P.filter (fun S => i ∈ S ∧ i ∈ S) = P.filter (fun S => i ∈ S) := by
      apply Finset.filter_congr
      intro S _
      exact ⟨fun h => h.1, fun h => ⟨h, h⟩⟩
    rw [ef, hone i]
  have hpairR : ∀ (i j : Fin N), i ≠ j →
      (((P.filter (fun S => i ∈ S ∧ j ∈ S)).card : ℕ) : ℝ) = (C1 : ℝ) - (C2 : ℝ) := by
    intro i j hij
    have hsplit : (P.filter (fun S => i ∈ S)).card
        = (P.filter (fun S => i ∈ S ∧ j ∈ S)).card
          + (P.filter (fun S => i ∈ S ∧ ¬ j ∈ S)).card := by
      have h := Finset.card_filter_add_card_filter_not (s := P.filter (fun S => i ∈ S))
        (p := fun S => j ∈ S)
      simp only [Finset.filter_filter] at h
      omega
    have h1 := hone i
    have h2 := hnotj i j hij
    have hnat : (P.filter (fun S => i ∈ S ∧ j ∈ S)).card + C2 = C1 := by omega
    have hcast : (((P.filter (fun S => i ∈ S ∧ j ∈ S)).card + C2 : ℕ) : ℝ) = (C1 : ℝ) := by
      rw [hnat]
    push_cast at hcast
    linarith
  have hrow : ∀ i : Fin N,
      (∑ j : Fin N, z j * (((P.filter (fun S => i ∈ S ∧ j ∈ S)).card : ℕ) : ℝ)) = z i * (C2 : ℝ) := by
    intro i
    have hmem : i ∈ (Finset.univ : Finset (Fin N)) := Finset.mem_univ i
    have hU : insert i ((Finset.univ : Finset (Fin N)).erase i) = (Finset.univ : Finset (Fin N)) :=
      Finset.insert_erase hmem
    have hnm : i ∉ (Finset.univ : Finset (Fin N)).erase i :=
      Finset.notMem_erase i (Finset.univ : Finset (Fin N))
    have hli : (∑ j ∈ (Finset.univ.erase i), z j) = - z i := by
      have hstep2 : (∑ j : Fin N, z j) = z i + ∑ j ∈ (Finset.univ.erase i), z j := by
        conv_lhs => rw [← hU]
        rw [Finset.sum_insert hnm]
      linarith
    have hstep : (∑ j : Fin N, z j * (((P.filter (fun S => i ∈ S ∧ j ∈ S)).card : ℕ) : ℝ))
        = z i * (((P.filter (fun S => i ∈ S ∧ i ∈ S)).card : ℕ) : ℝ)
          + ∑ j ∈ (Finset.univ.erase i),
              z j * (((P.filter (fun S => i ∈ S ∧ j ∈ S)).card : ℕ) : ℝ) := by
      conv_lhs => rw [← hU]
      rw [Finset.sum_insert hnm]
    have herase : (∑ j ∈ (Finset.univ.erase i),
          z j * (((P.filter (fun S => i ∈ S ∧ j ∈ S)).card : ℕ) : ℝ))
        = (∑ j ∈ (Finset.univ.erase i), z j) * ((C1 : ℝ) - (C2 : ℝ)) := by
      have hcongr : (∑ j ∈ (Finset.univ.erase i),
            z j * (((P.filter (fun S => i ∈ S ∧ j ∈ S)).card : ℕ) : ℝ))
          = ∑ j ∈ (Finset.univ.erase i), z j * ((C1 : ℝ) - (C2 : ℝ)) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hpairR i j (Ne.symm (Finset.mem_erase.mp hj).1)]
      rw [hcongr, Finset.sum_mul]
    rw [hstep, herase, hli, hdiagR i]
    ring
  have hT1 : P.sum (fun S => (S.sum (fun i => z i)) ^ 2)
      = P.sum (fun S => S.sum (fun i => S.sum (fun j => z i * z j))) :=
    Finset.sum_congr rfl (fun S _ => hexp S)
  have hT2 : P.sum (fun S => S.sum (fun i => S.sum (fun j => z i * z j)))
      = ∑ i : Fin N, ∑ j : Fin N,
          (z i * z j) * (((P.filter (fun S => i ∈ S ∧ j ∈ S)).card : ℕ) : ℝ) :=
    statopia_math_node_2596964945_1e623ff4 P (fun i j => z i * z j)
  have hT3 : (∑ i : Fin N, ∑ j : Fin N,
        (z i * z j) * (((P.filter (fun S => i ∈ S ∧ j ∈ S)).card : ℕ) : ℝ))
      = ∑ i : Fin N,
          z i * (∑ j : Fin N, z j * (((P.filter (fun S => i ∈ S ∧ j ∈ S)).card : ℕ) : ℝ)) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hT4 : (∑ i : Fin N,
        z i * (∑ j : Fin N, z j * (((P.filter (fun S => i ∈ S ∧ j ∈ S)).card : ℕ) : ℝ)))
      = (C2 : ℝ) * ∑ i : Fin N, (z i) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hrow i]
    ring
  rw [hT1, hT2, hT3, hT4]
  /- @proof-region region.target-node.session.d7058e9199f4bd9d end -/

end Msc62GroundTruth
