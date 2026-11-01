import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.Definitions
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M000_Vocabulary
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M001_Base

/- Original module ProverJobs.job_paper_dc88427b52844263b5321fc99eb582d8.ProvedNodes.Node_2358914211_b4f8e1dc_5ae14418; genuine source relocated, namespace-isolated only. -/
namespace DPCompletedProof
open _root_.Statlib.Imported

open Statlib.Imported
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Statlib.Imported
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_2358914211_b4f8e1dc : ∀ (n : ℕ) (w : Finset (Fin n) → ℝ)
    (S : Finset (Fin n)) (j : ℕ) (hj : 1 ≤ j),
    (∑ f ∈ (Finset.univ : Finset (Fin j → Finset (Fin n))).filter (fun f =>
        (∀ i : Fin j, (f i).Nonempty) ∧
        (∀ i : Fin j, f i ⊆ S) ∧
        (∀ i : Fin j, ∀ i' : Fin j, i ≠ i' → Disjoint (f i) (f i')) ∧
        (∀ x ∈ S, ∃ i : Fin j, x ∈ f i)),
      ∏ i : Fin j, w (f i))
    = (∑ B ∈ (Finset.univ : Finset (Finset (Fin n))).filter
          (fun B => B.Nonempty ∧ B ⊆ S),
        w B * (∑ f ∈ (Finset.univ : Finset (Fin (j - 1) → Finset (Fin n))).filter (fun f =>
            (∀ i : Fin (j - 1), (f i).Nonempty) ∧
            (∀ i : Fin (j - 1), f i ⊆ S \ B) ∧
            (∀ i : Fin (j - 1), ∀ i' : Fin (j - 1), i ≠ i' → Disjoint (f i) (f i')) ∧
            (∀ x ∈ S \ B, ∃ i : Fin (j - 1), x ∈ f i)),
          ∏ i : Fin (j - 1), w (f i))) := by
  /- @proof-region region.target-node.session.7529c049cf9087ab begin -/
  intro n w S j hj
  generalize hk : j - 1 = k
  have hj' : j = k + 1 := by rw [← hk]; exact (Nat.sub_add_cancel hj).symm
  rw [hj']
  classical
  have key :
      (∑ f ∈ (Finset.univ : Finset (Fin (k + 1) → Finset (Fin n))).filter (fun f =>
          (∀ i : Fin (k + 1), (f i).Nonempty) ∧
          (∀ i : Fin (k + 1), f i ⊆ S) ∧
          (∀ i : Fin (k + 1), ∀ i' : Fin (k + 1), i ≠ i' → Disjoint (f i) (f i')) ∧
          (∀ x ∈ S, ∃ i : Fin (k + 1), x ∈ f i)),
        ∏ i : Fin (k + 1), w (f i))
      = ∑ y ∈ ((Finset.univ : Finset (Finset (Fin n))).filter (fun B => B.Nonempty ∧ B ⊆ S)).sigma
            (fun B => (Finset.univ : Finset (Fin k → Finset (Fin n))).filter (fun g =>
              (∀ i : Fin k, (g i).Nonempty) ∧
              (∀ i : Fin k, g i ⊆ S \ B) ∧
              (∀ i : Fin k, ∀ i' : Fin k, i ≠ i' → Disjoint (g i) (g i')) ∧
              (∀ x ∈ S \ B, ∃ i : Fin k, x ∈ g i))),
          w y.fst * ∏ i : Fin k, w (y.snd i) := by
    refine Finset.sum_bij (fun a _ => ⟨a 0, Fin.tail a⟩) ?_ ?_ ?_ ?_
    · intro a ha
      rw [Finset.mem_filter] at ha
      obtain ⟨-, hL1, hL2, hL3, hL4⟩ := ha
      rw [Finset.mem_sigma]
      constructor
      · rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hL1 0, hL2 0⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_, ?_, ?_, ?_⟩
        · intro i
          exact hL1 (Fin.succ i)
        · intro i x hx
          rw [Finset.mem_sdiff]
          refine ⟨hL2 (Fin.succ i) hx, ?_⟩
          have hne : Fin.succ i ≠ (0 : Fin (k+1)) := by
            intro h
            have h2 : i.val + 1 = 0 := by
              have := congrArg Fin.val h
              simpa using this
            omega
          exact (Finset.disjoint_left.mp (hL3 (Fin.succ i) 0 hne)) hx
        · intro i i' hii'
          exact hL3 (Fin.succ i) (Fin.succ i') (fun h => hii' (Fin.succ_injective k h))
        · intro x hx
          rw [Finset.mem_sdiff] at hx
          obtain ⟨hxS, hx0⟩ := hx
          obtain ⟨i0, hi0⟩ := hL4 x hxS
          have hi0ne : i0 ≠ 0 := by
            intro h
            rw [h] at hi0
            exact hx0 hi0
          have hpos : 0 < i0.val :=
            Nat.pos_of_ne_zero (fun h => hi0ne (Fin.ext (by simpa using h)))
          have hi0lt : i0.val < k + 1 := i0.isLt
          let j : Fin k := ⟨i0.val - 1, by omega⟩
          have hsucc : Fin.succ j = i0 := by
            apply Fin.ext
            show i0.val - 1 + 1 = i0.val
            omega
          refine ⟨j, ?_⟩
          show x ∈ a (Fin.succ j)
          rw [hsucc]
          exact hi0
    · intro a1 _ a2 _ h
      have h1 : a1 0 = a2 0 := by simpa using congrArg (fun x => x.fst) h
      have h2 : Fin.tail a1 = Fin.tail a2 := by simpa using congrArg (fun x => x.snd) h
      calc a1 = Fin.cons (a1 0) (Fin.tail a1) := (Fin.cons_self_tail a1).symm
        _ = Fin.cons (a2 0) (Fin.tail a2) := by rw [h1, h2]
        _ = a2 := Fin.cons_self_tail a2
    · intro a1 ha1
      obtain ⟨B, gg⟩ := a1
      rw [Finset.mem_sigma] at ha1
      obtain ⟨hB, hgg⟩ := ha1
      rw [Finset.mem_filter] at hB hgg
      obtain ⟨-, hBne, hBsub⟩ := hB
      obtain ⟨-, hgg1, hgg2, hgg3, hgg4⟩ := hgg
      refine ⟨Fin.cons B gg, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_, ?_, ?_, ?_⟩
        · intro i
          refine Fin.cases ?_ ?_ i
          · rw [Fin.cons_zero]; exact hBne
          · intro j; rw [Fin.cons_succ]; exact hgg1 j
        · intro i
          refine Fin.cases ?_ ?_ i
          · rw [Fin.cons_zero]; exact hBsub
          · intro j
            rw [Fin.cons_succ]
            intro x hx
            exact (Finset.mem_sdiff.mp (hgg2 j hx)).1
        · intro i i'
          refine Fin.cases ?_ ?_ i
          · rw [Fin.cons_zero]
            refine Fin.cases ?_ ?_ i'
            · intro h; exact absurd rfl h
            · intro j
              rw [Fin.cons_succ]
              intro _
              exact Finset.disjoint_left.mpr (fun x hx hxg => (Finset.mem_sdiff.mp (hgg2 j hxg)).2 hx)
          · intro i1
            rw [Fin.cons_succ]
            refine Fin.cases ?_ ?_ i'
            · rw [Fin.cons_zero]
              intro _
              exact Finset.disjoint_left.mpr (fun x hxg hxB => (Finset.mem_sdiff.mp (hgg2 i1 hxg)).2 hxB)
            · intro j
              rw [Fin.cons_succ]
              intro h
              exact hgg3 i1 j (fun heq => h (congrArg Fin.succ heq))
        · intro x hx
          by_cases hxB : x ∈ B
          · exact ⟨0, by rw [Fin.cons_zero]; exact hxB⟩
          · obtain ⟨j, hj⟩ := hgg4 x (Finset.mem_sdiff.mpr ⟨hx, hxB⟩)
            exact ⟨j.succ, by rw [Fin.cons_succ]; exact hj⟩
      · have htail : Fin.tail (Fin.cons (α := fun _ : Fin (k+1) => Finset (Fin n)) B gg) = gg := by
          funext i
          show Fin.cons (α := fun _ : Fin (k+1) => Finset (Fin n)) B gg (Fin.succ i) = gg i
          rw [Fin.cons_succ]
        simp only [Fin.cons_zero, htail]
    · intro a ha
      exact Fin.prod_univ_succ (fun i => w (a i))
  have hsigma :
      (∑ B ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun B => B.Nonempty ∧ B ⊆ S),
          w B * (∑ g ∈ (Finset.univ : Finset (Fin k → Finset (Fin n))).filter (fun g =>
              (∀ i : Fin k, (g i).Nonempty) ∧
              (∀ i : Fin k, g i ⊆ S \ B) ∧
              (∀ i : Fin k, ∀ i' : Fin k, i ≠ i' → Disjoint (g i) (g i')) ∧
              (∀ x ∈ S \ B, ∃ i : Fin k, x ∈ g i)),
            ∏ i : Fin k, w (g i)))
      = ∑ y ∈ ((Finset.univ : Finset (Finset (Fin n))).filter (fun B => B.Nonempty ∧ B ⊆ S)).sigma
            (fun B => (Finset.univ : Finset (Fin k → Finset (Fin n))).filter (fun g =>
              (∀ i : Fin k, (g i).Nonempty) ∧
              (∀ i : Fin k, g i ⊆ S \ B) ∧
              (∀ i : Fin k, ∀ i' : Fin k, i ≠ i' → Disjoint (g i) (g i')) ∧
              (∀ x ∈ S \ B, ∃ i : Fin k, x ∈ g i))),
          w y.fst * ∏ i : Fin k, w (y.snd i) := by
    have hsig := (Finset.sum_sigma
      (s := (Finset.univ : Finset (Finset (Fin n))).filter (fun B => B.Nonempty ∧ B ⊆ S))
      (t := fun B => (Finset.univ : Finset (Fin k → Finset (Fin n))).filter (fun g =>
              (∀ i : Fin k, (g i).Nonempty) ∧
              (∀ i : Fin k, g i ⊆ S \ B) ∧
              (∀ i : Fin k, ∀ i' : Fin k, i ≠ i' → Disjoint (g i) (g i')) ∧
              (∀ x ∈ S \ B, ∃ i : Fin k, x ∈ g i)))
      (f := fun y => w y.fst * ∏ i : Fin k, w (y.snd i))).symm
    rw [← hsig]
    apply Finset.sum_congr rfl
    intro B hB
    exact Finset.mul_sum _ _ (w B)
  exact key.trans hsigma.symm
  /- @proof-region region.target-node.session.7529c049cf9087ab end -/

end

end Statlib.Imported
end DPCompletedProof
