import ProverJobs.job_paper_20b0260ed6f74673a96e9b9321c3333f.Vocabulary
import ProverJobs.job_paper_20b0260ed6f74673a96e9b9321c3333f.Base

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_947343170_012e2f22 : ∀ (n s : ℕ),
    (by
      classical
      let O : Finset (Fin s → Finset (Fin n)) :=
        Finset.univ.filter fun f =>
          (∀ j : Fin s, (f j).Nonempty) ∧
            (∀ j j' : Fin s, j ≠ j' → Disjoint (f j) (f j')) ∧
              (∀ i : Fin n, ∃ j : Fin s, i ∈ f j)
      exact
        ((∀ f ∈ O,
            (∀ j : Fin s, (f j).card ≤ n) ∧
              (∑ j : Fin s, (f j).card = n) ∧
                (∃ a ∈ orderedCompositions n s, ∀ j : Fin s, (a j).val = (f j).card)) ∧
          (∀ (M : Type*) [AddCommMonoid M] (g : (Fin s → Finset (Fin n)) → M),
            ∑ f ∈ O, g f =
              ∑ a ∈ orderedCompositions n s,
                ∑ f ∈ O.filter (fun f => ∀ j : Fin s, (f j).card = (a j).val), g f))) := by
  /- @proof-region region.target-node.session.e56db20def4066e1 begin -/
  intro n s
  dsimp only
  set O : Finset (Fin s → Finset (Fin n)) := (by
    classical
    exact Finset.univ.filter (fun f =>
      (∀ j : Fin s, (f j).Nonempty) ∧
      (∀ j k : Fin s, j ≠ k → Disjoint (f j) (f k)) ∧
      (∀ i : Fin n, ∃ j : Fin s, i ∈ f j))) with hO
  classical
  have sum_card : ∀ p : Fin s → Finset (Fin n),
      (∀ j k : Fin s, j ≠ k → Disjoint (p j) (p k)) →
      (∀ i : Fin n, ∃ j : Fin s, i ∈ p j) →
      ∑ j : Fin s, (p j).card = n := by
    intro p hdisj hcov
    have hpd : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin s))) (fun j => p j) := by
      intro a _ b _ hne
      exact hdisj a b hne
    have h1 := Finset.card_biUnion (s := Finset.univ) (t := fun j => p j) hpd
    have hunion : Finset.univ.biUnion (fun j => p j) = Finset.univ := by
      rw [Finset.eq_univ_iff_forall]
      intro i
      rw [Finset.mem_biUnion]
      obtain ⟨j, hj⟩ := hcov i
      exact ⟨j, Finset.mem_univ j, hj⟩
    rw [hunion, Finset.card_univ, Fintype.card_fin] at h1
    exact h1.symm
  constructor
  · intro f hf
    obtain ⟨_, hne, hdisj, hcov⟩ := Finset.mem_filter.mp hf
    have hcard : ∀ j : Fin s, (f j).card ≤ n := fun j => by
      simpa using Finset.card_le_card (Finset.subset_univ (f j))
    refine ⟨hcard, sum_card f hdisj hcov, ?_⟩
    refine ⟨fun j => ⟨(f j).card, Nat.lt_succ_of_le (hcard j)⟩, ?_, ?_⟩
    · simp only [orderedCompositions, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, ?_⟩
      · intro j
        show (1 : ℕ) ≤ (f j).card
        have := Finset.card_pos.mpr (hne j)
        omega
      · show ∑ j : Fin s, (f j).card = n
        exact sum_card f hdisj hcov
    · intro j
      rfl
  · intro M _ g
    let V : (Fin s → Finset (Fin n)) → (Fin s → Fin (n + 1)) :=
      fun x j => ⟨min ((x j).card) n, Nat.lt_succ_of_le (min_le_right ((x j).card) n)⟩
    have hiff : ∀ (a : Fin s → Fin (n + 1)) (x : Fin s → Finset (Fin n)),
        (V x = a) ↔ (∀ j : Fin s, (x j).card = (a j).val) := by
      intro a x
      constructor
      · intro hV j
        have h1 : (V x j).val = (a j).val := congrArg Fin.val (congrFun hV j)
        have hVval : (V x j).val = (x j).card := by
          show min ((x j).card) n = (x j).card
          exact min_eq_left (by simpa using Finset.card_le_card (Finset.subset_univ (x j)))
        rw [hVval] at h1
        exact h1
      · intro hc
        funext j
        apply Fin.ext
        have hVval : (V x j).val = (x j).card := by
          show min ((x j).card) n = (x j).card
          exact min_eq_left (by simpa using Finset.card_le_card (Finset.subset_univ (x j)))
        exact hVval.trans (hc j)
    have hmem : ∀ x ∈ O, V x ∈ orderedCompositions n s := by
      intro x hx
      obtain ⟨_, hne, hdisj, hcov⟩ := Finset.mem_filter.mp hx
      have hVval : ∀ j : Fin s, (V x j).val = (x j).card := fun j => by
        show min ((x j).card) n = (x j).card
        exact min_eq_left (by simpa using Finset.card_le_card (Finset.subset_univ (x j)))
      simp only [orderedCompositions, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, ?_⟩
      · intro j
        rw [hVval j]
        have := Finset.card_pos.mpr (hne j)
        omega
      · have hxs : ∑ j : Fin s, (x j).card = n := sum_card x hdisj hcov
        have hcongr : ∑ j : Fin s, (V x j).val = ∑ j : Fin s, (x j).card := by
          apply Finset.sum_congr rfl
          intro j _
          exact hVval j
        exact hcongr.trans hxs
    have hfilter : ∀ a : Fin s → Fin (n + 1),
        O.filter (fun f => V f = a) =
          O.filter (fun f => ∀ j : Fin s, (f j).card = (a j).val) := by
      intro a
      apply Finset.filter_congr
      intro x _
      exact hiff a x
    have hstr : (∑ a ∈ orderedCompositions n s,
          ∑ f ∈ O.filter (fun f => V f = a), g f) = ∑ f ∈ O, g f :=
      Finset.sum_fiberwise_of_maps_to (s := O) (t := orderedCompositions n s) (g := V) hmem g
    have hstr2 : (∑ a ∈ orderedCompositions n s,
          ∑ f ∈ O.filter (fun f => V f = a), g f)
        = ∑ a ∈ orderedCompositions n s,
          ∑ f ∈ O.filter (fun f => ∀ j : Fin s, (f j).card = (a j).val), g f := by
      apply Finset.sum_congr rfl
      intro a _
      simp only [hfilter a]
    exact hstr.symm.trans hstr2
  /- @proof-region region.target-node.session.e56db20def4066e1 end -/

end Statlib.Imported
