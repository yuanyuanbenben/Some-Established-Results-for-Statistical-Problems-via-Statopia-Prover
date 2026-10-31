import ProverJobs.job_paper_20b0260ed6f74673a96e9b9321c3333f.Vocabulary
import ProverJobs.job_paper_20b0260ed6f74673a96e9b9321c3333f.Base
import ProverJobs.job_paper_20b0260ed6f74673a96e9b9321c3333f.ProvedNodes.Node_3407542413_9e317a08_caccb340

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_4055972497_2dd86b3f : ∀ (n s : ℕ) (a : Fin s → Fin (n + 1))
    (ha : a ∈ orderedCompositions n s),
    ((Finset.univ : Finset (Fin s → Finset (Fin n))).filter (fun f =>
        (∀ j : Fin s, f j ≠ ∅) ∧
        (∀ j : Fin s, ∀ k : Fin s, j ≠ k → Disjoint (f j) (f k)) ∧
        (∀ i : Fin n, ∃ j : Fin s, i ∈ f j) ∧
        (∀ j : Fin s, (f j).card = (a j).val))).card
      = Nat.multinomial (Finset.univ : Finset (Fin s)) (fun j : Fin s => (a j).val) := by
  /- @proof-region region.target-node.session.a2490c8f074ad42b begin -/
  intro n s a ha
  have ha' := ha
  simp only [orderedCompositions, Finset.mem_filter, Finset.mem_univ, true_and] at ha'
  obtain ⟨ha1, ha2⟩ := ha'
  have hmain : ∀ (s : ℕ) (α : Type) [Fintype α] [DecidableEq α] (b : Fin s → ℕ),
      (∑ j, b j = Fintype.card α) →
      Fintype.card {g : α → Fin s // ∀ j, (Finset.univ.filter (fun i => g i = j)).card = b j}
        = Nat.multinomial (Finset.univ : Finset (Fin s)) b :=
    statopia_math_node_3407542413_9e317a08
  have hbij : ((Finset.univ : Finset (Fin s → Finset (Fin n))).filter (fun f =>
      (∀ j : Fin s, (f j).Nonempty) ∧
      (∀ j k : Fin s, j ≠ k → Disjoint (f j) (f k)) ∧
      (∀ i : Fin n, ∃ j : Fin s, i ∈ f j) ∧
      (∀ j : Fin s, (f j).card = (a j).val))).card
      = Fintype.card {g : Fin n → Fin s //
          ∀ j, (Finset.univ.filter (fun i => g i = j)).card = (a j).val} := by
    rw [← Fintype.card_subtype (fun f : Fin s → Finset (Fin n) =>
      (∀ j : Fin s, (f j).Nonempty) ∧
      (∀ j k : Fin s, j ≠ k → Disjoint (f j) (f k)) ∧
      (∀ i : Fin n, ∃ j : Fin s, i ∈ f j) ∧
      (∀ j : Fin s, (f j).card = (a j).val))]
    have key : ∀ (f : {f : Fin s → Finset (Fin n) //
        (∀ j : Fin s, (f j).Nonempty) ∧
        (∀ j k : Fin s, j ≠ k → Disjoint (f j) (f k)) ∧
        (∀ i : Fin n, ∃ j : Fin s, i ∈ f j) ∧
        (∀ j : Fin s, (f j).card = (a j).val)}) (j : Fin s),
        (Finset.univ.filter (fun i => Classical.choose (f.2.2.2.1 i) = j)) = f.1 j := by
      intro f j
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        have hc := Classical.choose_spec (f.2.2.2.1 i)
        rw [h] at hc
        exact hc
      · intro h
        by_contra hne
        have hc := Classical.choose_spec (f.2.2.2.1 i)
        have hd : Disjoint (f.1 j) (f.1 (Classical.choose (f.2.2.2.1 i))) :=
          f.2.2.1 j _ (Ne.symm hne)
        exact (Finset.disjoint_left.mp hd) h hc
    have pgproof : ∀ (f : {f : Fin s → Finset (Fin n) //
        (∀ j : Fin s, (f j).Nonempty) ∧
        (∀ j k : Fin s, j ≠ k → Disjoint (f j) (f k)) ∧
        (∀ i : Fin n, ∃ j : Fin s, i ∈ f j) ∧
        (∀ j : Fin s, (f j).card = (a j).val)}),
        ∀ j : Fin s, (Finset.univ.filter (fun i => Classical.choose (f.2.2.2.1 i) = j)).card = (a j).val := by
      intro f j
      rw [key f j]
      exact f.2.2.2.2 j
    refine Fintype.card_congr (Equiv.ofBijective
      (fun f : {f : Fin s → Finset (Fin n) //
          (∀ j : Fin s, (f j).Nonempty) ∧
          (∀ j k : Fin s, j ≠ k → Disjoint (f j) (f k)) ∧
          (∀ i : Fin n, ∃ j : Fin s, i ∈ f j) ∧
          (∀ j : Fin s, (f j).card = (a j).val)} =>
        (⟨fun i => Classical.choose (f.2.2.2.1 i), pgproof f⟩ :
          {g : Fin n → Fin s // ∀ j, (Finset.univ.filter (fun i => g i = j)).card = (a j).val}))
      ⟨?_, ?_⟩)
    · intro f1 f2 h
      apply Subtype.ext
      funext j
      ext i
      have hval : Classical.choose (f1.2.2.2.1 i) = Classical.choose (f2.2.2.2.1 i) := by
        simpa using congrFun (congrArg Subtype.val h) i
      rw [← key f1 j, ← key f2 j]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hval]
    · intro g
      have hA : ∀ j : Fin s, (Finset.univ.filter (fun i => g.1 i = j)).Nonempty := by
        intro j
        exact Finset.card_pos.mp (by have h : 1 ≤ (a j).val := ha1 j; rw [g.2 j]; omega)
      have hB : ∀ j k : Fin s, j ≠ k →
          Disjoint (Finset.univ.filter (fun i => g.1 i = j)) (Finset.univ.filter (fun i => g.1 i = k)) := by
        intro j k hjk
        rw [Finset.disjoint_left]
        intro i hi hj
        exact hjk ((Finset.mem_filter.mp hi).2.symm.trans (Finset.mem_filter.mp hj).2)
      have hC : ∀ i : Fin n, ∃ j : Fin s, i ∈ Finset.univ.filter (fun i => g.1 i = j) := by
        intro i
        exact ⟨g.1 i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
      have hf : (∀ j : Fin s, (Finset.univ.filter (fun i => g.1 i = j)).Nonempty) ∧
          (∀ j k : Fin s, j ≠ k → Disjoint (Finset.univ.filter (fun i => g.1 i = j)) (Finset.univ.filter (fun i => g.1 i = k))) ∧
          (∀ i : Fin n, ∃ j : Fin s, i ∈ Finset.univ.filter (fun i => g.1 i = j)) ∧
          (∀ j : Fin s, (Finset.univ.filter (fun i => g.1 i = j)).card = (a j).val) :=
        ⟨hA, hB, hC, g.2⟩
      refine ⟨⟨fun j => Finset.univ.filter (fun i => g.1 i = j), hf⟩, ?_⟩
      apply Subtype.ext
      funext i
      have hspec := Classical.choose_spec (hf.2.2.1 i)
      rw [Finset.mem_filter] at hspec
      exact hspec.2.symm
  have hO : (Finset.univ : Finset (Fin s → Finset (Fin n))).filter (fun f =>
      (∀ j : Fin s, f j ≠ ∅) ∧
      (∀ j k : Fin s, j ≠ k → Disjoint (f j) (f k)) ∧
      (∀ i : Fin n, ∃ j : Fin s, i ∈ f j) ∧
      (∀ j : Fin s, (f j).card = (a j).val))
      = (Finset.univ : Finset (Fin s → Finset (Fin n))).filter (fun f =>
      (∀ j : Fin s, (f j).Nonempty) ∧
      (∀ j k : Fin s, j ≠ k → Disjoint (f j) (f k)) ∧
      (∀ i : Fin n, ∃ j : Fin s, i ∈ f j) ∧
      (∀ j : Fin s, (f j).card = (a j).val)) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun j => Finset.nonempty_iff_ne_empty.mpr (h1 j), h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun j => Finset.nonempty_iff_ne_empty.mp (h1 j), h2⟩
  rw [hO, hbij]
  exact hmain s (Fin n) (fun j => (a j).val) (by simpa using ha2)
  /- @proof-region region.target-node.session.a2490c8f074ad42b end -/

end Statlib.Imported
