import ProverJobs.job_paper_20b0260ed6f74673a96e9b9321c3333f.Vocabulary
import ProverJobs.job_paper_20b0260ed6f74673a96e9b9321c3333f.Base

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_2866290612_0c13d721 : ∀ (n s : ℕ)
    (a : Fin s → Fin (n + 1)) (ha : a ∈ orderedCompositions n s),
    (∀ j : Fin s, (canonBlock n s a j).Nonempty) ∧
    (∀ j : Fin s, (canonBlock n s a j).card = (a j).val) ∧
    (∀ j k : Fin s, j ≠ k → Disjoint (canonBlock n s a j) (canonBlock n s a k)) ∧
    (∀ i : Fin n, ∃ j : Fin s, i ∈ canonBlock n s a j) ∧
    ((Finset.univ : Finset (Fin s)).sup (canonBlock n s a) = (Finset.univ : Finset (Fin n))) := by
  /- @proof-region region.target-node.session.447b3129321afd4d begin -/
  intro n s a ha
  classical
  simp only [orderedCompositions, Finset.mem_filter, Finset.mem_univ, true_and] at ha
  obtain ⟨ha1, ha2⟩ := ha
  have hP0 : partialSum n a 0 = 0 := by
    simp only [partialSum]
    exact Finset.sum_eq_zero (fun k _ => if_neg (Nat.not_lt_zero (k : ℕ)))
  have hPs : partialSum n a s = n := by
    have h1 : partialSum n a s = ∑ k : Fin s, (a k).val := by
      simp only [partialSum]
      exact Finset.sum_congr rfl (fun k _ => if_pos k.isLt)
    rw [h1, ha2]
  have hmono : Monotone (partialSum n a) := by
    intro m1 m2 hm
    simp only [partialSum]
    refine Finset.sum_le_sum (fun k _ => ?_)
    by_cases h : (k : ℕ) < m1
    · rw [if_pos h, if_pos (lt_of_lt_of_le h hm)]
    · rw [if_neg h]
      exact Nat.zero_le _
  have hstep : ∀ (j k : Fin s),
      (if (k : ℕ) < (j : ℕ) + 1 then (a k).val else 0)
        = (if (k : ℕ) < (j : ℕ) then (a k).val else 0)
          + (if k = j then (a j).val else 0) := by
    intro j k
    by_cases hkj : k = j
    · subst k
      have h1 : (j : ℕ) < (j : ℕ) + 1 := by omega
      have h2 : ¬ (j : ℕ) < (j : ℕ) := by omega
      rw [if_pos h1, if_neg h2, if_pos rfl]
      omega
    · by_cases hlt : (k : ℕ) < (j : ℕ)
      · have h1 : (k : ℕ) < (j : ℕ) + 1 := by omega
        rw [if_pos h1, if_pos hlt, if_neg hkj]
        omega
      · have h1 : ¬ (k : ℕ) < (j : ℕ) + 1 := by omega
        rw [if_neg h1, if_neg hlt, if_neg hkj]
  have hPsucc : ∀ j : Fin s,
      partialSum n a ((j : ℕ) + 1) = partialSum n a (j : ℕ) + (a j).val := by
    intro j
    have h1 : partialSum n a ((j : ℕ) + 1)
        = ∑ k : Fin s, ((if (k : ℕ) < (j : ℕ) then (a k).val else 0)
            + (if k = j then (a j).val else 0)) := by
      simp only [partialSum]
      exact Finset.sum_congr rfl (fun k _ => hstep j k)
    have h2 : (∑ k : Fin s, (if k = j then (a j).val else 0)) = (a j).val := by
      rw [Finset.sum_eq_single (a := j)]
      · rw [if_pos rfl]
      · intro b _ hb
        exact if_neg hb
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    have h3 : (∑ k : Fin s, (if (k : ℕ) < (j : ℕ) then (a k).val else 0))
        = partialSum n a (j : ℕ) := rfl
    calc partialSum n a ((j : ℕ) + 1)
        = ∑ k : Fin s, ((if (k : ℕ) < (j : ℕ) then (a k).val else 0)
            + (if k = j then (a j).val else 0)) := h1
      _ = (∑ k : Fin s, (if (k : ℕ) < (j : ℕ) then (a k).val else 0))
            + ∑ k : Fin s, (if k = j then (a j).val else 0) := Finset.sum_add_distrib
      _ = partialSum n a (j : ℕ) + (a j).val := by rw [h2, h3]
  have hPle : ∀ j : Fin s, partialSum n a ((j : ℕ) + 1) ≤ n := by
    intro j
    calc partialSum n a ((j : ℕ) + 1) ≤ partialSum n a s := hmono (Nat.succ_le_of_lt j.isLt)
      _ = n := hPs
  have hcard : ∀ j : Fin s, (canonBlock n s a j).card = (a j).val := by
    intro j
    have hstepj : partialSum n a ((j : ℕ) + 1) = partialSum n a (j : ℕ) + (a j).val := hPsucc j
    have hlej : partialSum n a ((j : ℕ) + 1) ≤ n := hPle j
    let f : Fin ((a j).val) → Fin n :=
      fun t => ⟨partialSum n a (j : ℕ) + t.val, by have := t.isLt; omega⟩
    have hfval : ∀ t : Fin ((a j).val), (f t).val = partialSum n a (j : ℕ) + t.val :=
      fun t => rfl
    have hbij : (Finset.univ : Finset (Fin ((a j).val))).card = (canonBlock n s a j).card := by
      refine Finset.card_bij
        (i := fun (t : Fin ((a j).val)) (_ : t ∈ (Finset.univ : Finset (Fin ((a j).val)))) => f t)
        ?_ ?_ ?_
      · intro t _
        simp only [canonBlock, Finset.mem_filter, Finset.mem_univ, true_and]
        show partialSum n a (j : ℕ) ≤ partialSum n a (j : ℕ) + t.val ∧
          partialSum n a (j : ℕ) + t.val < partialSum n a ((j : ℕ) + 1)
        exact ⟨by omega, by omega⟩
      · intro t1 _ t2 _ heq
        have h : (f t1).val = (f t2).val := congrArg Fin.val heq
        rw [hfval t1, hfval t2] at h
        exact Fin.ext (by omega)
      · intro i hi
        simp only [canonBlock, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        obtain ⟨hlei, hlti⟩ := hi
        refine ⟨⟨i.val - partialSum n a (j : ℕ), by omega⟩, Finset.mem_univ _, ?_⟩
        apply Fin.ext
        show partialSum n a (j : ℕ) + (i.val - partialSum n a (j : ℕ)) = i.val
        omega
    calc (canonBlock n s a j).card = (Finset.univ : Finset (Fin ((a j).val))).card := hbij.symm
      _ = (a j).val := by simp
  have hne : ∀ j : Fin s, (canonBlock n s a j).Nonempty := by
    intro j
    rw [← Finset.card_pos, hcard j]
    have h1 : 1 ≤ (a j).val := ha1 j
    omega
  have hdisj : ∀ j k : Fin s, j ≠ k → Disjoint (canonBlock n s a j) (canonBlock n s a k) := by
    intro j k hjk
    refine Finset.disjoint_left.mpr ?_
    intro i hi hk
    simp only [canonBlock, Finset.mem_filter, Finset.mem_univ, true_and] at hi hk
    obtain ⟨hlej, hltj⟩ := hi
    obtain ⟨hlek, hltk⟩ := hk
    have hne' : (j : ℕ) ≠ (k : ℕ) := fun h => hjk (Fin.ext h)
    rcases lt_or_gt_of_ne hne' with hlt | hlt
    · have h1 : partialSum n a ((j : ℕ) + 1) ≤ partialSum n a (k : ℕ) :=
        hmono (Nat.succ_le_of_lt hlt)
      omega
    · have h1 : partialSum n a ((k : ℕ) + 1) ≤ partialSum n a (j : ℕ) :=
        hmono (Nat.succ_le_of_lt hlt)
      omega
  have hcover : ∀ i : Fin n, ∃ j : Fin s, i ∈ canonBlock n s a j := by
    intro i
    have hex : ∃ m : ℕ, (i : ℕ) < partialSum n a m := ⟨s, by rw [hPs]; exact i.isLt⟩
    have hspec : (i : ℕ) < partialSum n a (Nat.find hex) := Nat.find_spec hex
    have hle : Nat.find hex ≤ s := Nat.find_min' hex (by rw [hPs]; exact i.isLt)
    have hpos : 1 ≤ Nat.find hex := by
      rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
      · rw [h, hP0] at hspec
        omega
      · omega
    have hprev : partialSum n a (Nat.find hex - 1) ≤ (i : ℕ) := by
      have h1 : ¬ (i : ℕ) < partialSum n a (Nat.find hex - 1) :=
        Nat.find_min hex (by omega)
      omega
    refine ⟨⟨Nat.find hex - 1, by omega⟩, ?_⟩
    rw [canonBlock, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, hprev, ?_⟩
    show (i : ℕ) < partialSum n a (Nat.find hex - 1 + 1)
    rw [Nat.sub_add_cancel hpos]
    exact hspec
  refine ⟨hne, hcard, hdisj, hcover, ?_⟩
  apply Finset.ext
  intro i
  rw [Finset.mem_sup]
  simp only [Finset.mem_univ, true_and]
  exact ⟨fun _ => trivial, fun _ => hcover i⟩
  /- @proof-region region.target-node.session.447b3129321afd4d end -/

end Statlib.Imported
