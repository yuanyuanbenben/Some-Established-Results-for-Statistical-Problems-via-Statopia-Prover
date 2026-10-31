import ProverJobs.real_V_eq_15312944933b.Vocabulary
import ProverJobs.real_V_eq_15312944933b.Base
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_3072499416_ba39391c_ab2fe261
open scoped BigOperators
open LiuBangXiangYu

open scoped BigOperators
namespace LiuBangXiangYu

set_option autoImplicit false in
theorem statopia_math_node_2583178723_e50b326f : ∀ (l : List ℝ) (blocks : List (List ℝ)) (hflat : blocks.flatten = l),
    ∃ o : Fin ((l.mergeSort (fun x1 x2 => decide (x1 ≥ x2))).length) → Fin blocks.length,
      ∀ i : Fin blocks.length,
        (∑ j ∈ Finset.univ.filter
              (fun j : Fin ((l.mergeSort (fun x1 x2 => decide (x1 ≥ x2))).length) => o j = i),
            (l.mergeSort (fun x1 x2 => decide (x1 ≥ x2))).get j)
          = (blocks.get i).sum := by
  /- @proof-region region.target-node.session.e11ceeeceb469c95 begin -/
  intro l blocks hflat
  classical
  obtain ⟨pos, hpos⟩ := statopia_math_node_3072499416_ba39391c l blocks hflat
  let D : List (ℝ × Fin blocks.length) := List.ofFn (fun j : Fin l.length => (l.get j, pos j))
  let cmp : (ℝ × Fin blocks.length) → (ℝ × Fin blocks.length) → Bool :=
    fun a b => decide (a.1 ≥ b.1)
  let Ds : List (ℝ × Fin blocks.length) := D.mergeSort cmp
  let vals : List ℝ := Ds.map Prod.fst
  have hDfst : D.map Prod.fst = l := by
    rw [List.map_ofFn]
    exact List.ofFn_get l
  have hpermDs : Ds.Perm D := List.mergeSort_perm D cmp
  have aux_pairwise_get : ∀ l : List ℝ, List.Pairwise (fun a b : ℝ => a ≥ b) l →
      ∀ (i j : ℕ) (hi : i < l.length) (hj : j < l.length), i ≤ j → l[j] ≤ l[i] := by
    intro l
    induction l with
    | nil => intro h i j hi hj hij; simp at hi
    | cons a t ih =>
      intro h i j hi hj hij
      cases h with
      | cons hrel htail =>
        cases i with
        | zero =>
          cases j with
          | zero => simp
          | succ m =>
            have hm : m < t.length := by
              simp only [List.length_cons] at hj
              omega
            simpa using hrel t[m] (List.getElem_mem hm)
        | succ k =>
          cases j with
          | zero => exact absurd hij (by omega)
          | succ m =>
            have hk : k < t.length := by
              simp only [List.length_cons] at hi
              omega
            have hm : m < t.length := by
              simp only [List.length_cons] at hj
              omega
            have hkm : k ≤ m := by omega
            simpa using ih htail k m hk hm hkm
  have hvalssortPW : List.Pairwise (fun a b : ℝ => a ≥ b) vals := by
    have h1 : List.Pairwise (fun a b : ℝ × Fin blocks.length => decide (a.1 ≥ b.1) = true) Ds :=
      List.sorted_mergeSort (le := fun a b : ℝ × Fin blocks.length => decide (a.1 ≥ b.1))
        (fun a b c hab hbc =>
          decide_eq_true_iff.mpr (le_trans (of_decide_eq_true hbc) (of_decide_eq_true hab)))
        (fun a b => by
          show (decide (a.1 ≥ b.1) || decide (b.1 ≥ a.1)) = true
          rcases le_total a.1 b.1 with h | h
          · rw [decide_eq_true_iff.mpr h]; simp
          · rw [decide_eq_true_iff.mpr h]; simp)
        D
    exact List.Pairwise.map Prod.fst (fun a b hab => (of_decide_eq_true hab : a.1 ≥ b.1)) h1
  have hvalssort : List.SortedGE vals := by
    unfold List.SortedGE
    intro i j hij
    rw [List.get_eq_getElem, List.get_eq_getElem]
    exact aux_pairwise_get vals hvalssortPW i.val j.val i.isLt j.isLt hij
  have hsrt_sortPW : List.Pairwise (fun a b : ℝ => a ≥ b)
      (l.mergeSort (fun x1 x2 => decide (x1 ≥ x2))) := by
    have h1 : List.Pairwise (fun a b : ℝ => decide (a ≥ b) = true)
        (l.mergeSort (fun x1 x2 => decide (x1 ≥ x2))) :=
      List.sorted_mergeSort (le := fun x1 x2 : ℝ => decide (x1 ≥ x2))
        (fun a b c hab hbc =>
          decide_eq_true_iff.mpr (le_trans (of_decide_eq_true hbc) (of_decide_eq_true hab)))
        (fun a b => by
          show (decide (a ≥ b) || decide (b ≥ a)) = true
          rcases le_total a b with h | h
          · rw [decide_eq_true_iff.mpr h]; simp
          · rw [decide_eq_true_iff.mpr h]; simp)
        l
    have h2 : List.Pairwise (fun a b : ℝ => a ≥ b)
        (List.map id (l.mergeSort (fun x1 x2 => decide (x1 ≥ x2)))) :=
      List.Pairwise.map id (fun a b hab => (of_decide_eq_true hab : a ≥ b)) h1
    rwa [List.map_id] at h2
  have hsrt_sort : List.SortedGE (l.mergeSort (fun x1 x2 => decide (x1 ≥ x2))) := by
    unfold List.SortedGE
    intro i j hij
    rw [List.get_eq_getElem, List.get_eq_getElem]
    exact aux_pairwise_get (l.mergeSort (fun x1 x2 => decide (x1 ≥ x2)))
      hsrt_sortPW i.val j.val i.isLt j.isLt hij
  have hpermvals : vals.Perm (l.mergeSort (fun x1 x2 => decide (x1 ≥ x2))) := by
    have h1 : l.Perm vals := by
      have h2 := List.Perm.map Prod.fst hpermDs.symm
      rw [hDfst] at h2
      exact h2
    exact h1.symm.trans (List.mergeSort_perm l (fun x1 x2 => decide (x1 ≥ x2))).symm
  have hvalseq : vals = l.mergeSort (fun x1 x2 => decide (x1 ≥ x2)) :=
    List.Perm.eq_of_sortedGE hvalssort hsrt_sort hpermvals
  have hcast : (l.mergeSort (fun x1 x2 => decide (x1 ≥ x2))).length = (Ds.map Prod.snd).length := by
    show (l.mergeSort (fun x1 x2 => decide (x1 ≥ x2))).length =
      ((D.mergeSort cmp).map Prod.snd).length
    rw [List.length_map, List.length_mergeSort, List.length_mergeSort]
    show l.length = D.length
    rw [show D.length = l.length from List.length_ofFn]
  rw [show l.mergeSort (fun x1 x2 => decide (x1 ≥ x2)) = vals from hvalseq.symm]
  have hlen : vals.length = Ds.length := by
    show (Ds.map Prod.fst).length = Ds.length
    rw [List.length_map]
  have sum_cast : ∀ (m : ℕ) (hm : vals.length = m) (G : Fin m → ℝ),
      (List.ofFn (fun j : Fin vals.length => G (Fin.cast hm j))).sum = (List.ofFn G).sum := by
    intro m hm G
    revert G
    cases hm
    intro G
    simp only [List.sum_ofFn]
    apply Finset.sum_congr rfl
    intro j _
    first
      | rfl
      | (congr 1; decide)
      | (congr 1; ext; rfl)
  have val_get : ∀ j : Fin vals.length, vals.get j = (Ds.get (Fin.cast hlen j)).1 := by
    intro j
    show (Ds.map Prod.fst).get j = (Ds.get (Fin.cast hlen j)).1
    rw [List.get_eq_getElem, List.get_eq_getElem]
    rw [List.getElem_map]
    rfl
  refine ⟨fun j => (Ds.get (Fin.cast hlen j)).2, ?_⟩
  intro i
  let H : ℝ × Fin blocks.length → ℝ := fun q => if q.2 = i then q.1 else 0
  have step1 : (∑ j ∈ Finset.univ.filter (fun j : Fin vals.length => (Ds.get (Fin.cast hlen j)).2 = i), vals.get j)
      = (List.ofFn (fun j : Fin vals.length => H (Ds.get (Fin.cast hlen j)))).sum := by
    rw [Finset.sum_filter, List.sum_ofFn]
    apply Finset.sum_congr rfl
    intro j _
    rw [val_get j]
  have step2b : (List.ofFn (fun k : Fin Ds.length => H (Ds.get k))).sum = (Ds.map H).sum := by
    have h2 : List.ofFn (fun k : Fin Ds.length => Ds.get k) = Ds := List.ofFn_get Ds
    have hmap : List.map H (List.ofFn (fun k : Fin Ds.length => Ds.get k))
        = List.ofFn (fun k : Fin Ds.length => H (Ds.get k)) :=
      List.map_ofFn (fun k : Fin Ds.length => Ds.get k) H
    rw [← hmap, h2]
  have step2 : (List.ofFn (fun j : Fin vals.length => H (Ds.get (Fin.cast hlen j)))).sum
      = (Ds.map H).sum :=
    (sum_cast Ds.length hlen (fun k : Fin Ds.length => H (Ds.get k))).trans step2b
  have step3 : (Ds.map H).sum = (D.map H).sum :=
    List.Perm.sum_eq (List.Perm.map H hpermDs)
  have hDlist : D.map H = List.ofFn (fun j : Fin l.length => if pos j = i then l.get j else 0) := by
    show (List.ofFn fun j : Fin l.length => (l.get j, pos j)).map H
      = List.ofFn (fun j : Fin l.length => if pos j = i then l.get j else 0)
    rw [List.map_ofFn]
    exact congrArg List.ofFn (funext (fun j => by
      show H (l.get j, pos j) = if pos j = i then l.get j else 0
      rfl))
  have step4 : (D.map H).sum = (∑ j ∈ Finset.univ.filter (fun j : Fin l.length => pos j = i), l.get j) := by
    rw [hDlist, List.sum_ofFn, Finset.sum_filter]
  exact step1.trans (step2.trans (step3.trans (step4.trans (hpos i))))
  /- @proof-region region.target-node.session.e11ceeeceb469c95 end -/

end LiuBangXiangYu
