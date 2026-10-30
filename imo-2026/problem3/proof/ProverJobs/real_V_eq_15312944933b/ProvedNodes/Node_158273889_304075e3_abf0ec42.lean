import ProverJobs.real_V_eq_15312944933b.Vocabulary
import ProverJobs.real_V_eq_15312944933b.Base
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_247222274_f4a96af6_4b656963
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_3358436945_300d0d3a_563d9d50
open scoped BigOperators
open LiuBangXiangYu

open scoped BigOperators
namespace LiuBangXiangYu

set_option autoImplicit false in
theorem statopia_math_node_158273889_304075e3 : ∀ (l : List ℝ) (a : ℝ),
    let s : List ℝ := (a :: a :: l).mergeSort (· ≥ ·)
    let d : ℝ := ((s.zipIdx.filter (fun p => p.2 % 2 = 0)).map (fun p => p.1 - s.getD (p.2 + 1) 0)).sum
    let t : List ℝ := l.mergeSort (· ≥ ·)
    let e : ℝ := ((t.zipIdx.filter (fun p => p.2 % 2 = 0)).map (fun p => p.1 - t.getD (p.2 + 1) 0)).sum
    d = e := by
  /- @proof-region region.target-node.session.772cf405fa104b51 begin -/
  intro l a
  let B : List ℝ → ℝ := fun s =>
    (((s.zipIdx).filter (fun p => p.2 % 2 = 0)).map (fun p => p.1 - s.getD (p.2 + 1) 0)).sum
  show B ((a :: a :: l).mergeSort (· ≥ ·)) = B (l.mergeSort (· ≥ ·))
  have hBnil : B [] = 0 := by simp [B]
  have hBsingle : ∀ x : ℝ, B [x] = x := by intro x; simp [B]
  have hzipIdx_add : ∀ (L : List ℝ) (n m : ℕ),
      L.zipIdx (n + m) = (L.zipIdx n).map (fun p => (p.1, p.2 + m)) := by
    intro L n m
    induction L generalizing n m with
    | nil => simp [List.zipIdx]
    | cons hd tl ih =>
      simp only [List.zipIdx, List.map]
      rw [show n + m + 1 = (n + 1) + m from by omega, ih (n + 1) m]
  have hfilter_map : ∀ (M : List (ℝ × ℕ)) (g : ℝ × ℕ → ℝ × ℕ) (q : ℝ × ℕ → Bool),
      (M.map g).filter q = (M.filter (fun p => q (g p))).map g := by
    intro M g q
    induction M with
    | nil => simp
    | cons p M ih => by_cases h : q (g p) <;> simp [List.filter, h, ih]
  have hpar : ∀ k : ℕ, (k + 2) % 2 = k % 2 := by intro k; omega
  have hgetD_cons : ∀ (d : ℝ) (l : List ℝ) (k : ℕ),
      (d :: l).getD (k + 1) 0 = l.getD k 0 := by
    intro d l k
    simp
  have hgetD_zero : ∀ (d : ℝ) (l : List ℝ), (d :: l).getD 0 0 = d := by
    intro d l
    simp
  have hgetD2 : ∀ (k : ℕ) (x y : ℝ) (L : List ℝ),
      (x :: y :: L).getD (k + 2) 0 = L.getD k 0 := by
    intro k x y L
    rw [show k + 2 = (k + 1) + 1 from by omega]
    rw [hgetD_cons x (y :: L) (k + 1), hgetD_cons y L k]
  have hBpair : ∀ (x y : ℝ) (L : List ℝ), B (x :: y :: L) = x - y + B L := by
    intro x y L
    have hz : L.zipIdx (0 + 1 + 1) = (L.zipIdx).map (fun p : ℝ × ℕ => (p.1, p.2 + 2)) := by
      simpa using hzipIdx_add L 0 2
    have hpred : (fun p : ℝ × ℕ => decide (((p.1, p.2 + 2) : ℝ × ℕ).2 % 2 = 0))
        = (fun p : ℝ × ℕ => decide (p.2 % 2 = 0)) := by
      funext p
      rw [show ((p.1, p.2 + 2) : ℝ × ℕ).2 = p.2 + 2 from rfl, hpar (p.2)]
    have hcomp : (fun p : ℝ × ℕ => p.1 - (x :: y :: L).getD (p.2 + 1) 0) ∘
          (fun p : ℝ × ℕ => (p.1, p.2 + 2))
        = (fun p : ℝ × ℕ => p.1 - L.getD (p.2 + 1) 0) := by
      funext p
      show (p.1, p.2 + 2).1 - (x :: y :: L).getD ((p.1, p.2 + 2).2 + 1) 0
        = p.1 - L.getD (p.2 + 1) 0
      rw [show (p.1, p.2 + 2).1 = p.1 from rfl,
        show ((p.1, p.2 + 2) : ℝ × ℕ).2 + 1 = (p.2 + 1) + 2 from by omega,
        hgetD2 (p.2 + 1) x y L]
    have hhead : (x, (0 : ℕ)).1 - (x :: y :: L).getD ((x, (0 : ℕ)).2 + 1) 0 = x - y := by
      have h1 : (x :: y :: L).getD 1 0 = y := by
        rw [show (1 : ℕ) = 0 + 1 from rfl, hgetD_cons x (y :: L) 0, hgetD_zero y L]
      rw [show (x, (0 : ℕ)).1 = x from rfl, show (x, (0 : ℕ)).2 + 1 = 1 from rfl, h1]
    simp only [B, List.zipIdx]
    rw [hz]
    have hfil : List.filter (fun p : ℝ × ℕ => decide (p.2 % 2 = 0))
        ((x, 0) :: (y, 0 + 1) :: List.map (fun p : ℝ × ℕ => (p.1, p.2 + 2)) L.zipIdx)
        = (x, 0) :: List.map (fun p : ℝ × ℕ => (p.1, p.2 + 2))
            (List.filter (fun p : ℝ × ℕ => decide (p.2 % 2 = 0)) L.zipIdx) := by
      simp [List.filter, hfilter_map, hpred]
    rw [hfil]
    simp only [List.map_cons, List.sum_cons, List.map_map, hhead, hcomp]
  have hBcons : ∀ (x : ℝ) (L : List ℝ), B (x :: L) = x - B L := by
    intro x L
    induction L generalizing x with
    | nil => simp [hBsingle x, hBnil]
    | cons y L ih =>
      rw [hBpair x y L, ih y]
      ring
  have hBins : ∀ (l₁ l₂ : List ℝ) (a : ℝ), B (l₁ ++ a :: a :: l₂) = B (l₁ ++ l₂) := by
    intro l₁ l₂ a
    induction l₁ with
    | nil =>
      rw [List.nil_append, List.nil_append, hBcons a (a :: l₂), hBcons a l₂]
      ring
    | cons x l₁ ih =>
      rw [List.cons_append, List.cons_append, hBcons x (l₁ ++ a :: a :: l₂),
        hBcons x (l₁ ++ l₂), ih]
  let big : List ℝ := (l.mergeSort (· ≥ ·)).takeWhile (fun x => a < x)
  let small : List ℝ := (l.mergeSort (· ≥ ·)).dropWhile (fun x => a < x)
  have hTD : big ++ small = l.mergeSort (· ≥ ·) := List.takeWhile_append_dropWhile
  have hleTrans : ∀ x y z : ℝ,
      decide (x ≥ y) = true → decide (y ≥ z) = true → decide (x ≥ z) = true := by
    intro x y z hxy hyz
    simpa using le_trans (show y ≥ z from by simpa using hyz) (show x ≥ y from by simpa using hxy)
  have hleTot : ∀ x y : ℝ, (decide (x ≥ y) || decide (y ≥ x)) = true := by
    intro x y
    rw [Bool.or_eq_true]
    rcases le_total y x with h | h
    · exact Or.inl (by simpa using h)
    · exact Or.inr (by simpa using h)
  have hSsort : ((a :: a :: l).mergeSort (· ≥ ·)).SortedGE := List.sortedGE_mergeSort
  have hTsort : (l.mergeSort (· ≥ ·)).SortedGE := List.sortedGE_mergeSort
  have hSperm : ((a :: a :: l).mergeSort (· ≥ ·)).Perm (a :: a :: l) := List.mergeSort_perm _ _
  have hTperm : (l.mergeSort (· ≥ ·)).Perm l := List.mergeSort_perm _ _
  have hInsSorted : (big ++ a :: a :: small).SortedGE :=
    statopia_math_node_3358436945_300d0d3a (l.mergeSort (· ≥ ·)) a hTsort
  have hComm : ∀ (x y : List ℝ), (x ++ y).Perm (y ++ x) := by
    intro x y
    first
    | exact List.perm_append_comm x y
    | exact List.Perm.append_comm x y
    | exact List.perm_append_comm
    | exact List.Perm.append_comm
  have hInsPerm : (big ++ a :: a :: small).Perm (a :: a :: (l.mergeSort (· ≥ ·))) := by
    rw [← hTD]
    exact (hComm big (a :: a :: small)).trans
      (List.Perm.cons a (List.Perm.cons a (hComm small big)))
  have hSperm' : ((a :: a :: l).mergeSort (· ≥ ·)).Perm (a :: a :: (l.mergeSort (· ≥ ·))) :=
    hSperm.trans ((hTperm.cons a).cons a).symm
  have hEq : (a :: a :: l).mergeSort (· ≥ ·) = big ++ a :: a :: small :=
    List.Perm.eq_of_sortedGE hSsort hInsSorted (hSperm'.trans hInsPerm.symm)
  rw [hEq, hBins, hTD]
  /- @proof-region region.target-node.session.772cf405fa104b51 end -/

end LiuBangXiangYu
