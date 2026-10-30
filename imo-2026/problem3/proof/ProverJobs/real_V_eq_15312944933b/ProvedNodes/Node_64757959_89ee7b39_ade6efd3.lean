import ProverJobs.real_V_eq_15312944933b.Vocabulary
import ProverJobs.real_V_eq_15312944933b.Base
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_258886546_cb96d69f_eaf2fd75
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_2999225285_90342243_ea48111e
open scoped BigOperators
open LiuBangXiangYu

open scoped BigOperators
namespace LiuBangXiangYu

set_option autoImplicit false in
theorem statopia_math_node_64757959_89ee7b39 : ∀ (n : ℕ) (hn : 1 ≤ n) (d : ℝ) (hd : 0 < d)
    (hd1 : d * ((2 : ℝ) ^ (n + 1) - 1) = 1)
    (T : Finset ℝ) (hT : (T : Set ℝ) ⊆ Set.Ioo (0 : ℝ) 1)
    (blocks : List (List ℝ)) (hflat : blocks.flatten = pieceLengths T)
    (hsums : blocks.map (fun b => b.sum) = (List.range (n + 1)).map (fun i => d * (2 : ℝ) ^ i))
    (hcard : T.card ≤ 2 * n),
    (∀ x ∈ pieceLengths T, 0 ≤ x) ∧
    (let xs : List ℝ := (pieceLengths T).mergeSort (· ≥ ·)
     let D : ℝ := ((xs.zipIdx.filter (fun p => p.2 % 2 = 0)).map (fun p => p.1 - xs.getD (p.2 + 1) 0)).sum
     xs.sum = 1 ∧ d ≤ D) := by
  /- @proof-region region.target-node.session.4d0b53d8d55a6549 begin -/
  intro n hn d hd hd1 T hT blocks hflat hsums hcard
  have hpos : ∀ x ∈ pieceLengths T, 0 < x := by
    have hS : ∀ y ∈ T.sort (· ≤ ·), (0:ℝ) < y ∧ y < 1 := by
      intro y hy
      exact hT ((Finset.mem_sort (· ≤ ·)).mp hy)
    have nodup_ne : ∀ (l : List ℝ), l.Nodup → l.Pairwise (· ≠ ·) := by
      intro l
      induction l with
      | nil => intro _; simp
      | cons a t ih =>
        intro h
        rw [List.nodup_cons] at h
        obtain ⟨hnot, hnt⟩ := h
        rw [List.pairwise_cons]
        exact ⟨fun y hy heq => hnot (heq.symm ▸ hy), ih hnt⟩
    have strict_of_le_ne : ∀ (l : List ℝ), l.Pairwise (· ≤ ·) → l.Pairwise (· ≠ ·) →
        l.Pairwise (· < ·) := by
      intro l
      induction l with
      | nil => intro _ _; simp
      | cons a t ih =>
        intro hle hne
        rw [List.pairwise_cons] at hle hne
        obtain ⟨hle1, hle2⟩ := hle
        obtain ⟨hne1, hne2⟩ := hne
        rw [List.pairwise_cons]
        exact ⟨fun y hy => lt_of_le_of_ne (hle1 y hy) (hne1 y hy), ih hle2 hne2⟩
    have hl : ((0:ℝ) :: T.sort (· ≤ ·) ++ [1]).Pairwise (· ≤ ·) := by
      rw [List.pairwise_append]
      refine ⟨?_, ?_, ?_⟩
      · rw [List.pairwise_cons]
        exact ⟨fun y hy => le_of_lt (hS y hy).1, Finset.pairwise_sort T (· ≤ ·)⟩
      · simp
      · rintro a ha b hb
        rw [List.mem_singleton] at hb
        subst hb
        rcases List.mem_cons.mp ha with rfl | haS
        · exact zero_le_one
        · exact le_of_lt (hS a haS).2
    have hne : ((0:ℝ) :: T.sort (· ≤ ·) ++ [1]).Pairwise (· ≠ ·) := by
      rw [List.pairwise_append]
      refine ⟨?_, ?_, ?_⟩
      · rw [List.pairwise_cons]
        exact ⟨fun y hy => ne_of_lt (hS y hy).1,
          nodup_ne _ (Finset.sort_nodup T (· ≤ ·))⟩
      · simp
      · rintro a ha b hb
        rw [List.mem_singleton] at hb
        subst hb
        rcases List.mem_cons.mp ha with rfl | haS
        · exact zero_ne_one
        · exact ne_of_lt (hS a haS).2
    have hlt : ((0:ℝ) :: T.sort (· ≤ ·) ++ [1]).Pairwise (· < ·) :=
      strict_of_le_ne _ hl hne
    have zip_pos : ∀ (l : List ℝ), l.Pairwise (· < ·) →
        ∀ x ∈ List.zipWith (fun a b => b - a) l l.tail, 0 < x := by
      intro l
      induction l with
      | nil => intro _ x hx; simp at hx
      | cons a t ih =>
        intro hpair x hx
        cases t with
        | nil => simp at hx
        | cons b t' =>
          rw [List.pairwise_cons] at hpair
          obtain ⟨hab, hbt⟩ := hpair
          change x ∈ List.zipWith (fun a b => b - a) (a :: b :: t') (b :: t') at hx
          rw [List.zipWith_cons_cons, List.mem_cons] at hx
          rcases hx with rfl | hx
          · have hab' : a < b := hab b (by simp)
            linarith
          · exact ih hbt x hx
    intro x hx
    exact zip_pos ((0:ℝ) :: T.sort (· ≤ ·) ++ [1]) hlt x hx
  have hL : ∀ x ∈ pieceLengths T, 0 ≤ x := fun x hx => le_of_lt (hpos x hx)
  refine ⟨hL, ?_⟩
  dsimp only
  refine ⟨?_, ?_⟩
  · have hflat_sum : ∀ (bs : List (List ℝ)), bs.flatten.sum = (bs.map List.sum).sum := by
      intro bs
      induction bs with
      | nil => simp
      | cons b bs ih =>
        simp [List.flatten_cons, List.sum_append, List.map_cons, List.sum_cons, ih]
    have hgeom : ∀ k : ℕ,
        ((List.range k).map (fun i => d * (2 : ℝ) ^ i)).sum = d * ((2 : ℝ) ^ k - 1) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [List.range_succ, List.map_append, List.sum_append, ih]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, pow_succ]
        ring
    have hperm : ((pieceLengths T).mergeSort (fun x1 x2 => decide (x1 ≥ x2))).sum
        = (pieceLengths T).sum :=
      List.Perm.sum_eq (List.mergeSort_perm (pieceLengths T) (fun x1 x2 => decide (x1 ≥ x2)))
    have hps : (pieceLengths T).sum = 1 := by
      rw [← hflat, hflat_sum blocks, hsums, hgeom (n + 1)]
      exact hd1
    exact hperm.trans hps
  · set Ls : List ℝ := (pieceLengths T).mergeSort (· ≥ ·) with hLs
    have hsplit : ∀ (srt : List ℝ),
        ((srt.zipIdx.filter (fun p => p.2 % 2 = 0)).map (fun p => p.1 - srt.getD (p.2 + 1) 0)).sum
          = (∑ j ∈ Finset.range ((srt.length + 1) / 2),
              ((if h : 2 * j < srt.length then srt.get ⟨2 * j, h⟩ else 0)
                - (if h : 2 * j + 1 < srt.length then srt.get ⟨2 * j + 1, h⟩ else 0))) := by
      intro srt
      have hbr : ∀ (k : ℕ) (f : ℕ → ℝ),
          (∑ j ∈ Finset.range k, f j) = ((List.range k).map f).sum := fun k f => rfl
      have hdiv2 : ∀ n : ℕ, (n + 2) / 2 = n / 2 + 1 := by intro n; omega
      have hpar : ∀ k : ℕ, ((k + 1) % 2 = 0) ↔ (k % 2 = 1) := by intro k; omega
      have hgetD : ∀ (l : List ℝ) (n : ℕ),
          l.getD n 0 = if h : n < l.length then l.get ⟨n, h⟩ else 0 := by
        intro l
        induction l with
        | nil => intro n; simp
        | cons a t ih =>
          intro n
          cases n with
          | zero =>
            rw [List.getD_cons_zero, dif_pos (by simp)]
            simp
          | succ n =>
            rw [List.getD_cons_succ, ih n]
            by_cases h : n < t.length
            · rw [dif_pos h, dif_pos (by simp [h])]
              simp
            · rw [dif_neg h, dif_neg (by simp [h])]
      have hkey : ∀ (l : List ℝ) (k : ℕ),
          (l.zipIdx k).filter (fun p => p.2 % 2 = 0) =
            (if k % 2 = 0
              then (List.range ((l.length + 1) / 2)).map (fun i => (l.getD (2 * i) 0, k + 2 * i))
              else (List.range (l.length / 2)).map (fun i => (l.getD (2 * i + 1) 0, k + 2 * i + 1))) := by
        intro l
        induction l with
        | nil => intro k; simp
        | cons a t ih =>
          intro k
          by_cases hk : k % 2 = 0
          · have hk1 : ¬ (k + 1) % 2 = 0 := by omega
            have hcnt : ((t.length + 1) + 1) / 2 = t.length / 2 + 1 := hdiv2 t.length
            have hfil : ((a, k) :: t.zipIdx (k + 1)).filter (fun p => p.2 % 2 = 0)
                = (a, k) :: (t.zipIdx (k + 1)).filter (fun p => p.2 % 2 = 0) := by
              simp [hk]
            have hA : ∀ i : ℕ, (k + 1) + 2 * i + 1 = k + 2 * (i + 1) := fun i => by omega
            have hg : ∀ i : ℕ, 2 * (i + 1) = 2 * i + 1 + 1 := fun i => by omega
            have hcomp : ((fun i : ℕ => ((a :: t).getD (2 * i) 0, k + 2 * i)) ∘ Nat.succ)
                = (fun i : ℕ => (t.getD (2 * i + 1) 0, k + (2 * i + 1 + 1))) := by
              funext i
              simp only [Function.comp_apply, Nat.succ_eq_add_one, hg]
              rw [List.getD_cons_succ]
            rw [List.zipIdx_cons, hfil, ih (k + 1), if_neg hk1, if_pos hk, List.length_cons,
              hcnt, List.range_succ_eq_map, List.map_cons, List.map_map]
            simp only [List.getD_cons_zero, Nat.mul_zero, Nat.add_zero, hg, hA]
            rw [hcomp]
          · have hk1 : (k + 1) % 2 = 0 := by omega
            have hfil : ((a, k) :: t.zipIdx (k + 1)).filter (fun p => p.2 % 2 = 0)
                = (t.zipIdx (k + 1)).filter (fun p => p.2 % 2 = 0) := by
              simp [hk]
            have hB : ∀ i : ℕ, (k + 1) + 2 * i = k + 2 * i + 1 := fun i => by omega
            rw [List.zipIdx_cons, hfil, ih (k + 1), if_pos hk1, if_neg hk]
            simp only [List.length_cons, List.getD_cons_succ, hB]
      have hD : ((srt.zipIdx.filter (fun p => p.2 % 2 = 0)).map (fun p => p.1 - srt.getD (p.2 + 1) 0)).sum
          = (∑ j ∈ Finset.range ((srt.length + 1) / 2),
              ((if h : 2 * j < srt.length then srt.get ⟨2 * j, h⟩ else 0)
                - (if h : 2 * j + 1 < srt.length then srt.get ⟨2 * j + 1, h⟩ else 0))) := by
        have hC : (fun p : ℝ × ℕ => p.1 - srt.getD (p.2 + 1) 0) ∘
              (fun i : ℕ => (srt.getD (2 * i) 0, 0 + 2 * i))
            = fun i : ℕ => (if h : 2 * i < srt.length then srt.get ⟨2 * i, h⟩ else 0)
                - (if h : 2 * i + 1 < srt.length then srt.get ⟨2 * i + 1, h⟩ else 0) := by
          funext i
          simp only [Function.comp_apply, hgetD, Nat.zero_add]
        rw [hkey srt 0, if_pos (by decide), List.map_map, hC]
        exact (hbr ((srt.length + 1) / 2) _).symm
      exact hD
    have hmain : (∑ j ∈ Finset.range ((Ls.length + 1) / 2),
        ((if h : 2 * j < Ls.length then Ls.get ⟨2 * j, h⟩ else 0)
          - (if h : 2 * j + 1 < Ls.length then Ls.get ⟨2 * j + 1, h⟩ else 0))) ≥ d := by
      have hL : ((0:ℝ) :: T.sort (· ≤ ·) ++ [1]).length = T.card + 2 := by
        simp only [List.length_append, List.length_cons, List.length_nil,
          Finset.length_sort]
      have hlen : (pieceLengths T).length = T.card + 1 := by
        change (List.zipWith (fun a b => b - a) ((0:ℝ) :: T.sort (· ≤ ·) ++ [1])
          (((0:ℝ) :: T.sort (· ≤ ·) ++ [1]).tail)).length = T.card + 1
        rw [List.length_zipWith, List.length_tail, hL]
        omega
      have hm_le : (pieceLengths T).length ≤ 2 * n + 1 := by omega
      have hchild := statopia_math_node_258886546_cb96d69f n hn d hd (pieceLengths T)
        hpos blocks hflat hsums hm_le
      rw [hLs]
      exact hchild
    rw [hsplit Ls]
    exact hmain
  /- @proof-region region.target-node.session.4d0b53d8d55a6549 end -/

end LiuBangXiangYu
