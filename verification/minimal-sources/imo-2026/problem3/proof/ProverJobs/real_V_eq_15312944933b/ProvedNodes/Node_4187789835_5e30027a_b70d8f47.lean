import ProverJobs.real_V_eq_15312944933b.Vocabulary
import ProverJobs.real_V_eq_15312944933b.Base

open scoped BigOperators
open LiuBangXiangYu

open scoped BigOperators
namespace LiuBangXiangYu

set_option autoImplicit false in
theorem statopia_math_node_4187789835_5e30027a : ∀ (S : Finset ℝ) (q : ℕ) (t : ℕ → ℝ)
    (hq : 1 ≤ q) (ht0 : t 0 = 0) (htq : t q = 1)
    (hmono : StrictMonoOn t (Set.Icc 0 q))
    (hint : ∀ i, 1 ≤ i → i < q → t i ∈ Set.Ioo (0 : ℝ) 1)
    (hS : (S : Set ℝ) = t '' Set.Icc 1 (q - 1)),
    pieceLengths S = (List.range q).map (fun i => t (i + 1) - t i) := by
  /- @proof-region region.target-node.session.f563345be5d4fb75 begin -/
  intro S q t hq ht0 htq hmono hint hS
  set n : ℕ := q - 1 with hn
  have hnq : n + 1 = q := by omega
  set ls : List ℝ := (List.range n).map (fun i => t (i + 1)) with hls
  have hmono_range : ∀ (m : ℕ) (g : ℕ → ℝ) (R : ℝ → ℝ → Prop),
      (∀ a b, a < b → b < m → R (g a) (g b)) → ((List.range m).map g).Pairwise R := by
    intro m
    induction m with
    | zero => intro g R _; exact List.Pairwise.nil
    | succ m ih =>
      intro g R hR
      rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.pairwise_cons]
      exact ⟨fun b hb => by
        rw [List.mem_map] at hb
        obtain ⟨i, hi, rfl⟩ := hb
        rw [List.mem_range] at hi
        exact hR 0 (Nat.succ i) (Nat.succ_pos i) (by omega),
        ih (g ∘ Nat.succ) R (fun a b hab hb => hR (Nat.succ a) (Nat.succ b) (by omega) (by omega))⟩
  have hmonoI : ∀ a b, a < b → b < n → t (a + 1) < t (b + 1) := by
    intro a b hab hb
    exact hmono (by simp only [Set.mem_Icc]; omega) (by simp only [Set.mem_Icc]; omega) (by omega)
  have hnodup : ls.Nodup := by
    rw [hls]
    exact hmono_range n (fun i => t (i + 1)) (· ≠ ·) (fun a b hab hb => ne_of_lt (hmonoI a b hab hb))
  have hpair : ls.Pairwise (· ≤ ·) := by
    rw [hls]
    exact hmono_range n (fun i => t (i + 1)) (· ≤ ·) (fun a b hab hb => le_of_lt (hmonoI a b hab hb))
  have hfinset : ls.toFinset = S := by
    ext x
    rw [List.mem_toFinset, hls, List.mem_map, ← Finset.mem_coe, hS]
    constructor
    · rintro ⟨i, hi, hix⟩
      rw [List.mem_range] at hi
      exact ⟨i + 1, by simp only [Set.mem_Icc]; omega, hix⟩
    · rintro ⟨j, hj, hjx⟩
      rw [Set.mem_Icc] at hj
      obtain ⟨hj1, hj2⟩ := hj
      refine ⟨j - 1, ?_, ?_⟩
      · rw [List.mem_range]; omega
      · show t ((j - 1) + 1) = x
        rw [Nat.sub_add_cancel hj1, hjx]
  have hsort : S.sort (· ≤ ·) = ls := by
    have h := (List.toFinset_sort (· ≤ ·) (l := ls) hnodup).mpr hpair
    rwa [hfinset] at h
  have hrange_map : ∀ (M : ℕ) (h : ℕ → ℝ),
      (List.range (M + 1)).map h = h 0 :: (List.range M).map (fun i => h (i + 1)) := by
    intro M h
    have hcomp : (h ∘ Nat.succ) = fun i => h (i + 1) := by
      funext i; simp [Function.comp_apply, Nat.succ_eq_add_one]
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, hcomp]
  have hZgen : ∀ (N : ℕ) (g : ℕ → ℝ),
      List.zipWith (fun a b => b - a) (g 0 :: (List.range N).map (fun i => g (i + 1)))
        ((List.range N).map (fun i => g (i + 1))) = (List.range N).map (fun i => g (i + 1) - g i) := by
    intro N
    induction N with
    | zero => intro g; rfl
    | succ N ih =>
      intro g
      rw [hrange_map N (fun i => g (i + 1)), hrange_map N (fun i => g (i + 1) - g i),
        List.zipWith_cons_cons, ih (fun i => g (i + 1))]
  have hZ : ∀ (N : ℕ) (g : ℕ → ℝ),
      List.zipWith (fun a b => b - a) ((List.range (N + 1)).map g) ((List.range N).map (fun i => g (i + 1)))
        = (List.range N).map (fun i => g (i + 1) - g i) := by
    intro N g
    rw [hrange_map N g]
    exact hZgen N g
  have hg1 : t (n + 1) = 1 := by rw [hnq, htq]
  have hLt' : ls ++ [1] = (List.range q).map (fun i => t (i + 1)) := by
    rw [hls, ← hnq, List.range_succ, List.map_append, List.map_cons, List.map_nil, hg1]
  have hL : ((0 : ℝ) :: S.sort (· ≤ ·)) ++ [1] = (List.range (q + 1)).map t := by
    rw [hsort, List.cons_append, hLt', List.range_succ_eq_map, List.map_cons, List.map_map, ht0]
    congr 1
  have htail : (((0 : ℝ) :: S.sort (· ≤ ·)) ++ [1]).tail = (List.range q).map (fun i => t (i + 1)) := by
    rw [List.cons_append, List.tail_cons, hsort, hLt']
  change List.zipWith (fun a b => b - a) (((0 : ℝ) :: S.sort (· ≤ ·)) ++ [1])
      ((((0 : ℝ) :: S.sort (· ≤ ·)) ++ [1]).tail) = (List.range q).map (fun i => t (i + 1) - t i)
  rw [htail, hL]
  exact hZ q t
  /- @proof-region region.target-node.session.f563345be5d4fb75 end -/

end LiuBangXiangYu
