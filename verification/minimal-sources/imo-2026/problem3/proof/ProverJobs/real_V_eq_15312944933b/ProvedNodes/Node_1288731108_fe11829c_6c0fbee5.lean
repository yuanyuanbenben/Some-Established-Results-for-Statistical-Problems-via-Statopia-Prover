import ProverJobs.real_V_eq_15312944933b.Vocabulary
import ProverJobs.real_V_eq_15312944933b.Base

open scoped BigOperators
open LiuBangXiangYu

open scoped BigOperators
namespace LiuBangXiangYu

set_option autoImplicit false in
theorem statopia_math_node_1288731108_fe11829c : ∀ (n : ℕ) (A B : Finset ℝ)
    (hA : AdmissibleMark n A) (hB : AdmissibleMark n B), 0 ≤ L A B := by
  /- @proof-region region.target-node.session.c9cbc4088d1d985d begin -/
  intro n A B hA hB
  classical
  set S : Finset ℝ := A ∪ B with hSdef
  have hSsub : ∀ x ∈ S, x ∈ Set.Ioo (0 : ℝ) 1 := by
    intro x hx
    rw [hSdef] at hx
    simp only [Finset.mem_union] at hx
    rcases hx with hx | hx
    · exact hA.1 hx
    · exact hB.1 hx
  have hsort0 : ∀ x ∈ S.sort (· ≤ ·), (0 : ℝ) ≤ x := by
    intro x hx
    exact le_of_lt (hSsub x ((Finset.mem_sort (α := ℝ) (· ≤ ·)).mp hx)).1
  have hsort1 : ∀ x ∈ S.sort (· ≤ ·), x ≤ 1 := by
    intro x hx
    exact le_of_lt (hSsub x ((Finset.mem_sort (α := ℝ) (· ≤ ·)).mp hx)).2
  have hsPW : (S.sort (· ≤ ·)).Pairwise (· ≤ ·) := by
    have hnd : (S.sort (· ≤ ·)).Nodup := Finset.sort_nodup S (· ≤ ·)
    have htf : (S.sort (· ≤ ·)).toFinset = S := Finset.sort_toFinset S (· ≤ ·)
    have hfix : (S.sort (· ≤ ·)).toFinset.sort (· ≤ ·) = S.sort (· ≤ ·) := by rw [htf]
    exact (List.toFinset_sort (α := ℝ) (· ≤ ·) hnd).mp hfix
  have hlPW : ((0 : ℝ) :: (S.sort (· ≤ ·)) ++ [1]).Pairwise (· ≤ ·) := by
    rw [List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · rw [List.pairwise_cons]
      exact ⟨hsort0, hsPW⟩
    · show ([1] : List ℝ).Pairwise (· ≤ ·)
      simp
    · intro x hx y hy
      have hy1 : y = 1 := by simpa using hy
      rw [hy1]
      have hx' : x = 0 ∨ x ∈ S.sort (· ≤ ·) := by simpa using hx
      rcases hx' with rfl | hx'
      · norm_num
      · exact hsort1 x hx'
  have hzip : ∀ (l : List ℝ), l.Pairwise (· ≤ ·) →
      ∀ x ∈ List.zipWith (fun a b => b - a) l l.tail, 0 ≤ x := by
    intro l
    induction l with
    | nil => intro _ x hx; simp at hx
    | cons a t ih =>
      cases t with
      | nil => intro _ x hx; simp at hx
      | cons b t' =>
        intro hs x hx
        rw [List.pairwise_cons] at hs
        obtain ⟨hle, hst⟩ := hs
        have hab : a ≤ b := hle b (by simp)
        simp only [List.tail_cons, List.zipWith_cons_cons, List.mem_cons] at hx
        rcases hx with h | h
        · rw [h]; linarith
        · exact ih hst x h
  have hpiece : ∀ x ∈ pieceLengths S, 0 ≤ x := by
    intro x hx
    have hx' : x ∈ List.zipWith (fun a b => b - a)
        ((0 : ℝ) :: (S.sort (· ≤ ·)) ++ [1])
        (((0 : ℝ) :: (S.sort (· ≤ ·)) ++ [1]).tail) := by
      simpa only [pieceLengths] using hx
    exact hzip _ hlPW x hx'
  have hshare : ∀ (l₀ : List ℝ), (∀ x ∈ l₀, 0 ≤ x) → 0 ≤ firstPlayerShare l₀ := by
    intro l₀ hl₀
    have hperm : (l₀.mergeSort (· ≥ ·)).Perm l₀ := List.mergeSort_perm l₀ (· ≥ ·)
    have hmem : ∀ x ∈ l₀.mergeSort (· ≥ ·), 0 ≤ x := fun x hx =>
      hl₀ x ((List.Perm.mem_iff hperm).mp hx)
    have hfst : ∀ (l : List ℝ), (l.zipIdx.map Prod.fst) = l := by
      intro l
      induction l with
      | nil => rfl
      | cons a t ih => simp [List.zipIdx, ih]
    have hsub : List.Sublist (((l₀.mergeSort (· ≥ ·)).zipIdx.filter (fun p => p.2 % 2 = 0)).map Prod.fst)
        (l₀.mergeSort (· ≥ ·)) := by
      have h1 : List.Sublist ((l₀.mergeSort (· ≥ ·)).zipIdx.filter (fun p => p.2 % 2 = 0))
          ((l₀.mergeSort (· ≥ ·)).zipIdx) := List.filter_sublist
      have h2 : List.Sublist (((l₀.mergeSort (· ≥ ·)).zipIdx.filter (fun p => p.2 % 2 = 0)).map Prod.fst)
          (((l₀.mergeSort (· ≥ ·)).zipIdx).map Prod.fst) := List.Sublist.map Prod.fst h1
      rwa [hfst] at h2
    have hsum_nn : ∀ (l : List ℝ), (∀ x ∈ l, 0 ≤ x) → 0 ≤ l.sum := by
      intro l
      induction l with
      | nil => intro _; simp
      | cons a t ih =>
        intro h
        have ha : 0 ≤ a := h a (by simp)
        have ht : 0 ≤ t.sum := ih (fun x hx => h x (by simp [hx]))
        simpa using add_nonneg ha ht
    show 0 ≤ (((l₀.mergeSort (· ≥ ·)).zipIdx.filter (fun p => p.2 % 2 = 0)).map Prod.fst).sum
    exact hsum_nn _ (fun y hy => hmem y (hsub.subset hy))
  show 0 ≤ firstPlayerShare (pieceLengths (A ∪ B))
  exact hshare (pieceLengths (A ∪ B)) hpiece
  /- @proof-region region.target-node.session.c9cbc4088d1d985d end -/

end LiuBangXiangYu
