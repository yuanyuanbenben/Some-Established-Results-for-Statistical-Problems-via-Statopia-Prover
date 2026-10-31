import ProverJobs.real_V_eq_15312944933b.Vocabulary
import ProverJobs.real_V_eq_15312944933b.Base

open scoped BigOperators
open LiuBangXiangYu

open scoped BigOperators
namespace LiuBangXiangYu

set_option autoImplicit false in
theorem statopia_math_node_3358436945_300d0d3a : ∀ (T : List ℝ) (a : ℝ) (hT : T.SortedGE),
    (T.takeWhile (fun x => decide (a < x)) ++ a :: a :: T.dropWhile (fun x => decide (a < x))).SortedGE := by
  /- @proof-region region.target-node.session.21ec8ef5d2e94d48 begin -/
  intro T a hT
  let p : ℝ → Bool := fun x => decide (a < x)
  have hPW : T.Pairwise (fun x y : ℝ => x ≥ y) := by
    rw [List.pairwise_iff_get]
    intro i j hij
    exact hT (le_of_lt hij)
  have htake_mem : ∀ x ∈ T.takeWhile p, a < x := by
    have aux : ∀ (l : List ℝ) (x : ℝ), x ∈ l.takeWhile p → a < x := by
      intro l
      induction l with
      | nil => intro x hx; simp at hx
      | cons y ys ih =>
        intro x hx
        simp only [List.takeWhile] at hx
        split at hx
        · rename_i hy
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx'
          · exact of_decide_eq_true hy
          · exact ih x hx'
        · exact absurd hx (by simp)
    exact aux T
  have hdrop_mem : ∀ x ∈ T.dropWhile p, x ≤ a := by
    have aux : ∀ (l : List ℝ), l.Pairwise (fun x y : ℝ => x ≥ y) →
        ∀ x ∈ l.dropWhile p, x ≤ a := by
      intro l
      induction l with
      | nil => intro _ x hx; simp at hx
      | cons y ys ih =>
        intro hpw x hx
        simp only [List.dropWhile] at hx
        split at hx
        · rename_i hy
          exact ih (List.pairwise_cons.mp hpw).2 x hx
        · rename_i hy
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx'
          · exact le_of_not_gt (of_decide_eq_false hy)
          · have hyx : x ≤ y := (List.pairwise_cons.mp hpw).1 x hx'
            have hya : y ≤ a := le_of_not_gt (of_decide_eq_false hy)
            exact le_trans hyx hya
    exact aux T hPW
  have hsplit : (T.takeWhile p).Pairwise (fun x y : ℝ => x ≥ y) ∧
      (T.dropWhile p).Pairwise (fun x y : ℝ => x ≥ y) ∧
      (∀ x ∈ T.takeWhile p, ∀ y ∈ T.dropWhile p, x ≥ y) := by
    have h : (T.takeWhile p ++ T.dropWhile p).Pairwise (fun x y : ℝ => x ≥ y) := by
      rw [List.takeWhile_append_dropWhile]
      exact hPW
    exact List.pairwise_append.mp h
  have hW : (T.takeWhile p ++ a :: a :: T.dropWhile p).Pairwise (fun x y : ℝ => x ≥ y) := by
    rw [List.pairwise_append]
    refine ⟨hsplit.1, ?_, ?_⟩
    · rw [List.pairwise_cons]
      refine ⟨?_, ?_⟩
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy'
        · exact le_refl _
        · exact hdrop_mem y hy'
      · rw [List.pairwise_cons]
        exact ⟨fun y hy => hdrop_mem y hy, hsplit.2.1⟩
    · intro x hx y hy
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact le_of_lt (htake_mem x hx)
      · rcases List.mem_cons.mp hy' with rfl | hy''
        · exact le_of_lt (htake_mem x hx)
        · exact hsplit.2.2 x hx y hy''
  have hms : (T.takeWhile p ++ a :: a :: T.dropWhile p).mergeSort
        (fun x1 x2 : ℝ => decide (x1 ≥ x2)) = T.takeWhile p ++ a :: a :: T.dropWhile p :=
    List.mergeSort_eq_self (fun x1 x2 : ℝ => x1 ≥ x2) hW
  have hfinal : (T.takeWhile p ++ a :: a :: T.dropWhile p).SortedGE := by
    have h := List.sortedGE_mergeSort (l := T.takeWhile p ++ a :: a :: T.dropWhile p)
    rw [hms] at h
    exact h
  exact hfinal
  /- @proof-region region.target-node.session.21ec8ef5d2e94d48 end -/

end LiuBangXiangYu
