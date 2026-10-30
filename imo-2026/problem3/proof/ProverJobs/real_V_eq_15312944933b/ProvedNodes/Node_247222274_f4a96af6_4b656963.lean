import ProverJobs.real_V_eq_15312944933b.Vocabulary
import ProverJobs.real_V_eq_15312944933b.Base
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_1153730635_3a67f9ee_6853e7b7
open scoped BigOperators
open LiuBangXiangYu

open scoped BigOperators
namespace LiuBangXiangYu

set_option autoImplicit false in
theorem statopia_math_node_247222274_f4a96af6 : ∀ (L : List ℝ) (hL : ∀ x ∈ L, 0 ≤ x),
    let xs : List ℝ := L.mergeSort (· ≥ ·)
    let O : ℝ := ((xs.zipIdx.filter (fun p => p.2 % 2 = 0)).map (fun p => p.1)).sum
    let E : ℝ := ((xs.zipIdx.filter (fun p => p.2 % 2 = 1)).map (fun p => p.1)).sum
    let D : ℝ :=
      ((xs.zipIdx.filter (fun p => p.2 % 2 = 0)).map (fun p => p.1 - xs.getD (p.2 + 1) 0)).sum
    let S : ℝ := xs.sum
    firstPlayerShare L = O ∧
    O - E = D ∧
    (∀ p ∈ xs.zipIdx.filter (fun p => p.2 % 2 = 0),
      0 ≤ p.1 - xs.getD (p.2 + 1) 0) ∧
    0 ≤ D ∧
    D = ((xs.zipIdx.filter (fun p => p.2 % 2 = 0)).map
          (fun p => |p.1 - xs.getD (p.2 + 1) 0|)).sum ∧
    O + E = S ∧
    O = (S + D) / 2 ∧
    (S = 1 → firstPlayerShare L = (1 + D) / 2 ∧ 0 ≤ firstPlayerShare L ∧ firstPlayerShare L ≤ 1) := by
  /- @proof-region region.target-node.session.80db2ffaca5b9f76 begin -/
  intro L hL
  have hpair : (L.mergeSort (· ≥ ·)).Pairwise (fun a b => a ≥ b) := by
    have hs0 : (L.mergeSort (fun x1 x2 : ℝ => decide (x1 ≥ x2))).Pairwise
        (fun a b => decide (a ≥ b) = true) := by
      apply List.pairwise_mergeSort (l := L) (le := fun x1 x2 : ℝ => decide (x1 ≥ x2))
      · intro a b c hab hbc
        simp only [decide_eq_true_eq] at hab hbc ⊢
        linarith
      · intro a b
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        rcases le_total b a with h | h
        · exact Or.inl h
        · exact Or.inr h
    simpa only [decide_eq_true_eq] using hs0
  have hnn : ∀ x ∈ L.mergeSort (· ≥ ·), 0 ≤ x := by
    intro x hx
    exact hL x ((List.mergeSort_perm L (fun x1 x2 : ℝ => decide (x1 ≥ x2))).subset hx)
  have key := statopia_math_node_1153730635_3a67f9ee (L.mergeSort (· ≥ ·)) hpair hnn
  simp only [] at key
  obtain ⟨h2, h3, h4, h5, h6, h7, h8⟩ := key
  simp only [firstPlayerShare]
  refine ⟨trivial, h2, h3, h4, h5, h6, h7, ?_⟩
  intro hS
  exact ⟨by rw [h7, hS], (h8 hS).1, (h8 hS).2⟩
  /- @proof-region region.target-node.session.80db2ffaca5b9f76 end -/

end LiuBangXiangYu
