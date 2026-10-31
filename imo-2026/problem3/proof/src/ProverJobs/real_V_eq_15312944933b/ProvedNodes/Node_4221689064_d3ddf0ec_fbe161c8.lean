import ProverJobs.real_V_eq_15312944933b.Vocabulary
import ProverJobs.real_V_eq_15312944933b.Base
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_1499306708_29a62a2a_c3ee751f
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_4187789835_5e30027a_b70d8f47
open scoped BigOperators
open LiuBangXiangYu

open scoped BigOperators
namespace LiuBangXiangYu

set_option autoImplicit false in
theorem statopia_math_node_4221689064_d3ddf0ec : ∀ (S : Finset ℝ) (hS : (S : Set ℝ) ⊆ Set.Ioo (0 : ℝ) 1)
    (s : ℕ → ℝ) (hs0 : s 0 = 0) (hs1 : s (S.card + 1) = 1)
    (hs_mono : StrictMonoOn s (Set.Icc 0 (S.card + 1)))
    (hs_int : (S : Set ℝ) = s '' Set.Icc 1 S.card),
    (pieceLengths S = (List.range (S.card + 1)).map (fun i => s (i + 1) - s i)) ∧
    (pieceLengths S).length = S.card + 1 ∧
    (∀ x ∈ pieceLengths S, 0 < x) ∧
    (pieceLengths S).sum = 1 ∧
    (∀ (T : Finset ℝ), S ⊆ T → (T : Set ℝ) ⊆ Set.Ioo (0 : ℝ) 1 →
      ∃ blocks : List (List ℝ),
        blocks.flatten = pieceLengths T ∧ blocks.map (fun b => b.sum) = pieceLengths S) ∧
    (∀ (q : ℕ) (t : ℕ → ℝ),
      1 ≤ q →
      t 0 = 0 → t q = 1 →
      StrictMonoOn t (Set.Icc 0 q) →
      (∀ i, 1 ≤ i → i < q → t i ∈ Set.Ioo (0 : ℝ) 1) →
      (S : Set ℝ) = t '' Set.Icc 1 (q - 1) →
      pieceLengths S = (List.range q).map (fun i => t (i + 1) - t i)) := by
  /- @proof-region region.target-node.session.02b6f2176ba1f85b begin -/
  intro S hS s hs0 hs1 hs_mono hs_int
  classical
  have hint : ∀ i, 1 ≤ i → i < S.card + 1 → s i ∈ Set.Ioo (0 : ℝ) 1 := by
    intro i hi1 hi2
    have hi : i ∈ Set.Icc 1 S.card := by simp only [Set.mem_Icc]; omega
    have hmem : s i ∈ s '' Set.Icc 1 S.card := ⟨i, hi, rfl⟩
    rw [← hs_int] at hmem
    exact hS hmem
  have hpiece1 : pieceLengths S = (List.range (S.card + 1)).map (fun i => s (i + 1) - s i) :=
    statopia_math_node_4187789835_5e30027a S (S.card + 1) s (by omega) hs0 hs1 hs_mono hint hs_int
  have hlen : (pieceLengths S).length = S.card + 1 := by
    rw [hpiece1, List.length_map, List.length_range]
  have hsum : (pieceLengths S).sum = 1 := by
    rw [hpiece1]
    have htel : ∀ n : ℕ,
        (List.map (fun i => s (i + 1) - s i) (List.range n)).sum = s n - s 0 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [List.sum_range_succ, ih]
        show (s n - s 0) + (s (n + 1) - s n) = s (n + 1) - s 0
        ring
    rw [htel (S.card + 1), hs1, hs0]
    norm_num
  have hpos : ∀ x ∈ pieceLengths S, 0 < x := by
    intro x hx
    rw [hpiece1] at hx
    obtain ⟨i, hi, hix⟩ := List.mem_map.mp hx
    rw [List.mem_range] at hi
    rw [← hix]
    show (0 : ℝ) < s (i + 1) - s i
    have h1 : i ∈ Set.Icc (0 : ℕ) (S.card + 1) := by simp only [Set.mem_Icc]; omega
    have h2 : i + 1 ∈ Set.Icc (0 : ℕ) (S.card + 1) := by simp only [Set.mem_Icc]; omega
    have h3 : s i < s (i + 1) := hs_mono h1 h2 (by omega)
    linarith
  refine ⟨hpiece1, hlen, hpos, hsum, ?_, ?_⟩
  · intro T hST hT
    exact statopia_math_node_1499306708_29a62a2a S T hST hT
  · intro q t hq ht0 htq hmono hint' hS'
    exact statopia_math_node_4187789835_5e30027a S q t hq ht0 htq hmono hint' hS'
  /- @proof-region region.target-node.session.02b6f2176ba1f85b end -/

end LiuBangXiangYu
