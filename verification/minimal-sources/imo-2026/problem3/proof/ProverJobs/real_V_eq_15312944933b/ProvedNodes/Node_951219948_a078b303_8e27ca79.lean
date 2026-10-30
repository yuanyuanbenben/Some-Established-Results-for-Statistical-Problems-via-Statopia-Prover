import ProverJobs.real_V_eq_15312944933b.Vocabulary
import ProverJobs.real_V_eq_15312944933b.Base

open scoped BigOperators
open LiuBangXiangYu

open scoped BigOperators
namespace LiuBangXiangYu

set_option autoImplicit false in
theorem statopia_math_node_951219948_a078b303 : ∀ (A : Finset ℝ)
    (hA : (A : Set ℝ) ⊆ Set.Ioo (0 : ℝ) 1),
    ∃ s : ℕ → ℝ, s 0 = 0 ∧ s (A.card + 1) = 1 ∧
      StrictMonoOn s (Set.Icc 0 (A.card + 1)) ∧
      (A : Set ℝ) = s '' Set.Icc 1 A.card := by
  /- @proof-region region.target-node.session.76f346ea5ec9834d begin -/
  intro A hA
  classical
  have hmem : ∀ x ∈ A, (0:ℝ) < x ∧ x < 1 := fun x hx => hA hx
  have h0A : (0:ℝ) ∉ A := fun h => (lt_irrefl (0:ℝ)) (hmem 0 h).1
  have h1A : (1:ℝ) ∉ A := fun h => (lt_irrefl (1:ℝ)) (hmem 1 h).2
  set B : Finset ℝ := insert (0:ℝ) (insert (1:ℝ) A) with hBdef
  have h0_notin : (0:ℝ) ∉ insert (1:ℝ) A := by
    rw [Finset.mem_insert, not_or]
    exact ⟨by norm_num, h0A⟩
  have hBcard : B.card = A.card + 2 := by
    rw [hBdef, Finset.card_insert_of_notMem h0_notin, Finset.card_insert_of_notMem h1A]
  have h0B : (0:ℝ) ∈ B := by rw [hBdef]; exact Finset.mem_insert_self _ _
  have h1B : (1:ℝ) ∈ B := by
    rw [hBdef]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hBmin : ∀ b ∈ B, (0:ℝ) ≤ b := by
    intro b hb
    simp only [hBdef, Finset.mem_insert] at hb
    rcases hb with rfl | rfl | hbA
    · exact le_refl 0
    · norm_num
    · exact le_of_lt (hmem b hbA).1
  have hBmax : ∀ b ∈ B, b ≤ (1:ℝ) := by
    intro b hb
    simp only [hBdef, Finset.mem_insert] at hb
    rcases hb with rfl | rfl | hbA
    · norm_num
    · exact le_refl 1
    · exact le_of_lt (hmem b hbA).2
  let e := B.orderIsoOfFin hBcard
  have he0 : ∀ (hk : 0 < A.card + 2), ((e ⟨0, hk⟩ : ↥B) : ℝ) = 0 := by
    intro hk
    apply le_antisymm
    · have h : e ⟨0, hk⟩ ≤ (⟨(0:ℝ), h0B⟩ : ↥B) := by
        rw [← e.apply_symm_apply (⟨(0:ℝ), h0B⟩ : ↥B)]
        exact e.strictMono.monotone (Fin.zero_le _)
      exact h
    · exact hBmin _ (e ⟨0, hk⟩).2
  have he1 : ∀ (hk : A.card + 1 < A.card + 2),
      ((e ⟨A.card + 1, hk⟩ : ↥B) : ℝ) = 1 := by
    intro hk
    apply le_antisymm
    · exact hBmax _ (e ⟨A.card + 1, hk⟩).2
    · have h : (⟨(1:ℝ), h1B⟩ : ↥B) ≤ e ⟨A.card + 1, hk⟩ := by
        rw [← e.apply_symm_apply (⟨(1:ℝ), h1B⟩ : ↥B)]
        apply e.strictMono.monotone
        show (e.symm (⟨(1:ℝ), h1B⟩ : ↥B)).val ≤ A.card + 1
        have := (e.symm (⟨(1:ℝ), h1B⟩ : ↥B)).isLt
        omega
      exact h
  let s : ℕ → ℝ := fun k => if hk : k < A.card + 2 then ((e ⟨k, hk⟩ : ↥B) : ℝ) else 0
  have hs0 : s 0 = 0 := by
    have hk0 : 0 < A.card + 2 := by omega
    change (if hk : (0:ℕ) < A.card + 2 then ((e ⟨0, hk⟩ : ↥B) : ℝ) else 0) = 0
    rw [dif_pos hk0]
    exact he0 hk0
  have hs1 : s (A.card + 1) = 1 := by
    have hk1 : A.card + 1 < A.card + 2 := by omega
    change (if hk : A.card + 1 < A.card + 2 then
      ((e ⟨A.card + 1, hk⟩ : ↥B) : ℝ) else 0) = 1
    rw [dif_pos hk1]
    exact he1 hk1
  have hsmono : StrictMonoOn s (Set.Icc 0 (A.card + 1)) := by
    intro i hi j hj hij
    rw [Set.mem_Icc] at hi hj
    have hi2 : i < A.card + 2 := by omega
    have hj2 : j < A.card + 2 := by omega
    change (if hk : i < A.card + 2 then ((e ⟨i, hk⟩ : ↥B) : ℝ) else 0) <
      (if hk : j < A.card + 2 then ((e ⟨j, hk⟩ : ↥B) : ℝ) else 0)
    rw [dif_pos hi2, dif_pos hj2]
    exact e.strictMono hij
  have himage : (A : Set ℝ) = s '' Set.Icc 1 A.card := by
    ext x
    constructor
    · intro hxA
      have hxB : x ∈ B := by
        rw [hBdef]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hxA)
      obtain ⟨j, hj⟩ := e.surjective (⟨x, hxB⟩ : ↥B)
      have hx0 : (0:ℝ) < x := (hmem x hxA).1
      have hx1 : x < (1:ℝ) := (hmem x hxA).2
      have hge : 1 ≤ j.val := by
        by_contra hlt
        rw [not_le] at hlt
        have hj0 : j.val = 0 := by omega
        have hjEq : j = (⟨0, by omega⟩ : Fin (A.card + 2)) := Fin.ext hj0
        have hzero : ((e j : ↥B) : ℝ) = 0 := by
          rw [hjEq]; exact he0 _
        rw [hj] at hzero
        exact absurd hzero (ne_of_gt hx0)
      have hle : j.val ≤ A.card := by
        by_contra hlt
        rw [not_le] at hlt
        have hjv : j.val = A.card + 1 := by have := j.isLt; omega
        have hjEq : j = (⟨A.card + 1, by omega⟩ : Fin (A.card + 2)) := Fin.ext hjv
        have hone : ((e j : ↥B) : ℝ) = 1 := by
          rw [hjEq]; exact he1 _
        rw [hj] at hone
        exact absurd hone (ne_of_lt hx1)
      refine ⟨j.val, Set.mem_Icc.mpr ⟨hge, hle⟩, ?_⟩
      have hjb : j.val < A.card + 2 := j.isLt
      have hsk : s j.val = ((e ⟨j.val, hjb⟩ : ↥B) : ℝ) := by
        change (if hk : j.val < A.card + 2 then
          ((e ⟨j.val, hk⟩ : ↥B) : ℝ) else 0) = ((e ⟨j.val, hjb⟩ : ↥B) : ℝ)
        rw [dif_pos hjb]
      rw [hsk]
      have hfin : (⟨j.val, hjb⟩ : Fin (A.card + 2)) = j := rfl
      rw [hfin, hj]
    · rintro ⟨k, hk, rfl⟩
      rw [Set.mem_Icc] at hk
      have hkB : k < A.card + 2 := by omega
      have hsk : s k = ((e ⟨k, hkB⟩ : ↥B) : ℝ) := by
        change (if hk : k < A.card + 2 then
          ((e ⟨k, hk⟩ : ↥B) : ℝ) else 0) = ((e ⟨k, hkB⟩ : ↥B) : ℝ)
        rw [dif_pos hkB]
      rw [hsk]
      have hmemB := (e ⟨k, hkB⟩).2
      have hne0 : ((e ⟨k, hkB⟩ : ↥B) : ℝ) ≠ 0 := by
        intro h
        have heq : e (⟨k, hkB⟩ : Fin (A.card + 2)) =
            e (⟨0, by omega⟩ : Fin (A.card + 2)) := by
          apply Subtype.ext
          rw [h, he0 (by omega)]
        have hval := congrArg Fin.val (e.injective heq)
        have : k = 0 := by simpa using hval
        omega
      have hne1 : ((e ⟨k, hkB⟩ : ↥B) : ℝ) ≠ 1 := by
        intro h
        have heq : e (⟨k, hkB⟩ : Fin (A.card + 2)) =
            e (⟨A.card + 1, by omega⟩ : Fin (A.card + 2)) := by
          apply Subtype.ext
          rw [h, he1 (by omega)]
        have hval := congrArg Fin.val (e.injective heq)
        have : k = A.card + 1 := by simpa using hval
        omega
      have hcl : ((e ⟨k, hkB⟩ : ↥B) : ℝ) = 0 ∨ ((e ⟨k, hkB⟩ : ↥B) : ℝ) = 1 ∨
          ((e ⟨k, hkB⟩ : ↥B) : ℝ) ∈ A := by
        simpa only [hBdef, Finset.mem_insert, Finset.mem_singleton] using hmemB
      rcases hcl with h | h | h
      · exact absurd h hne0
      · exact absurd h hne1
      · exact h
  exact ⟨s, hs0, hs1, hsmono, himage⟩
  /- @proof-region region.target-node.session.76f346ea5ec9834d end -/

end LiuBangXiangYu
