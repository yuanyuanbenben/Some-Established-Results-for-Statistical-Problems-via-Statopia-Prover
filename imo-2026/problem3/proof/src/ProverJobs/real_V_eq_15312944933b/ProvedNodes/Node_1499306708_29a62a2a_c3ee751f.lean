import ProverJobs.real_V_eq_15312944933b.Vocabulary
import ProverJobs.real_V_eq_15312944933b.Base
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_1162978405_2cbda557_cccee682
open scoped BigOperators
open LiuBangXiangYu

open scoped BigOperators
namespace LiuBangXiangYu

set_option autoImplicit false in
theorem statopia_math_node_1499306708_29a62a2a : ∀ (S T : Finset ℝ) (hST : S ⊆ T)
    (hT : (T : Set ℝ) ⊆ Set.Ioo (0 : ℝ) 1),
    ∃ blocks : List (List ℝ), blocks.flatten = pieceLengths T ∧
      blocks.map (fun b => b.sum) = pieceLengths S := by
  /- @proof-region region.target-node.session.73890eceb3172b83 begin -/
  intro S T hST hT
  classical
  have range_split : ∀ (m n : ℕ) (f : ℕ → ℝ),
      (List.range (m + n)).map f =
        (List.range m).map f ++ (List.range n).map (fun i => f (m + i)) := by
    intro m n
    induction n with
    | zero => intro f; simp
    | succ k ih =>
      intro f
      rw [Nat.add_succ, List.range_succ, List.map_append, ih, List.range_succ, List.map_append]
      simp only [List.map_cons, List.map_nil, List.append_assoc]
  have telesc : ∀ (g : ℕ → ℝ) (k a : ℕ),
      ((List.range k).map (fun i => g (a + (i + 1)) - g (a + i))).sum = g (a + k) - g a := by
    intro g k
    induction k with
    | zero => intro a; simp
    | succ k ih =>
      intro a
      rw [List.range_succ, List.map_append, List.sum_append, ih]
      have hlast : (List.map (fun i => g (a + (i + 1)) - g (a + i)) [k]).sum
          = g (a + (k + 1)) - g (a + k) := by simp
      rw [hlast]
      ring
  have crux : ∀ (n : ℕ) (A B : List ℝ) (κ : ℕ → ℕ),
      κ 0 = 0 →
      (∀ j : ℕ, j < n → κ j ≤ κ (j + 1)) →
      (∀ j : ℕ, j ≤ n → B.getD (κ j) 0 = A.getD j 0) →
      ∃ blocks : List (List ℝ),
        blocks.flatten =
          (List.range (κ n)).map (fun i => B.getD (i + 1) 0 - B.getD i 0) ∧
        blocks.map (fun b => b.sum) =
          (List.range n).map (fun j => A.getD (j + 1) 0 - A.getD j 0) := by
    intro n
    induction n with
    | zero =>
      intro A B κ hκ0 _ _
      exact ⟨[], by simp [hκ0], by simp⟩
    | succ n ih =>
      intro A B κ hκ0 hmono hval
      obtain ⟨blocks', hflat', hsum'⟩ :=
        ih A B κ hκ0 (fun j hj => hmono j (Nat.lt_succ_of_lt hj))
          (fun j hj => hval j (Nat.le_succ_of_le hj))
      have hle : κ n ≤ κ (n + 1) := hmono n (Nat.lt_succ_self n)
      set m : ℕ := κ (n + 1) - κ n with hm
      have hsplit : κ (n + 1) = κ n + m := by
        rw [hm]; exact (Nat.add_sub_of_le hle).symm
      have hlast_sum :
          ((List.range m).map (fun i => B.getD (κ n + i + 1) 0 - B.getD (κ n + i) 0)).sum
            = A.getD (n + 1) 0 - A.getD n 0 := by
        have h := telesc (fun i => B.getD i 0) m (κ n)
        rw [← hsplit] at h
        rw [hval (n + 1) (le_refl (n + 1)), hval n (Nat.le_succ n)] at h
        simpa using h
      refine ⟨blocks' ++
        [(List.range m).map (fun i => B.getD (κ n + i + 1) 0 - B.getD (κ n + i) 0)],
        ?_, ?_⟩
      · have hr := range_split (κ n) m (fun i => B.getD (i + 1) 0 - B.getD i 0)
        rw [List.flatten_append, hflat', hsplit, hr]
        simp
      · rw [List.map_append, hsum', List.range_succ, List.map_append]
        simp only [List.map_cons, List.map_nil, hlast_sum]
  have bridge_aux : ∀ (t : List ℝ) (x : ℝ),
      List.zipWith (fun a b => b - a) (x :: t) t =
        (List.range t.length).map
          (fun i => (x :: t).getD (i + 1) 0 - (x :: t).getD i 0) := by
    intro t
    induction t with
    | nil => intro x; simp
    | cons y t ih =>
      intro x
      rw [List.zipWith_cons_cons, ih y, List.length_cons, List.range_succ_eq_map]
      simp
  have bridge : ∀ (l : List ℝ),
      List.zipWith (fun a b => b - a) l l.tail =
        (List.range (l.length - 1)).map (fun i => l.getD (i + 1) 0 - l.getD i 0) := by
    intro l
    cases l with
    | nil => simp
    | cons x t =>
      rw [List.tail_cons, bridge_aux t x, List.length_cons, Nat.add_sub_cancel]
  let LA : List ℝ := (0 : ℝ) :: S.sort (· ≤ ·) ++ [1]
  let LB : List ℝ := (0 : ℝ) :: T.sort (· ≤ ·) ++ [1]
  have hLA_len : LA.length = S.card + 2 := by simp [LA, Finset.length_sort]
  have hLB_len : LB.length = T.card + 2 := by simp [LB, Finset.length_sort]
  have hLB_nonneg : ∀ x ∈ LB, 0 ≤ x := by
    intro x hx
    simp only [LB] at hx
    rcases List.mem_cons.mp hx with h | h
    · rw [h]
    · rcases List.mem_append.mp h with h' | h'
      · exact le_of_lt (hT ((Finset.mem_sort (fun a b : ℝ => a ≤ b)).mp h')).1
      · rcases List.mem_cons.mp h' with h2 | h2
        · rw [h2]; exact zero_le_one
        · exact absurd h2 (by simp)
  have hLAsub : ∀ x ∈ LA, x ∈ LB := by
    intro x hx
    simp only [LA, LB] at hx ⊢
    rcases List.mem_cons.mp hx with h | h
    · exact List.mem_cons.mpr (Or.inl h)
    · rcases List.mem_append.mp h with h' | h'
      · exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl
          ((Finset.mem_sort (fun a b : ℝ => a ≤ b)).mpr
            (hST ((Finset.mem_sort (fun a b : ℝ => a ≤ b)).mp h'))))))
      · rcases List.mem_cons.mp h' with h2 | h2
        · exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr
            (List.mem_cons.mpr (Or.inl h2)))))
        · exact absurd h2 (by simp)
  obtain ⟨κ, hκ0, hκend, hmono, hval⟩ :=
    statopia_math_node_1162978405_2cbda557 S T hST hT
  have hval' : ∀ j : ℕ, j ≤ S.card + 1 → LB.getD (κ j) 0 = LA.getD j 0 := by
    intro j hj
    simpa [LA, LB] using hval j hj
  obtain ⟨blocks, hflat, hsum⟩ := crux (S.card + 1) LA LB κ hκ0 hmono hval'
  have hpieceT : (List.range (T.card + 1)).map
      (fun i => LB.getD (i + 1) 0 - LB.getD i 0) = pieceLengths T := by
    have hb := bridge LB
    have hlen : LB.length - 1 = T.card + 1 := by rw [hLB_len]; simp
    rw [hlen] at hb
    simpa [pieceLengths, LB] using hb.symm
  have hpieceS : (List.range (S.card + 1)).map
      (fun j => LA.getD (j + 1) 0 - LA.getD j 0) = pieceLengths S := by
    have hb := bridge LA
    have hlen : LA.length - 1 = S.card + 1 := by rw [hLA_len]; simp
    rw [hlen] at hb
    simpa [pieceLengths, LA] using hb.symm
  refine ⟨blocks, ?_, ?_⟩
  · rw [hflat, hκend]
    exact hpieceT
  · rw [hsum]
    exact hpieceS
  /- @proof-region region.target-node.session.73890eceb3172b83 end -/

end LiuBangXiangYu
