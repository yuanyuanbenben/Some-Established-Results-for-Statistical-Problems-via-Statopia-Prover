import ProverJobs.real_V_eq_15312944933b.Vocabulary
import ProverJobs.real_V_eq_15312944933b.Base

open scoped BigOperators
open LiuBangXiangYu

open scoped BigOperators
namespace LiuBangXiangYu

set_option autoImplicit false in
theorem statopia_math_node_1162978405_2cbda557 : ∀ (S T : Finset ℝ) (hST : S ⊆ T)
    (hT : (T : Set ℝ) ⊆ Set.Ioo (0 : ℝ) 1),
    ∃ κ : ℕ → ℕ,
      κ 0 = 0 ∧
      κ (S.card + 1) = T.card + 1 ∧
      (∀ j : ℕ, j < S.card + 1 → κ j ≤ κ (j + 1)) ∧
      (∀ j : ℕ, j ≤ S.card + 1 →
        ((0 : ℝ) :: T.sort (· ≤ ·) ++ [1]).getD (κ j) 0 =
          ((0 : ℝ) :: S.sort (· ≤ ·) ++ [1]).getD j 0) := by
  /- @proof-region region.target-node.session.f00ade1b36dd2284 begin -/
  intro S T hST hT
  let LA : List ℝ := (0 : ℝ) :: S.sort (· ≤ ·) ++ [1]
  let LB : List ℝ := (0 : ℝ) :: T.sort (· ≤ ·) ++ [1]
  let cnt : List ℝ → ℝ → ℕ :=
    fun l v => l.foldr (fun a acc => (if a < v then 1 else 0) + acc) 0
  have cnt_nil : ∀ v : ℝ, cnt [] v = 0 := by
    intro v
    rfl
  have cnt_cons : ∀ (a : ℝ) (t : List ℝ) (v : ℝ),
      cnt (a :: t) v = (if a < v then 1 else 0) + cnt t v := by
    intro a t v
    rfl
  have hSsort_len : (S.sort (· ≤ ·)).length = S.card := by
    have h := (Finset.sort_perm_toList S (· ≤ ·)).length_eq
    rwa [Finset.length_toList] at h
  have hTsort_len : (T.sort (· ≤ ·)).length = T.card := by
    have h := (Finset.sort_perm_toList T (· ≤ ·)).length_eq
    rwa [Finset.length_toList] at h
  have hInS : ∀ x ∈ S.sort (· ≤ ·), (0 : ℝ) < x ∧ x < 1 := by
    intro x hx
    exact hT (hST ((Finset.mem_sort (· ≤ ·)).mp hx))
  have hInT : ∀ x ∈ T.sort (· ≤ ·), (0 : ℝ) < x ∧ x < 1 := by
    intro x hx
    exact hT ((Finset.mem_sort (· ≤ ·)).mp hx)
  have pair_lt : ∀ l : List ℝ, l.Pairwise (· ≤ ·) → l.Nodup → l.Pairwise (· < ·) := by
    intro l
    induction l with
    | nil => intro _ _; exact List.Pairwise.nil
    | cons x t ih =>
      intro hp hn
      rw [List.pairwise_cons] at hp
      obtain ⟨hle, hpt_le⟩ := hp
      rw [List.nodup_cons] at hn
      obtain ⟨hnotin, hnodup_t⟩ := hn
      exact List.pairwise_cons.mpr
        ⟨fun y hy => lt_of_le_of_ne (hle y hy) (fun hxy => hnotin (hxy ▸ hy)),
          ih hpt_le hnodup_t⟩
  have hSsort_mono : (S.sort (· ≤ ·)).Pairwise (· < ·) :=
    pair_lt _ (Finset.pairwise_sort S (· ≤ ·)) (Finset.sort_nodup S (· ≤ ·))
  have hTsort_mono : (T.sort (· ≤ ·)).Pairwise (· < ·) :=
    pair_lt _ (Finset.pairwise_sort T (· ≤ ·)) (Finset.sort_nodup T (· ≤ ·))
  have mkmono : ∀ (l : List ℝ), l.Pairwise (· < ·) → (∀ x ∈ l, (0 : ℝ) < x) →
      (∀ x ∈ l, x < 1) → (0 :: (l ++ [1])).Pairwise (· < ·) := by
    intro l hl h0 h1
    rw [List.pairwise_cons]
    refine ⟨?_, ?_⟩
    · intro x hx
      rw [List.mem_append] at hx
      rcases hx with hx | hx
      · exact h0 x hx
      · rw [List.mem_singleton] at hx
        rw [hx]
        norm_num
    · rw [List.pairwise_append]
      refine ⟨hl, ?_, ?_⟩
      · rw [List.pairwise_cons]
        exact ⟨fun x hx => by simp at hx, List.Pairwise.nil⟩
      · intro a ha b hb
        rw [List.mem_singleton] at hb
        rw [hb]
        exact h1 a ha
  have hLAmono : LA.Pairwise (· < ·) := by
    change (0 :: (S.sort (· ≤ ·) ++ [1])).Pairwise (· < ·)
    exact mkmono (S.sort (· ≤ ·)) hSsort_mono (fun x hx => (hInS x hx).1)
      (fun x hx => (hInS x hx).2)
  have hLBmono : LB.Pairwise (· < ·) := by
    change (0 :: (T.sort (· ≤ ·) ++ [1])).Pairwise (· < ·)
    exact mkmono (T.sort (· ≤ ·)) hTsort_mono (fun x hx => (hInT x hx).1)
      (fun x hx => (hInT x hx).2)
  have hLAlen : LA.length = S.card + 2 := by
    change (0 :: (S.sort (· ≤ ·) ++ [1])).length = S.card + 2
    rw [List.length_cons, List.length_append, List.length_singleton]
    omega
  have cnt_append : ∀ (l₁ l₂ : List ℝ) (v : ℝ),
      cnt (l₁ ++ l₂) v = cnt l₁ v + cnt l₂ v := by
    intro l₁
    induction l₁ with
    | nil => intro l₂ v; simp [cnt_nil]
    | cons a t ih =>
      intro l₂ v
      change (if a < v then 1 else 0) + cnt (t ++ l₂) v =
        ((if a < v then 1 else 0) + cnt t v) + cnt l₂ v
      rw [ih l₂ v]
      exact (Nat.add_assoc _ _ _).symm
  have cnt_zero_of : ∀ (l : List ℝ) (v : ℝ), (∀ x ∈ l, ¬ (x < v)) → cnt l v = 0 := by
    intro l
    induction l with
    | nil => intro v _; exact cnt_nil v
    | cons a t ih =>
      intro v h
      have ha : ¬ (a < v) := h a (by simp)
      have ht : ∀ x ∈ t, ¬ (x < v) := fun x hx =>
        h x (by rw [List.mem_cons]; exact Or.inr hx)
      rw [cnt_cons, if_neg ha]
      have ht0 : cnt t v = 0 := ih v ht
      omega
  have cnt_full_of : ∀ (l : List ℝ) (v : ℝ), (∀ x ∈ l, x < v) → cnt l v = l.length := by
    intro l
    induction l with
    | nil => intro v _; simp [cnt_nil]
    | cons a t ih =>
      intro v h
      have ha : a < v := h a (by simp)
      have ht : ∀ x ∈ t, x < v := fun x hx =>
        h x (by rw [List.mem_cons]; exact Or.inr hx)
      rw [cnt_cons, if_pos ha, ih v ht, List.length_cons]
      omega
  have cnt_le : ∀ (l : List ℝ) (v w : ℝ), v ≤ w → cnt l v ≤ cnt l w := by
    intro l
    induction l with
    | nil => intro v w _; simp [cnt_nil]
    | cons a t ih =>
      intro v w hvw
      have hih : cnt t v ≤ cnt t w := ih v w hvw
      rw [cnt_cons, cnt_cons]
      by_cases hav : a < v
      · have haw : a < w := lt_of_lt_of_le hav hvw
        rw [if_pos hav, if_pos haw]
        omega
      · by_cases haw : a < w
        · rw [if_neg hav, if_pos haw]
          omega
        · rw [if_neg hav, if_neg haw]
          omega
  have getD_mem_of_lt : ∀ (l : List ℝ) (i : ℕ), i < l.length → l.getD i 0 ∈ l := by
    intro l
    induction l with
    | nil => intro i hi; simp at hi
    | cons a t ih =>
      intro i hi
      cases i with
      | zero => simp
      | succ k =>
        rw [List.length_cons] at hi
        rw [List.getD_cons_succ, List.mem_cons]
        exact Or.inr (ih k (by omega))
  have cnt_getD : ∀ (l : List ℝ) (v : ℝ), l.Pairwise (· < ·) → v ∈ l →
      l.getD (cnt l v) 0 = v := by
    intro l
    induction l with
    | nil => intro v _ hv; simp at hv
    | cons a t ih =>
      intro v hp hv
      rw [List.pairwise_cons] at hp
      obtain ⟨hat, hpt⟩ := hp
      rw [List.mem_cons] at hv
      rcases hv with hv | hvt
      · have hzero : cnt (a :: t) v = 0 := by
          apply cnt_zero_of
          intro x hx
          rw [List.mem_cons] at hx
          rcases hx with hx | hx
          · rw [hx, hv]
            exact not_lt.mpr (le_refl a)
          · exact not_lt.mpr (le_of_lt (hv.symm ▸ hat x hx))
        rw [hzero, hv]
        simp
      · have hav : a < v := hat v hvt
        have hcons : cnt (a :: t) v = cnt t v + 1 := by
          rw [cnt_cons, if_pos hav]
          exact Nat.add_comm 1 (cnt t v)
        rw [hcons, List.getD_cons_succ]
        exact ih v hpt hvt
  have getD_append_left : ∀ (l₁ l₂ : List ℝ) (i : ℕ), i < l₁.length →
      (l₁ ++ l₂).getD i 0 = l₁.getD i 0 := by
    intro l₁
    induction l₁ with
    | nil => intro l₂ i hi; simp at hi
    | cons a t ih =>
      intro l₂ i hi
      cases i with
      | zero => simp
      | succ k =>
        rw [List.length_cons] at hi
        change (t ++ l₂).getD k 0 = t.getD k 0
        exact ih l₂ k (by omega)
  have getD_append_singleton : ∀ (l : List ℝ) (b d : ℝ), (l ++ [b]).getD l.length d = b := by
    intro l
    induction l with
    | nil => intro b d; simp
    | cons a t ih =>
      intro b d
      change (t ++ [b]).getD t.length d = b
      exact ih b d
  have getD_lt_getD : ∀ (l : List ℝ), l.Pairwise (· < ·) → ∀ i j : ℕ, i < j →
      j < l.length → l.getD i 0 < l.getD j 0 := by
    intro l
    induction l with
    | nil => intro _ i j _ hj; simp at hj
    | cons a t ih =>
      intro hp i j hij hj
      rw [List.pairwise_cons] at hp
      obtain ⟨hat, hpt⟩ := hp
      cases i with
      | zero =>
        cases j with
        | zero => omega
        | succ k =>
          rw [List.length_cons] at hj
          have hk : k < t.length := by omega
          rw [List.getD_cons_zero, List.getD_cons_succ]
          exact hat (t.getD k 0) (getD_mem_of_lt t k hk)
      | succ i' =>
        cases j with
        | zero => omega
        | succ j' =>
          rw [List.length_cons] at hj
          have hj' : j' < t.length := by omega
          have hi' : i' < j' := by omega
          rw [List.getD_cons_succ, List.getD_cons_succ]
          exact ih hpt i' j' hi' hj'
  have hLA0 : LA.getD 0 0 = (0 : ℝ) := by
    change (0 :: (S.sort (· ≤ ·) ++ [1])).getD 0 0 = (0 : ℝ)
    simp
  have hLAlast : LA.getD (S.card + 1) 0 = (1 : ℝ) := by
    change (0 :: (S.sort (· ≤ ·) ++ [1])).getD (S.card + 1) 0 = (1 : ℝ)
    rw [List.getD_cons_succ, ← hSsort_len]
    exact getD_append_singleton (S.sort (· ≤ ·)) 1 0
  have hLBpos : ∀ x ∈ LB, (0 : ℝ) ≤ x := by
    intro x hx
    change x ∈ (0 : ℝ) :: ((T.sort (· ≤ ·)) ++ [1]) at hx
    rw [List.mem_cons] at hx
    rcases hx with hx | hx
    · simp [hx]
    · rw [List.mem_append] at hx
      rcases hx with hx | hx
      · exact le_of_lt (hInT x hx).1
      · rw [List.mem_singleton] at hx
        rw [hx]
        norm_num
  have hmem : ∀ j : ℕ, j ≤ S.card + 1 → LA.getD j 0 ∈ LB := by
    intro j hj
    cases j with
    | zero =>
      rw [hLA0]
      change (0 : ℝ) ∈ (0 : ℝ) :: ((T.sort (· ≤ ·)) ++ [1])
      rw [List.mem_cons]
      exact Or.inl rfl
    | succ j' =>
      have hj' : j' ≤ S.card := by omega
      rcases lt_or_eq_of_le hj' with hlt | heq
      · have hstep : LA.getD (j' + 1) 0 = (S.sort (· ≤ ·)).getD j' 0 := by
          change (0 :: (S.sort (· ≤ ·) ++ [1])).getD (j' + 1) 0 =
            (S.sort (· ≤ ·)).getD j' 0
          rw [List.getD_cons_succ]
          exact getD_append_left (S.sort (· ≤ ·)) [1] j' (by rw [hSsort_len]; exact hlt)
        rw [hstep]
        have hmemT : (S.sort (· ≤ ·)).getD j' 0 ∈ T :=
          hST ((Finset.mem_sort (· ≤ ·)).mp
            (getD_mem_of_lt (S.sort (· ≤ ·)) j' (by rw [hSsort_len]; exact hlt)))
        change (S.sort (· ≤ ·)).getD j' 0 ∈ (0 : ℝ) :: ((T.sort (· ≤ ·)) ++ [1])
        rw [List.mem_cons, List.mem_append, List.mem_singleton]
        exact Or.inr (Or.inl ((Finset.mem_sort (· ≤ ·)).mpr hmemT))
      · rw [heq, hLAlast]
        change (1 : ℝ) ∈ (0 : ℝ) :: ((T.sort (· ≤ ·)) ++ [1])
        rw [List.mem_cons, List.mem_append, List.mem_singleton]
        exact Or.inr (Or.inr rfl)
  refine ⟨fun j => cnt LB (LA.getD j 0), ?_, ?_, ?_, ?_⟩
  · change cnt LB (LA.getD 0 0) = 0
    rw [hLA0]
    exact cnt_zero_of LB 0 (fun x hx => not_lt.mpr (hLBpos x hx))
  · change cnt LB (LA.getD (S.card + 1) 0) = T.card + 1
    rw [hLAlast]
    have hcnt1 : cnt LB (1 : ℝ) = T.card + 1 := by
      have hA : cnt LB (1 : ℝ) = 1 + cnt ((T.sort (· ≤ ·)) ++ [1]) (1 : ℝ) := by
        change cnt ((0 : ℝ) :: ((T.sort (· ≤ ·)) ++ [1])) (1 : ℝ) =
          1 + cnt ((T.sort (· ≤ ·)) ++ [1]) (1 : ℝ)
        simp [cnt]
      rw [hA, cnt_append]
      have hB : cnt [1] (1 : ℝ) = 0 := by
        change cnt ((1 : ℝ) :: []) (1 : ℝ) = 0
        simp [cnt]
      rw [hB]
      have hC : cnt (T.sort (· ≤ ·)) (1 : ℝ) = (T.sort (· ≤ ·)).length :=
        cnt_full_of _ _ (fun x hx => (hInT x hx).2)
      rw [hC, hTsort_len]
      omega
    exact hcnt1
  · intro j hj
    have hlt : LA.getD j 0 < LA.getD (j + 1) 0 :=
      getD_lt_getD LA hLAmono j (j + 1) (Nat.lt_succ_self j) (by rw [hLAlen]; omega)
    exact cnt_le LB (LA.getD j 0) (LA.getD (j + 1) 0) (le_of_lt hlt)
  · intro j hj
    exact cnt_getD LB (LA.getD j 0) hLBmono (hmem j hj)
  /- @proof-region region.target-node.session.f00ade1b36dd2284 end -/

end LiuBangXiangYu
