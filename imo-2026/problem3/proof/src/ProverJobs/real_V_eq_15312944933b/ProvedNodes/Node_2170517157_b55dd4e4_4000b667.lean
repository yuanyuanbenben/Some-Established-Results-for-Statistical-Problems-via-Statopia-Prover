import ProverJobs.real_V_eq_15312944933b.Vocabulary
import ProverJobs.real_V_eq_15312944933b.Base

open scoped BigOperators
open LiuBangXiangYu

open scoped BigOperators
namespace LiuBangXiangYu

set_option autoImplicit false in
theorem statopia_math_node_2170517157_b55dd4e4 : ∀ (n : ℕ) (p : Fin (n + 1) → ℝ) (M : Finset ℝ)
    (hp : StrictMono p) (hM : ∀ x ∈ M, p 0 ≤ x ∧ x ≤ p (Fin.last n)),
    p 0 :: (List.ofFn (fun k : Fin n =>
        ((M.filter (fun x => p (Fin.castSucc k) < x ∧ x < p (Fin.succ k))).sort (· ≤ ·)) ++
          [p (Fin.succ k)])).flatten
      = (Finset.image p Finset.univ ∪ M).sort (· ≤ ·) := by
  /- @proof-region region.target-node.session.52fd2fed67523186 begin -/
  intro n p M hp hM
  let W : Fin n → List ℝ := fun k =>
    (M.filter (fun x => p (Fin.castSucc k) < x ∧ x < p (Fin.succ k))).sort (· ≤ ·)
  let S : Finset ℝ := Finset.image p Finset.univ ∪ M
  let J : List ℝ := p 0 :: (List.ofFn (fun k : Fin n => W k ++ [p (Fin.succ k)])).flatten
  show J = S.sort (· ≤ ·)
  have aux : ∀ (m : ℕ) (q : Fin (m + 1) → ℝ) (V : Fin m → List ℝ),
      StrictMono q →
      (∀ k, (V k).Pairwise (· < ·)) →
      (∀ k y, y ∈ V k → q (Fin.castSucc k) < y) →
      (∀ k y, y ∈ V k → y < q (Fin.succ k)) →
      ((List.ofFn (fun k : Fin m => V k ++ [q (Fin.succ k)])).flatten).Pairwise (· < ·) ∧
      (∀ y ∈ (List.ofFn (fun k : Fin m => V k ++ [q (Fin.succ k)])).flatten,
        q 0 < y ∧ y ≤ q (Fin.last m)) := by
    intro m
    induction m with
    | zero =>
      intro q V hq hVs hlo hhi
      constructor
      · simp
      · intro y hy
        exact absurd hy (by simp)
    | succ m ih =>
      intro q V hq hVs hlo hhi
      have hidx : ∀ i : Fin m, Fin.succ (Fin.castSucc i) = Fin.castSucc (Fin.succ i) :=
        fun i => Fin.ext rfl
      have hq' : StrictMono (fun j : Fin (m + 1) => q (Fin.succ j)) := by
        intro a b hab
        exact hq (show Fin.succ a < Fin.succ b from Nat.succ_lt_succ hab)
      have hV' : ∀ i, ((fun i : Fin m => V (Fin.succ i)) i).Pairwise (· < ·) :=
        fun i => hVs (Fin.succ i)
      have hlo' : ∀ i y, y ∈ (fun i : Fin m => V (Fin.succ i)) i →
          (fun j : Fin (m + 1) => q (Fin.succ j)) (Fin.castSucc i) < y := by
        intro i y hy
        have h := hlo (Fin.succ i) y hy
        rw [← hidx i] at h
        exact h
      have hhi' : ∀ i y, y ∈ (fun i : Fin m => V (Fin.succ i)) i →
          y < (fun j : Fin (m + 1) => q (Fin.succ j)) (Fin.succ i) := by
        intro i y hy
        exact hhi (Fin.succ i) y hy
      have ih' := ih (fun j : Fin (m + 1) => q (Fin.succ j)) (fun i : Fin m => V (Fin.succ i))
        hq' hV' hlo' hhi'
      let K' : List ℝ :=
        (List.ofFn (fun i : Fin m => V (Fin.succ i) ++ [q (Fin.succ (Fin.succ i))])).flatten
      have hK'p : K'.Pairwise (· < ·) := ih'.1
      have hK'lo : ∀ y ∈ K', q (Fin.succ (0 : Fin (m + 1))) < y := fun y hy => (ih'.2 y hy).1
      have hK'hi : ∀ y ∈ K', y ≤ q (Fin.last (m + 1)) := fun y hy => (ih'.2 y hy).2
      have hlt0 : q (0 : Fin (m + 2)) < q (Fin.succ (0 : Fin (m + 1))) :=
        hq (show (0 : Fin (m + 2)) < Fin.succ (0 : Fin (m + 1)) from Nat.zero_lt_one)
      have hle1 : q (Fin.succ (0 : Fin (m + 1))) ≤ q (Fin.last (m + 1)) := by
        have h2 : Fin.succ (0 : Fin (m + 1)) ≤ Fin.last (m + 1) := by
          show (1 : ℕ) ≤ m + 1
          omega
        rcases lt_or_eq_of_le h2 with h | h
        · exact le_of_lt (hq h)
        · exact le_of_eq (congrArg q h)
      have hAp : (V 0 ++ [q (Fin.succ 0)]).Pairwise (· < ·) := by
        rw [List.pairwise_append]
        refine ⟨hVs 0, by simp, ?_⟩
        intro a ha b hb
        rw [List.mem_singleton] at hb
        subst hb
        exact hhi 0 a ha
      have hAB : ((V 0 ++ [q (Fin.succ 0)]) ++ K').Pairwise (· < ·) := by
        rw [List.pairwise_append]
        refine ⟨hAp, hK'p, ?_⟩
        intro a ha b hb
        rw [List.mem_append] at ha
        rcases ha with ha | ha
        · exact lt_of_lt_of_le (hhi 0 a ha) (le_of_lt (hK'lo b hb))
        · rw [List.mem_singleton] at ha
          subst ha
          exact hK'lo b hb
      have hK : (List.ofFn (fun k : Fin (m + 1) => V k ++ [q (Fin.succ k)])).flatten
          = (V 0 ++ [q (Fin.succ 0)]) ++ K' := by
        rw [List.ofFn_succ, List.flatten_cons]
      constructor
      · rw [hK]; exact hAB
      · intro y hy
        rw [hK, List.mem_append] at hy
        rcases hy with hy | hy
        · rw [List.mem_append] at hy
          rcases hy with hy | hy
          · exact ⟨hlo 0 y hy, le_trans (le_of_lt (hhi 0 y hy)) hle1⟩
          · rw [List.mem_singleton] at hy
            subst hy
            exact ⟨hlt0, hle1⟩
        · exact ⟨lt_trans hlt0 (hK'lo y hy), hK'hi y hy⟩
  have key : ∀ {L : List ℝ}, L.Pairwise (· ≤ ·) → L.Nodup → L.Pairwise (· < ·) := by
    intro L
    induction L with
    | nil => intro _ _; simp
    | cons a l ih =>
      intro hle hnd
      rw [List.pairwise_cons] at hle
      obtain ⟨hle1, hle2⟩ := hle
      rw [List.nodup_cons] at hnd
      obtain ⟨hnotin, hndl⟩ := hnd
      rw [List.pairwise_cons]
      exact ⟨fun b hb => lt_of_le_of_ne (hle1 b hb) (fun h => hnotin (h.symm ▸ hb)), ih hle2 hndl⟩
  have hWp : ∀ k, (W k).Pairwise (· < ·) := fun k =>
    key (Finset.pairwise_sort (M.filter (fun x => p (Fin.castSucc k) < x ∧ x < p (Fin.succ k))) (· ≤ ·))
      (Finset.sort_nodup (M.filter (fun x => p (Fin.castSucc k) < x ∧ x < p (Fin.succ k))) (· ≤ ·))
  have hWspec : ∀ k y, y ∈ W k → y ∈ M ∧ p (Fin.castSucc k) < y ∧ y < p (Fin.succ k) := by
    intro k y hy
    have hy1 : y ∈ (M.filter (fun x => p (Fin.castSucc k) < x ∧ x < p (Fin.succ k))).sort (· ≤ ·) := by
      simpa only [W] using hy
    have hy2 : y ∈ M.filter (fun x => p (Fin.castSucc k) < x ∧ x < p (Fin.succ k)) := by
      simpa only [Finset.mem_sort] using hy1
    exact Finset.mem_filter.mp hy2
  have haux := aux n p W hp hWp (fun k y hy => (hWspec k y hy).2.1) (fun k y hy => (hWspec k y hy).2.2)
  have hJlt : J.Pairwise (· < ·) := by
    change (p 0 :: (List.ofFn (fun k : Fin n => W k ++ [p (Fin.succ k)])).flatten).Pairwise (· < ·)
    exact List.pairwise_cons.mpr ⟨fun b hb => (haux.2 b hb).1, haux.1⟩
  have hJpair : J.Pairwise (· ≤ ·) := hJlt.imp (fun hab => le_of_lt hab)
  have hJnodup : J.Nodup := hJlt.imp (fun hab => ne_of_lt hab)
  have hcover : ∀ (m : ℕ) (q : Fin (m + 1) → ℝ), StrictMono q → ∀ x,
      q 0 ≤ x → x ≤ q (Fin.last m) →
      x = q 0 ∨ ∃ k : Fin m, q (Fin.castSucc k) < x ∧ x ≤ q (Fin.succ k) := by
    intro m
    induction m with
    | zero =>
      intro q hq x h0 h1
      exact Or.inl (le_antisymm h0 (h1.trans (le_of_eq (congrArg q (Fin.ext rfl))))).symm
    | succ m ih =>
      intro q hq x h0 h1
      by_cases hx : x ≤ q (Fin.castSucc (Fin.last m))
      · rcases ih (fun j : Fin (m + 1) => q (Fin.castSucc j))
          (fun a b hab => hq (show Fin.castSucc a < Fin.castSucc b from hab)) x h0 hx
          with h | ⟨k, hk1, hk2⟩
        · exact Or.inl h
        · refine Or.inr ⟨Fin.castSucc k, hk1, ?_⟩
          rw [show Fin.succ (Fin.castSucc k) = Fin.castSucc (Fin.succ k) from Fin.ext rfl]
          exact hk2
      · refine Or.inr ⟨Fin.last m, lt_of_not_ge hx, ?_⟩
        rw [show Fin.succ (Fin.last m) = Fin.last (m + 1) from Fin.ext rfl]
        exact h1
  have hmflatten : ∀ y, y ∈ (List.ofFn (fun k : Fin n => W k ++ [p (Fin.succ k)])).flatten ↔
      ∃ k : Fin n, y ∈ W k ∨ y = p (Fin.succ k) := by
    intro y
    rw [List.mem_flatten]
    constructor
    · rintro ⟨l', hl', hy⟩
      rw [List.mem_ofFn] at hl'
      obtain ⟨k, rfl⟩ := hl'
      rcases List.mem_append.mp hy with h | h
      · exact ⟨k, Or.inl h⟩
      · exact ⟨k, Or.inr (List.mem_singleton.mp h)⟩
    · rintro ⟨k, h | h⟩
      · exact ⟨W k ++ [p (Fin.succ k)], List.mem_ofFn.mpr ⟨k, rfl⟩, List.mem_append.mpr (Or.inl h)⟩
      · exact ⟨W k ++ [p (Fin.succ k)], List.mem_ofFn.mpr ⟨k, rfl⟩,
          List.mem_append.mpr (Or.inr (List.mem_singleton.mpr h))⟩
  have hmJ : ∀ y, y ∈ J ↔ y = p 0 ∨ ∃ k : Fin n, y ∈ W k ∨ y = p (Fin.succ k) := by
    intro y
    simp only [J, List.mem_cons, hmflatten]
  have hmS : ∀ x, x ∈ S ↔ (∃ j : Fin (n + 1), p j = x) ∨ x ∈ M := by
    intro x
    simp only [S, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  have hmW : ∀ k y, y ∈ W k ↔ y ∈ M ∧ p (Fin.castSucc k) < y ∧ y < p (Fin.succ k) := by
    intro k y
    simp only [W, Finset.mem_sort, Finset.mem_filter]
  have hpmono : ∀ {i j : Fin (n + 1)}, i ≤ j → p i ≤ p j := by
    intro i j hij
    rcases lt_or_eq_of_le hij with h | h
    · exact le_of_lt (hp h)
    · exact le_of_eq (congrArg p h)
  have hJtofinset : J.toFinset = S := by
    ext x
    rw [List.mem_toFinset, hmJ x, hmS x]
    constructor
    · rintro (rfl | ⟨k, h | h⟩)
      · exact Or.inl ⟨0, rfl⟩
      · exact Or.inr ((hmW k x).mp h).1
      · exact Or.inl ⟨Fin.succ k, h.symm⟩
    · rintro (⟨j, hj⟩ | hxM)
      · rw [← hj]
        have h0 : (0 : Fin (n + 1)) ≤ j := by show (0 : ℕ) ≤ j.1; omega
        have hl : j ≤ Fin.last n := by show j.1 ≤ n; omega
        rcases hcover n p hp (p j) (hpmono h0) (hpmono hl) with h | ⟨k0, hk1, hk2⟩
        · exact Or.inl h
        · have hkj : Fin.castSucc k0 < j := by
            by_cases hc : Fin.castSucc k0 < j
            · exact hc
            · exact absurd (lt_of_lt_of_le hk1 (hpmono (le_of_not_gt hc))) (lt_irrefl _)
          have hjk : j ≤ Fin.succ k0 := by
            by_cases hc : j ≤ Fin.succ k0
            · exact hc
            · exact absurd (lt_of_le_of_lt hk2 (hp (lt_of_not_ge hc))) (lt_irrefl _)
          have hjeq : j = Fin.succ k0 := by
            apply Fin.ext
            show j.1 = k0.1 + 1
            have h1 : k0.1 < j.1 := hkj
            have h2 : j.1 ≤ k0.1 + 1 := hjk
            omega
          exact Or.inr ⟨k0, Or.inr (congrArg p hjeq)⟩
      · have hh := hM x hxM
        rcases hcover n p hp x hh.1 hh.2 with h | ⟨k0, hk1, hk2⟩
        · exact Or.inl h
        · rcases lt_or_eq_of_le hk2 with hlt | heq
          · exact Or.inr ⟨k0, Or.inl ((hmW k0 x).mpr ⟨hxM, hk1, hlt⟩)⟩
          · exact Or.inr ⟨k0, Or.inr heq⟩
  have hmain := (List.toFinset_sort (r := (· ≤ ·)) hJnodup).2 hJpair
  rw [hJtofinset] at hmain
  exact hmain.symm
  /- @proof-region region.target-node.session.52fd2fed67523186 end -/

end LiuBangXiangYu
