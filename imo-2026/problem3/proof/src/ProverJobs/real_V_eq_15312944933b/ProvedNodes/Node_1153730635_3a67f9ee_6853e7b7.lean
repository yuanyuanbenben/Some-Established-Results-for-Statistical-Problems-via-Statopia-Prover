import ProverJobs.real_V_eq_15312944933b.Vocabulary
import ProverJobs.real_V_eq_15312944933b.Base

open scoped BigOperators
open LiuBangXiangYu

open scoped BigOperators
namespace LiuBangXiangYu

set_option autoImplicit false in
theorem statopia_math_node_1153730635_3a67f9ee : ∀ (t : List ℝ)
    (hpair : t.Pairwise (fun a b => a ≥ b)) (hnonneg : ∀ x ∈ t, 0 ≤ x),
    (let O : ℝ := (((t.zipIdx).filter (fun p => decide (p.2 % 2 = 0))).map (fun p => p.1)).sum
     let E : ℝ := (((t.zipIdx).filter (fun p => decide (p.2 % 2 = 1))).map (fun p => p.1)).sum
     let D : ℝ := (((t.zipIdx).filter (fun p => decide (p.2 % 2 = 0))).map (fun p => p.1 - t.getD (p.2 + 1) 0)).sum
     let S : ℝ := t.sum
     O - E = D ∧
     (∀ p ∈ (t.zipIdx).filter (fun p => decide (p.2 % 2 = 0)), 0 ≤ p.1 - t.getD (p.2 + 1) 0) ∧
     0 ≤ D ∧
     D = (((t.zipIdx).filter (fun p => decide (p.2 % 2 = 0))).map (fun p => |p.1 - t.getD (p.2 + 1) 0|)).sum ∧
     O + E = S ∧
     O = (S + D) / 2 ∧
     (S = 1 → 0 ≤ O ∧ O ≤ 1)) := by
  /- @proof-region region.target-node.session.8910e71c2fa311d1 begin -/
  intro t hpair hnonneg
  have hrec : ∀ (a : ℝ) (u : List ℝ) (n : Nat),
      (a :: u).zipIdx n = (a, n) :: u.zipIdx (n + 1) := by
    intro a u n
    simp
  have hshift : ∀ (u : List ℝ) (n : Nat),
      u.zipIdx (n + 1) = (u.zipIdx n).map (fun p => (p.1, p.2 + 1)) := by
    intro u n
    induction u generalizing n with
    | nil => simp
    | cons a u ih =>
      rw [hrec a u (n + 1), hrec a u n, List.map_cons, ih (n + 1)]
  have hrec0 : ∀ (a : ℝ) (u : List ℝ),
      (a :: u).zipIdx = (a, 0) :: (u.zipIdx).map (fun p => (p.1, p.2 + 1)) := by
    intro a u
    rw [hrec a u 0, hshift u 0]
  let Ye : List ℝ → ℝ :=
    fun u => ((u.zipIdx.filter (fun p => decide (p.2 % 2 = 0))).map (fun p => p.1)).sum
  let Yo : List ℝ → ℝ :=
    fun u => ((u.zipIdx.filter (fun p => decide (p.2 % 2 = 1))).map (fun p => p.1)).sum
  let Ds : List ℝ → ℝ :=
    fun u => ((u.zipIdx.filter (fun p => decide (p.2 % 2 = 0))).map
      (fun p => p.1 - u.getD (p.2 + 1) 0)).sum
  have hfm : ∀ {α β : Type} (l : List α) (f : α → β) (q : β → Bool),
      (l.map f).filter q = (l.filter (fun a => q (f a))).map f := by
    intro α β l f q
    induction l with
    | nil => simp
    | cons a l ih =>
      cases hb : q (f a) with
      | true => simp [ih, hb]
      | false => simp [ih, hb]
  have hpar : ∀ k : Nat, decide ((k + 1) % 2 = 0) = decide (k % 2 = 1) := by
    intro k
    have h : ((k + 1) % 2 = 0) ↔ (k % 2 = 1) := by omega
    simp [h]
  have hpar' : ∀ k : Nat, decide ((k + 1) % 2 = 1) = decide (k % 2 = 0) := by
    intro k
    have h : ((k + 1) % 2 = 1) ↔ (k % 2 = 0) := by omega
    simp [h]
  have Ye_cons : ∀ (a : ℝ) (u : List ℝ), Ye (a :: u) = a + Yo u := by
    intro a u
    simp only [Ye, Yo, hrec0 a u]
    simp
    rw [hfm, List.map_map]
    rw [show ((fun p : ℝ × Nat => p.1) ∘ (fun p : ℝ × Nat => (p.1, p.2 + 1)))
        = (fun p : ℝ × Nat => p.1) from by funext p; rfl]
    show (List.map (fun p : ℝ × Nat => p.1)
          (List.filter (fun a => decide ((a.2 + 1) % 2 = 0)) u.zipIdx)).sum
        = (List.map (fun p : ℝ × Nat => p.1)
          (List.filter (fun p => decide (p.2 % 2 = 1)) u.zipIdx)).sum
    rw [show (fun a : ℝ × Nat => decide ((a.2 + 1) % 2 = 0))
        = (fun p : ℝ × Nat => decide (p.2 % 2 = 1)) from by funext p; exact hpar p.2]
  have Yo_cons : ∀ (a : ℝ) (u : List ℝ), Yo (a :: u) = Ye u := by
    intro a u
    simp only [Yo, Ye, hrec0 a u]
    simp
    rw [hfm, List.map_map]
    rw [show ((fun p : ℝ × Nat => p.1) ∘ (fun p : ℝ × Nat => (p.1, p.2 + 1)))
        = (fun p : ℝ × Nat => p.1) from by funext p; rfl]
    show (List.map (fun p : ℝ × Nat => p.1)
          (List.filter (fun a => decide ((a.2 + 1) % 2 = 1)) u.zipIdx)).sum
        = (List.map (fun p : ℝ × Nat => p.1)
          (List.filter (fun p => decide (p.2 % 2 = 0)) u.zipIdx)).sum
    rw [show (fun a : ℝ × Nat => decide ((a.2 + 1) % 2 = 1))
        = (fun p : ℝ × Nat => decide (p.2 % 2 = 0)) from by funext p; exact hpar' p.2]
  have hpartgen : ∀ (α : Type) (l : List α) (q : α → Bool) (f : α → ℝ),
      ((l.filter q).map f).sum + ((l.filter (fun a => !q a)).map f).sum = (l.map f).sum := by
    intro α l q f
    induction l with
    | nil => simp
    | cons a l ih =>
      cases hb : q a with
      | true => simp [hb]; linarith [ih]
      | false => simp [hb]; linarith [ih]
  have hcompl : ∀ k : Nat, Bool.not (decide (k % 2 = 1)) = decide (k % 2 = 0) := by
    intro k
    have h : k % 2 = 0 ∨ k % 2 = 1 := by omega
    rcases h with h | h <;> simp [h]
  have hgd : ∀ (x : ℝ) (u : List ℝ) (n : Nat), (x :: u).getD (n + 1) 0 = u.getD n 0 := by
    intro x u n
    rfl
  have hgd0 : ∀ (x : ℝ) (u : List ℝ), (x :: u).getD 0 0 = x := by
    intro x u
    rfl
  have htel : ∀ (u : List ℝ),
      ((u.zipIdx).map (fun p => p.1 - u.getD (p.2 + 1) 0)).sum = u.getD 0 0 := by
    intro u
    induction u with
    | nil => simp
    | cons a u ih =>
      simp only [hrec0 a u, List.map_cons, List.sum_cons]
      rw [List.map_map]
      rw [show ((fun p : ℝ × Nat => p.1 - (a :: u).getD (p.2 + 1) 0) ∘ (fun p : ℝ × Nat => (p.1, p.2 + 1)))
          = (fun p : ℝ × Nat => p.1 - u.getD (p.2 + 1) 0) from by
        funext p
        simp only [Function.comp_apply]
        rw [hgd a u (p.2 + 1)]]
      rw [ih]
      rw [hgd a u 0]
      rw [hgd0 a u]
      ring
  have hSo : ∀ (u : List ℝ),
      ((u.zipIdx.filter (fun p => decide (p.2 % 2 = 1))).map
        (fun p => p.1 - u.getD (p.2 + 1) 0)).sum = u.getD 0 0 - Ds u := by
    intro u
    have hp := hpartgen (ℝ × Nat) u.zipIdx (fun p => decide (p.2 % 2 = 1))
      (fun p => p.1 - u.getD (p.2 + 1) 0)
    have hc : (fun p : ℝ × Nat => !decide (p.2 % 2 = 1)) = (fun p : ℝ × Nat => decide (p.2 % 2 = 0)) := by
      funext p; exact hcompl p.2
    rw [hc] at hp
    have ht := htel u
    have hd : Ds u = ((u.zipIdx.filter (fun p => decide (p.2 % 2 = 0))).map
        (fun p => p.1 - u.getD (p.2 + 1) 0)).sum := rfl
    linarith
  have Ds_cons : ∀ (a : ℝ) (u : List ℝ), Ds (a :: u) = a - Ds u := by
    intro a u
    have hsu := hSo u
    have hD1 : Ds (a :: u) = (a - u.getD 0 0)
        + ((u.zipIdx.filter (fun p => decide (p.2 % 2 = 1))).map
            (fun p => p.1 - u.getD (p.2 + 1) 0)).sum := by
      simp only [Ds, hrec0 a u]
      simp
      rw [hfm, List.map_map]
      rw [show (fun a : ℝ × Nat => decide ((a.1, a.2 + 1).2 % 2 = 0))
          = (fun p : ℝ × Nat => decide (p.2 % 2 = 1)) from by funext p; exact hpar p.2]
      apply congrArg List.sum
      congr 1
    rw [hD1]
    linarith
  let gE : List ℝ → List ℝ :=
    fun u => ((u.zipIdx.filter (fun p => decide (p.2 % 2 = 0))).map (fun p => p.1 - u.getD (p.2 + 1) 0))
  let gO : List ℝ → List ℝ :=
    fun u => ((u.zipIdx.filter (fun p => decide (p.2 % 2 = 1))).map (fun p => p.1 - u.getD (p.2 + 1) 0))
  have gE_cons : ∀ (a : ℝ) (u : List ℝ), gE (a :: u) = (a - u.getD 0 0) :: gO u := by
    intro a u
    simp only [gE, gO, hrec0 a u]
    rw [show (((a, 0) :: (u.zipIdx).map (fun p => (p.1, p.2 + 1))).filter
          (fun p => decide (p.2 % 2 = 0)))
        = (a, 0) :: (((u.zipIdx).map (fun p => (p.1, p.2 + 1))).filter
          (fun p => decide (p.2 % 2 = 0))) from by simp]
    rw [List.map_cons]
    congr 1
    rw [hfm, List.map_map]
    show (List.map (fun q : ℝ × Nat => q.1 - u.getD (q.2 + 1) 0)
          (List.filter (fun q : ℝ × Nat => decide ((q.2 + 1) % 2 = 0)) u.zipIdx))
        = (List.map (fun q : ℝ × Nat => q.1 - u.getD (q.2 + 1) 0)
          (List.filter (fun q : ℝ × Nat => decide (q.2 % 2 = 1)) u.zipIdx))
    rw [show (fun q : ℝ × Nat => decide ((q.2 + 1) % 2 = 0))
        = (fun q : ℝ × Nat => decide (q.2 % 2 = 1)) from by funext q; exact hpar q.2]
  have gO_cons : ∀ (a : ℝ) (u : List ℝ), gO (a :: u) = gE u := by
    intro a u
    simp only [gO, gE, hrec0 a u]
    rw [show (((a, 0) :: (u.zipIdx).map (fun p => (p.1, p.2 + 1))).filter
          (fun p => decide (p.2 % 2 = 1)))
        = ((u.zipIdx).map (fun p => (p.1, p.2 + 1))).filter
          (fun p => decide (p.2 % 2 = 1)) from by simp]
    rw [hfm, List.map_map]
    show (List.map (fun q : ℝ × Nat => q.1 - u.getD (q.2 + 1) 0)
          (List.filter (fun q : ℝ × Nat => decide ((q.2 + 1) % 2 = 1)) u.zipIdx))
        = (List.map (fun q : ℝ × Nat => q.1 - u.getD (q.2 + 1) 0)
          (List.filter (fun q : ℝ × Nat => decide (q.2 % 2 = 0)) u.zipIdx))
    rw [show (fun q : ℝ × Nat => decide ((q.2 + 1) % 2 = 1))
        = (fun q : ℝ × Nat => decide (q.2 % 2 = 0)) from by funext q; exact hpar' q.2]
  have hYs : ∀ (u : List ℝ), Ye u + Yo u = u.sum := by
    intro u
    induction u with
    | nil => simp [Ye, Yo]
    | cons a u ih =>
      rw [Ye_cons a u, Yo_cons a u, List.sum_cons]
      linarith
  have hYd : ∀ (u : List ℝ), Ye u - Yo u = Ds u := by
    intro u
    induction u with
    | nil => simp [Ye, Yo, Ds]
    | cons a u ih =>
      rw [Ye_cons a u, Yo_cons a u, Ds_cons a u]
      linarith
  have hsum_congr : ∀ (l : List (ℝ × Nat)) (f g : ℝ × Nat → ℝ),
      (∀ x ∈ l, f x = g x) → (l.map f).sum = (l.map g).sum := by
    intro l
    induction l with
    | nil => intro f g _; simp
    | cons x l ih =>
      intro f g h
      simp only [List.map_cons, List.sum_cons]
      rw [h x (by simp), ih f g (fun y hy => h y (by simp [hy]))]
  have key : ∀ (u : List ℝ), u.Pairwise (fun a b => a ≥ b) → (∀ x ∈ u, 0 ≤ x) →
      (∀ x ∈ gE u, 0 ≤ x) ∧ (∀ x ∈ gO u, 0 ≤ x) ∧
      0 ≤ (gE u).sum ∧ 0 ≤ (gO u).sum ∧ 0 ≤ Ye u ∧ 0 ≤ Yo u := by
    intro u
    induction u with
    | nil =>
      intro _ _
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [gE, gO, Ye, Yo]
    | cons a u ih =>
      intro hp hn
      cases hp with
      | cons hab hpu =>
        have ha : 0 ≤ a := hn a (by simp)
        have hhead : u.getD 0 0 ≤ a := by
          cases u with
          | nil =>
            have h0 : ([].getD 0 (0 : ℝ)) = 0 := rfl
            rw [h0]
            exact ha
          | cons b v => exact hab b (by simp)
        obtain ⟨ihE, ihO, ihES, ihOS, ihYe, ihYo⟩ := ih hpu (fun x hx => hn x (by simp [hx]))
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro x hx
          rw [gE_cons a u] at hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · have h1 : 0 ≤ a - u.getD 0 0 := by linarith
            exact h1
          · exact ihO x hx
        · intro x hx
          rw [gO_cons a u] at hx
          exact ihE x hx
        · rw [gE_cons a u, List.sum_cons]
          have h1 : 0 ≤ a - u.getD 0 0 := by linarith
          exact add_nonneg h1 ihOS
        · rw [gO_cons a u]
          exact ihES
        · rw [Ye_cons a u]
          exact add_nonneg ha ihYo
        · rw [Yo_cons a u]
          exact ihYe


  have hpt : ∀ p ∈ (t.zipIdx).filter (fun p => decide (p.2 % 2 = 0)),
      0 ≤ p.1 - t.getD (p.2 + 1) 0 := by
    intro p hp
    have hmem : (fun q : ℝ × Nat => q.1 - t.getD (q.2 + 1) 0) p ∈ gE t := by
      show (fun q : ℝ × Nat => q.1 - t.getD (q.2 + 1) 0) p ∈
        ((t.zipIdx.filter (fun q => decide (q.2 % 2 = 0))).map
          (fun q => q.1 - t.getD (q.2 + 1) 0))
      exact List.mem_map.mpr ⟨p, hp, rfl⟩
    exact (key t hpair hnonneg).1 ((fun q : ℝ × Nat => q.1 - t.getD (q.2 + 1) 0) p) hmem
  have hOe : Ye t = (((t.zipIdx).filter (fun p => decide (p.2 % 2 = 0))).map (fun p => p.1)).sum := rfl
  have hEe : Yo t = (((t.zipIdx).filter (fun p => decide (p.2 % 2 = 1))).map (fun p => p.1)).sum := rfl
  have hDe : Ds t = (((t.zipIdx).filter (fun p => decide (p.2 % 2 = 0))).map
      (fun p => p.1 - t.getD (p.2 + 1) 0)).sum := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show Ye t - Yo t = Ds t
    exact hYd t
  · exact hpt
  · show 0 ≤ (gE t).sum
    exact (key t hpair hnonneg).2.2.1
  · show (gE t).sum = ((t.zipIdx.filter (fun p => decide (p.2 % 2 = 0))).map
        (fun p => |p.1 - t.getD (p.2 + 1) 0|)).sum
    exact hsum_congr (t.zipIdx.filter (fun p => decide (p.2 % 2 = 0)))
      (fun p => p.1 - t.getD (p.2 + 1) 0) (fun p => |p.1 - t.getD (p.2 + 1) 0|)
      (fun p hp => (abs_of_nonneg (hpt p hp)).symm)
  · show Ye t + Yo t = t.sum
    exact hYs t
  · have h1 := hYd t
    have h5 := hYs t
    linarith
  · intro hS
    have hYe : 0 ≤ Ye t := (key t hpair hnonneg).2.2.2.2.1
    have hYo : 0 ≤ Yo t := (key t hpair hnonneg).2.2.2.2.2
    have h5 := hYs t
    have hS' : t.sum = 1 := hS
    refine ⟨?_, ?_⟩
    · show 0 ≤ Ye t
      exact hYe
    · show Ye t ≤ 1
      linarith
  
  /- @proof-region region.target-node.session.8910e71c2fa311d1 end -/

end LiuBangXiangYu
