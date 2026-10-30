import ProverJobs.real_V_eq_15312944933b.Vocabulary
import ProverJobs.real_V_eq_15312944933b.Base

open scoped BigOperators
open LiuBangXiangYu

open scoped BigOperators
namespace LiuBangXiangYu

set_option autoImplicit false in
theorem statopia_math_node_3072499416_ba39391c : ∀ (l : List ℝ) (blocks : List (List ℝ))
    (hflat : blocks.flatten = l),
    ∃ pos : Fin l.length → Fin blocks.length,
      ∀ i : Fin blocks.length,
        (∑ j ∈ Finset.univ.filter (fun j : Fin l.length => pos j = i), l.get j)
          = (blocks.get i).sum := by
  /- @proof-region region.target-node.session.473c84f4b5eea840 begin -/
  intro l blocks hflat
  subst hflat
  induction blocks with
  | nil =>
      exact ⟨Fin.elim0, fun i => i.elim0⟩
  | cons b B ih =>
      obtain ⟨posB, hposB⟩ := ih
      have hsub : ∀ (j : Fin (b :: B).flatten.length), ¬ (j : ℕ) < b.length →
          (j : ℕ) - b.length < B.flatten.length := by
        intro j hj
        have hj' : (j : ℕ) < b.length + B.flatten.length := by
          simpa only [List.flatten_cons, List.length_append] using j.isLt
        omega
      let pos : Fin (b :: B).flatten.length → Fin (b :: B).length := fun j =>
        if h : (j : ℕ) < b.length then ⟨0, Nat.succ_pos B.length⟩
        else Fin.succ (posB ⟨(j : ℕ) - b.length, hsub j h⟩)
      have hpos_lt : ∀ (j : Fin (b :: B).flatten.length) (hj : (j : ℕ) < b.length),
          pos j = (⟨0, Nat.succ_pos B.length⟩ : Fin (b :: B).length) := by
        intro j hj
        simp only [pos, dif_pos hj]
      have hpos_ge : ∀ (j : Fin (b :: B).flatten.length) (hj : ¬ (j : ℕ) < b.length),
          pos j = Fin.succ (posB ⟨(j : ℕ) - b.length, hsub j hj⟩) := by
        intro j hj
        simp only [pos, dif_neg hj]
      refine ⟨pos, ?_⟩
      intro i
      let z : Fin (b :: B).length := ⟨0, Nat.succ_pos B.length⟩
      by_cases hz : (i : ℕ) = 0
      · have hiz : i = z := Fin.ext (by simpa only [z] using hz)
        rw [hiz]
        let emb : Fin b.length → Fin (b :: B).flatten.length := fun k => ⟨(k : ℕ), by
          have hk : (k : ℕ) < b.length + B.flatten.length := by
            have hk' := k.isLt
            omega
          simpa only [List.flatten_cons, List.length_append] using hk⟩
        have h1 : (∑ k ∈ (Finset.univ : Finset (Fin b.length)), b.get k)
              = ∑ j ∈ (Finset.univ : Finset (Fin (b :: B).flatten.length)).filter
                  (fun j => pos j = z), (b :: B).flatten.get j := by
          refine Finset.sum_bij (fun k _ => emb k) (fun k _ => ?_) (fun k1 _ k2 _ h => ?_)
            (fun j hj => ?_) (fun k _ => ?_)
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact hpos_lt (emb k) k.isLt
          · have h' : (emb k1 : Fin (b :: B).flatten.length) = emb k2 := h
            have h'' : (emb k1 : ℕ) = (emb k2 : ℕ) :=
              congrArg (fun x : Fin (b :: B).flatten.length => (x : ℕ)) h'
            exact Fin.ext (by simpa using h'')
          · have hp : pos j = z := by
              simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hj
            have hjlt : (j : ℕ) < b.length := by
              by_contra hcon
              have hge := hpos_ge j hcon
              rw [hp] at hge
              have hv : (posB ⟨(j : ℕ) - b.length, hsub j hcon⟩).val + 1 = 0 := by
                have h := congrArg Fin.val hge
                simpa only [z] using h.symm
              omega
            exact ⟨⟨(j : ℕ), hjlt⟩, Finset.mem_univ _, Fin.ext rfl⟩
          · exact (List.getElem_append_left k.isLt).symm
        have h2 : (∑ k ∈ (Finset.univ : Finset (Fin b.length)), b.get k) = ((b :: B).get z).sum := by
          have hg : ((b :: B).get z) = b := rfl
          rw [hg, ← List.sum_ofFn, List.ofFn_get]
        rw [← h1]
        exact h2
      · have hi_lt : (i : ℕ) < B.length + 1 := by
          simpa only [List.length_cons] using i.isLt
        have hi0 : 0 < (i : ℕ) := Nat.pos_of_ne_zero hz
        obtain ⟨i', hi'⟩ : ∃ i' : Fin B.length, i = Fin.succ i' := by
          refine ⟨⟨(i : ℕ) - 1, by omega⟩, ?_⟩
          apply Fin.ext
          have h1v : ((i : ℕ) - 1) + 1 = (i : ℕ) := by omega
          exact h1v.symm
        have happ : ∀ (l₁ : List ℝ) (k : Fin B.flatten.length),
            (l₁ ++ B.flatten).get ⟨(k : ℕ) + l₁.length, by
              have hk' := k.isLt
              simp only [List.length_append]
              omega⟩ = B.flatten.get k := by
          intro l₁
          induction l₁ with
          | nil =>
              intro k
              rfl
          | cons c l' ihl =>
              intro k
              exact ihl k
        rw [hi']
        let emb2 : Fin B.flatten.length → Fin (b :: B).flatten.length := fun k =>
          ⟨(k : ℕ) + b.length, by
            have hk' := k.isLt
            have hk'' : (k : ℕ) + b.length < b.length + B.flatten.length := by omega
            simpa only [List.flatten_cons, List.length_append] using hk''⟩
        have h1' : (∑ k ∈ ((Finset.univ : Finset (Fin B.flatten.length)).filter
                (fun k => posB k = i')), B.flatten.get k)
              = ∑ j ∈ ((Finset.univ : Finset (Fin (b :: B).flatten.length)).filter
                  (fun j => pos j = Fin.succ i')), (b :: B).flatten.get j := by
          refine Finset.sum_bij (fun k _ => emb2 k) (fun k hk => ?_) (fun k1 _ k2 _ h => ?_)
            (fun j hj => ?_) (fun k _ => ?_)
          · have hpk : posB k = i' := by
              simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hk
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            have hnot : ¬ (emb2 k : ℕ) < b.length := by
              simp only [emb2]
              omega
            have hkk : (⟨(emb2 k : ℕ) - b.length, hsub (emb2 k) hnot⟩ : Fin B.flatten.length) = k := by
              apply Fin.ext
              simp only [emb2]
              omega
            rw [hpos_ge (emb2 k) hnot, hkk, hpk]
          · have h'' : (emb2 k1 : ℕ) = (emb2 k2 : ℕ) :=
              congrArg (fun x : Fin (b :: B).flatten.length => (x : ℕ)) h
            have h4 : (k1 : ℕ) + b.length = (k2 : ℕ) + b.length := by
              simpa only [emb2] using h''
            exact Fin.ext (by omega)
          · have hp : pos j = Fin.succ i' := by
              simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hj
            have hjge : ¬ (j : ℕ) < b.length := by
              intro hcon
              have hpz : pos j = z := hpos_lt j hcon
              rw [hpz] at hp
              have h5 : (0 : ℕ) = (i' : ℕ) + 1 := by
                have h6 := congrArg Fin.val hp
                simpa only [z] using h6
              omega
            have hpk : posB ⟨(j : ℕ) - b.length, hsub j hjge⟩ = i' := by
              have h7 : (posB ⟨(j : ℕ) - b.length, hsub j hjge⟩).val + 1 = (i' : ℕ) + 1 := by
                have h8 := congrArg Fin.val (show Fin.succ (posB ⟨(j : ℕ) - b.length, hsub j hjge⟩) = Fin.succ i' by
                  rw [← hpos_ge j hjge]
                  exact hp)
                simpa using h8
              exact Fin.ext (by omega)
            refine ⟨⟨(j : ℕ) - b.length, hsub j hjge⟩, ?_, ?_⟩
            · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              exact hpk
            · apply Fin.ext
              simp only [emb2]
              omega
          · have h9 : (b ++ B.flatten).get (emb2 k) = B.flatten.get k := happ b k
            exact h9.symm
        have h2' : ((b :: B).get (Fin.succ i')).sum = (B.get i').sum := rfl
        have hB : (∑ k ∈ ((Finset.univ : Finset (Fin B.flatten.length)).filter
              (fun k => posB k = i')), B.flatten.get k) = (B.get i').sum := hposB i'
        rw [← h1', hB]
        exact h2'.symm
  /- @proof-region region.target-node.session.473c84f4b5eea840 end -/

end LiuBangXiangYu
