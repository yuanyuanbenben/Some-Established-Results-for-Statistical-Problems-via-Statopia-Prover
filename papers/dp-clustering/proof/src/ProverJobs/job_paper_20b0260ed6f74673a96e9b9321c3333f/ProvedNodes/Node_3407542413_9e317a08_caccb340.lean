import ProverJobs.job_paper_20b0260ed6f74673a96e9b9321c3333f.Vocabulary
import ProverJobs.job_paper_20b0260ed6f74673a96e9b9321c3333f.Base

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_3407542413_9e317a08 : ∀ (s : ℕ) (α : Type) [Fintype α] [DecidableEq α] (b : Fin s → ℕ)
    (hb : ∑ j : Fin s, b j = Fintype.card α),
    Fintype.card {g : α → Fin s // ∀ j : Fin s, (Finset.univ.filter (fun i => g i = j)).card = b j}
      = Nat.multinomial (Finset.univ : Finset (Fin s)) b := by
  /- @proof-region region.target-node.session.1f3d8f4f74abd919 begin -/
  intro s
  induction s with
  | zero =>
    intro α _ _ b hb
    have hcard : Fintype.card α = 0 := by
      rw [← hb]
      simp
    have hsub : Fintype.card {g : α → Fin 0 // ∀ j : Fin 0, (Finset.univ.filter (fun i => g i = j)).card = b j}
        = Fintype.card (α → Fin 0) :=
      Fintype.card_congr
        { toFun := fun g => g.1
          invFun := fun g => ⟨g, fun j => Fin.elim0 j⟩
          left_inv := fun g => Subtype.ext rfl
          right_inv := fun g => rfl }
    rw [hsub, Fintype.card_fun, hcard, Fintype.card_fin]
    simp [Nat.multinomial]
  | succ s ih =>
    intro α _ _ b hb
    let p : (x : Fin (s+1)) → x ≠ 0 → Fin s := fun x hx => ⟨x.val - 1, by
      have hxne : x.val ≠ 0 := fun h => hx (Fin.ext (by simpa using h))
      have hxlt := x.isLt
      omega⟩
    have hp_succ : ∀ (x : Fin (s+1)) (hx : x ≠ 0), (p x hx).succ = x := by
      intro x hx
      have hxne : x.val ≠ 0 := fun h => hx (Fin.ext (by simpa using h))
      apply Fin.ext
      show x.val - 1 + 1 = x.val
      omega
    let C : ℕ := Nat.multinomial (Finset.univ : Finset (Fin s)) (fun k => b k.succ)
    have card_subtype : ∀ (β : Type) [Fintype β] (q : β → Prop) [DecidablePred q],
        Fintype.card {x // q x} = ((Finset.univ : Finset β).filter q).card := by
      intro β _ q _
      rw [← Fintype.card_coe]
      refine Fintype.card_congr ⟨?_, ?_, ?_, ?_⟩
      · exact fun x => ⟨x.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.2⟩⟩
      · exact fun x => ⟨x.1, (Finset.mem_filter.mp x.2).2⟩
      · intro x; exact Subtype.ext rfl
      · intro x; exact Subtype.ext rfl
    have hmaps : Set.MapsTo (fun g : α → Fin (s+1) => Finset.univ.filter (fun i => g i = 0))
        ↑((Finset.univ : Finset (α → Fin (s+1))).filter (fun g => ∀ j : Fin (s+1), (Finset.univ.filter (fun i => g i = j)).card = b j))
        ↑(Finset.powersetCard (b 0) (Finset.univ : Finset α)) := by
      intro g hg
      rw [Finset.mem_coe, Finset.mem_filter] at hg
      rw [Finset.mem_coe, Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, hg.2 0⟩
    have hstep1 : Fintype.card {g : α → Fin (s+1) // ∀ j : Fin (s+1), (Finset.univ.filter (fun i => g i = j)).card = b j}
        = ∑ S ∈ Finset.powersetCard (b 0) (Finset.univ : Finset α),
            Fintype.card {g : α → Fin (s+1) // (∀ j : Fin (s+1), (Finset.univ.filter (fun i => g i = j)).card = b j) ∧ (Finset.univ.filter (fun i => g i = 0)) = S} := by
      rw [card_subtype (α → Fin (s+1)) (fun g => ∀ j : Fin (s+1), (Finset.univ.filter (fun i => g i = j)).card = b j)]
      rw [Finset.card_eq_sum_card_fiberwise hmaps]
      apply Finset.sum_congr rfl
      intro S hS
      rw [card_subtype (α → Fin (s+1)) (fun g => (∀ j : Fin (s+1), (Finset.univ.filter (fun i => g i = j)).card = b j) ∧ (Finset.univ.filter (fun i => g i = 0)) = S)]
      congr 1
      ext g
      simp [Finset.mem_filter]
    have hconst : ∀ (S : Finset α), S.card = b 0 →
        Fintype.card {g : α → Fin (s+1) // (∀ j : Fin (s+1), (Finset.univ.filter (fun i => g i = j)).card = b j) ∧ (Finset.univ.filter (fun i => g i = 0)) = S} = C := by
      intro S hS
      have hsumc : (∑ k : Fin s, b k.succ) = Fintype.card ↥(Sᶜ) := by
        have h1 : b 0 + ∑ k : Fin s, b k.succ = Fintype.card α := by
          rw [← hb, Fin.sum_univ_succ]
        rw [Fintype.card_coe, Finset.card_compl, hS]
        omega
      let inS : (g : α → Fin (s+1)) → ((Finset.univ.filter (fun i => g i = 0)) = S) → (a : α) → g a = 0 → a ∈ S :=
        fun g hg a h0 => by rw [← hg]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0⟩
      let fwd : (g : α → Fin (s+1)) → ((Finset.univ.filter (fun i => g i = 0)) = S) → (↥(Sᶜ) → Fin s) :=
        fun g hg i => p (g i.1) (fun h0 => Finset.mem_compl.mp i.2 (inS g hg i.1 h0))
      let bwd : (↥(Sᶜ) → Fin s) → (α → Fin (s+1)) :=
        fun h a => if ha : a ∈ S then 0 else Fin.succ (h ⟨a, Finset.mem_compl.mpr ha⟩)
      let e : ↥(Sᶜ) ↪ α := ⟨Subtype.val, fun x y h => Subtype.ext h⟩
      have hbwd0 : ∀ (h : ↥(Sᶜ) → Fin s), (Finset.univ.filter (fun i => bwd h i = 0)) = S := by
        intro h
        ext a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h0
          by_contra ha
          simp only [bwd, dif_neg ha] at h0
          exact Fin.succ_ne_zero _ h0
        · intro ha
          exact dif_pos ha
      have hident : ∀ (g : α → Fin (s+1)) (hg : (Finset.univ.filter (fun i => g i = 0)) = S) (k : Fin s),
          (Finset.univ.filter (fun a : α => g a = Fin.succ k))
            = (Finset.univ.filter (fun i : ↥(Sᶜ) => fwd g hg i = k)).map e := by
        intro g hg k
        ext a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
        constructor
        · intro ha
          have hnotS : a ∉ S := by
            intro haS
            have hmem : a ∈ Finset.univ.filter (fun i => g i = 0) := by rw [hg]; exact haS
            have h0 : g a = 0 := (Finset.mem_filter.mp hmem).2
            rw [ha] at h0
            exact Fin.succ_ne_zero k h0
          refine ⟨⟨a, Finset.mem_compl.mpr hnotS⟩, ?_, rfl⟩
          have hfwd' : fwd g hg ⟨a, Finset.mem_compl.mpr hnotS⟩ = p (g a) (fun h0 => Finset.mem_compl.mp (Finset.mem_compl.mpr hnotS) (inS g hg a h0)) := rfl
          rw [hfwd']
          apply Fin.ext
          show (g a).val - 1 = k.val
          rw [ha]
          show k.val + 1 - 1 = k.val
          omega
        · rintro ⟨i, hi, rfl⟩

          have hnotS : i.1 ∉ S := Finset.mem_compl.mp i.2
          have hne : g i.1 ≠ 0 := fun h0 => hnotS (inS g hg i.1 h0)
          have hfwd' : fwd g hg i = p (g i.1) (fun h0 => Finset.mem_compl.mp i.2 (inS g hg i.1 h0)) := rfl
          have hval : (fwd g hg i).val = k.val := by rw [hi]
          rw [hfwd'] at hval
          have hval' : (g i.1).val - 1 = k.val := hval
          have hne' : (g i.1).val ≠ 0 := fun h => hne (Fin.ext (by simpa using h))
          apply Fin.ext
          show (g i.1).val = k.val + 1
          omega
      have hback : ∀ (g : α → Fin (s+1)) (hg : (Finset.univ.filter (fun i => g i = 0)) = S),
          bwd (fwd g hg) = g := by
        intro g hg
        funext a
        by_cases ha : a ∈ S
        · have h0 : g a = 0 := by
            have hmem : a ∈ Finset.univ.filter (fun i => g i = 0) := by rw [hg]; exact ha
            exact (Finset.mem_filter.mp hmem).2
          have hb : bwd (fwd g hg) a = 0 := dif_pos ha
          rw [hb, h0]
        · have hnotS : a ∉ S := ha
          have hb : bwd (fwd g hg) a = Fin.succ (fwd g hg ⟨a, Finset.mem_compl.mpr hnotS⟩) := dif_neg hnotS
          rw [hb]
          apply Fin.ext
          show (g a).val - 1 + 1 = (g a).val
          have hne : g a ≠ 0 := fun h0 => hnotS (inS g hg a h0)
          have hne' : (g a).val ≠ 0 := fun h => hne (Fin.ext (by simpa using h))
          omega
      have hforth : ∀ (h : ↥(Sᶜ) → Fin s), fwd (bwd h) (hbwd0 h) = h := by
        intro h
        funext i
        have hnotS : i.1 ∉ S := Finset.mem_compl.mp i.2
        have hb : bwd h i.1 = Fin.succ (h ⟨i.1, Finset.mem_compl.mpr hnotS⟩) := dif_neg hnotS
        have hstep : (h ⟨i.1, Finset.mem_compl.mpr hnotS⟩).val = (h i).val :=
          congrArg (fun x => (h x).val) (Subtype.ext rfl)
        apply Fin.ext
        show (bwd h i.1).val - 1 = (h i).val
        rw [hb]
        show (h ⟨i.1, Finset.mem_compl.mpr hnotS⟩).val + 1 - 1 = (h i).val
        rw [hstep]
        omega

      have key : Fintype.card {g : α → Fin (s+1) // (∀ j : Fin (s+1), (Finset.univ.filter (fun i => g i = j)).card = b j) ∧ (Finset.univ.filter (fun i => g i = 0)) = S}
          = Fintype.card {h : ↥(Sᶜ) → Fin s // ∀ k : Fin s, (Finset.univ.filter (fun i => h i = k)).card = b k.succ} := by
        apply Fintype.card_congr
        refine
          { toFun := fun gv => ⟨fwd gv.1 gv.2.2, ?_⟩
            invFun := fun hv => ⟨bwd hv.1, ?_, hbwd0 hv.1⟩
            left_inv := fun gv => Subtype.ext (hback gv.1 gv.2.2)
            right_inv := fun hv => Subtype.ext (hforth hv.1) }
        · intro k
          rw [← Finset.card_map, ← hident gv.1 gv.2.2 k]
          exact gv.2.1 (Fin.succ k)
        · intro j
          by_cases hj : j = 0
          · rw [hj, hbwd0 hv.1, hS]
          · have hs : (Finset.univ.filter (fun i : α => bwd hv.1 i = Fin.succ (p j hj))).card = b (Fin.succ (p j hj)) := by
              rw [hident (bwd hv.1) (hbwd0 hv.1) (p j hj), Finset.card_map, hforth hv.1]
              exact hv.2 (p j hj)
            rwa [hp_succ j hj] at hs
      rw [key]
      exact ih ↥(Sᶜ) (fun k => b k.succ) hsumc
    have hstep2 : (∑ S ∈ Finset.powersetCard (b 0) (Finset.univ : Finset α),
            Fintype.card {g : α → Fin (s+1) // (∀ j : Fin (s+1), (Finset.univ.filter (fun i => g i = j)).card = b j) ∧ (Finset.univ.filter (fun i => g i = 0)) = S})
        = ∑ S ∈ Finset.powersetCard (b 0) (Finset.univ : Finset α), C := by
      apply Finset.sum_congr rfl
      intro S hS
      exact hconst S (Finset.mem_powersetCard.mp hS).2
    have hsum_const : (∑ S ∈ Finset.powersetCard (b 0) (Finset.univ : Finset α), C) = (Fintype.card α).choose (b 0) * C := by
      rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, nsmul_eq_mul]
      simp
    have hsum_eq : b 0 + (∑ i ∈ Finset.univ.image (Fin.succ : Fin s → Fin (s+1)), b i) = Fintype.card α := by
      rw [Finset.sum_image]
      · rw [← hb, Fin.sum_univ_succ]
      · intro x _ y _ hxy
        exact Fin.succ_injective s hxy
    have h0 : (0 : Fin (s+1)) ∉ Finset.univ.image (Fin.succ : Fin s → Fin (s+1)) := by
      intro hmem
      obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hmem
      exact Fin.succ_ne_zero k hk
    have hmult_img : Nat.multinomial (Finset.univ.image (Fin.succ : Fin s → Fin (s+1))) b = C := by
      simp only [C, Nat.multinomial]
      have h1 : (Finset.univ.image (Fin.succ : Fin s → Fin (s+1))).sum b = ∑ k : Fin s, b k.succ := by
        rw [Finset.sum_image]
        intro x _ y _ hxy
        exact Fin.succ_injective s hxy
      have h2 : (Finset.univ.image (Fin.succ : Fin s → Fin (s+1))).prod (fun i => (b i).factorial) = ∏ k : Fin s, (b k.succ).factorial := by
        rw [Finset.prod_image]
        intro x _ y _ hxy
        exact Fin.succ_injective s hxy
      rw [h1, h2]

    have hcons_eq : (Finset.univ : Finset (Fin (s+1))) = Finset.cons (0 : Fin (s+1)) (Finset.univ.image (Fin.succ : Fin s → Fin (s+1))) h0 := by
      rw [Finset.cons_eq_insert]
      symm
      apply Finset.eq_univ_of_forall
      intro x
      rw [Finset.mem_insert, Finset.mem_image]
      by_cases hx : x = 0
      · exact Or.inl hx
      · refine Or.inr ⟨⟨x.val - 1, by
          have hxval : x.val ≠ 0 := fun h => hx (Fin.ext (by simpa using h))
          have hxlt := x.isLt
          omega⟩, Finset.mem_univ _, ?_⟩
        apply Fin.ext
        show x.val - 1 + 1 = x.val
        have hxval : x.val ≠ 0 := fun h => hx (Fin.ext (by simpa using h))
        omega
    have hmult : Nat.multinomial (Finset.univ : Finset (Fin (s+1))) b = (Fintype.card α).choose (b 0) * C := by
      rw [hcons_eq, Nat.multinomial_cons, hsum_eq, hmult_img]
    rw [hstep1, hstep2, hsum_const, ← hmult]
  /- @proof-region region.target-node.session.1f3d8f4f74abd919 end -/

end Statlib.Imported
