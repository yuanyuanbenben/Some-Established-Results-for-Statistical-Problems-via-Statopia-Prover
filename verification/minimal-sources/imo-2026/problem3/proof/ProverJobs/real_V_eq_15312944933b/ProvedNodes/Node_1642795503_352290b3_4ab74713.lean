import ProverJobs.real_V_eq_15312944933b.Vocabulary
import ProverJobs.real_V_eq_15312944933b.Base

open scoped BigOperators
open LiuBangXiangYu

open scoped BigOperators
namespace LiuBangXiangYu

set_option autoImplicit false in
theorem statopia_math_node_1642795503_352290b3 : ∀ (β : Type) [Fintype β] [DecidableEq β]
    (K : ℕ) (a b : Fin K → β) (W : β → ℝ)
    (h1 : ∃ u : β, W u ≠ 0)
    (h5 : ∀ u : β, ∃ e : Fin K, a e = u ∨ b e = u)
    (h6 : (Finset.univ.filter (fun u : β => W u = 0)).card ≤ 1)
    (h7 : K ≤ Fintype.card β - 1),
    ∃ S : Finset β, S.Nonempty ∧ (∃ u ∈ S, W u ≠ 0) ∧
      (∀ e : Fin K, (a e ∈ S ↔ b e ∈ S)) ∧
      (∃ ε : β → ℝ, (∀ u ∈ S, ε u = 1 ∨ ε u = -1) ∧ (∀ u ∉ S, ε u = 0) ∧
        (∀ e : Fin K, a e ∈ S → a e ≠ b e ∧ ε (a e) ≠ ε (b e))) := by
  /- @proof-region region.target-node.session.6d75103721bb58ec begin -/
  intro β _ _ K a b W h1 h5 h6 h7
  classical
  let EF : Finset β → Finset (Fin K) := fun V => Finset.univ.filter (fun e => a e ∈ V ∧ b e ∈ V)
  let HD : Finset β → β → ℕ := fun V u =>
    ((EF V).filter (fun e => a e = u)).card + ((EF V).filter (fun e => b e = u)).card
  have hEF : ∀ V e, e ∈ EF V ↔ a e ∈ V ∧ b e ∈ V := by
    intro V e
    simp [EF]
  have hHD : ∀ V u, HD V u =
      ((EF V).filter (fun e => a e = u)).card + ((EF V).filter (fun e => b e = u)).card :=
    fun V u => rfl
  have hsum : ∀ V : Finset β, ∑ u ∈ V, HD V u = 2 * (EF V).card := by
    intro V
    have hma : Set.MapsTo a (↑(EF V) : Set (Fin K)) (↑V : Set β) := by
      intro e he
      exact ((hEF V e).mp (Finset.mem_coe.mp he)).1
    have hmb : Set.MapsTo b (↑(EF V) : Set (Fin K)) (↑V : Set β) := by
      intro e he
      exact ((hEF V e).mp (Finset.mem_coe.mp he)).2
    have ha := Finset.card_eq_sum_card_fiberwise (f := a) hma
    have hb := Finset.card_eq_sum_card_fiberwise (f := b) hmb
    have hexp : ∑ u ∈ V, HD V u
        = ∑ u ∈ V, (((EF V).filter (fun e => a e = u)).card
            + ((EF V).filter (fun e => b e = u)).card) :=
      Finset.sum_congr rfl (fun u _ => hHD V u)
    rw [hexp, Finset.sum_add_distrib, ← ha, ← hb]
    ring
  have hleaf : ∀ V : Finset β, V.Nonempty → (∀ u ∈ V, 1 ≤ HD V u) →
      (EF V).card ≤ V.card - 1 → ∃ v ∈ V, HD V v = 1 := by
    intro V hVne hdeg hsize
    by_contra hcon
    push_neg at hcon
    have h2 : ∀ u ∈ V, 2 ≤ HD V u := by
      intro u hu
      have h1u := hdeg u hu
      have hnu := hcon u hu
      omega
    have hle : (∑ u ∈ V, (2 : ℕ)) ≤ ∑ u ∈ V, HD V u := Finset.sum_le_sum h2
    have hconst : (∑ u ∈ V, (2 : ℕ)) = V.card * 2 := by simp
    have htot := hsum V
    have hpos : 0 < V.card := Finset.card_pos.mpr hVne
    omega
  have key : ∀ V : Finset β, V.Nonempty → (∀ u ∈ V, 1 ≤ HD V u) →
      (EF V).card ≤ V.card - 1 → (V.filter (fun u => W u = 0)).card ≤ 1 →
      ∃ S : Finset β, S ⊆ V ∧ S.Nonempty ∧ (∃ u ∈ S, W u ≠ 0) ∧
        (∀ e : Fin K, a e ∈ V → b e ∈ V → (a e ∈ S ↔ b e ∈ S)) ∧
        (∃ ε : β → ℝ, (∀ u ∈ S, ε u = 1 ∨ ε u = -1) ∧ (∀ u ∉ S, ε u = 0) ∧
          (∀ e : Fin K, a e ∈ V → b e ∈ V → a e ∈ S → ε (a e) ≠ ε (b e))) := by
    suffices H : ∀ n : ℕ, ∀ V : Finset β, V.card ≤ n → V.Nonempty →
        (∀ u ∈ V, 1 ≤ HD V u) → (EF V).card ≤ V.card - 1 →
        (V.filter (fun u => W u = 0)).card ≤ 1 →
        ∃ S : Finset β, S ⊆ V ∧ S.Nonempty ∧ (∃ u ∈ S, W u ≠ 0) ∧
          (∀ e : Fin K, a e ∈ V → b e ∈ V → (a e ∈ S ↔ b e ∈ S)) ∧
          (∃ ε : β → ℝ, (∀ u ∈ S, ε u = 1 ∨ ε u = -1) ∧ (∀ u ∉ S, ε u = 0) ∧
            (∀ e : Fin K, a e ∈ V → b e ∈ V → a e ∈ S → ε (a e) ≠ ε (b e))) from
      fun V => H V.card V le_rfl
    intro n
    induction n with
    | zero =>
      intro V hcard hVne hdeg hsize hzero
      exact absurd (Finset.card_pos.mpr hVne) (by omega)
    | succ n ih =>
      intro V hcard hVne hdeg hsize hzero
      by_cases hsmall : V.card ≤ n
      · exact ih V hsmall hVne hdeg hsize hzero
      · have hVc : V.card = n + 1 := by omega
        obtain ⟨v, hvV, hvdeg⟩ := hleaf V hVne hdeg hsize
        have hsplit : ((EF V).filter (fun e => a e = v)).card
            + ((EF V).filter (fun e => b e = v)).card = 1 := by
          have h := hHD V v
          omega
        have hloop : ¬ ∃ e ∈ EF V, a e = v ∧ b e = v := by
          rintro ⟨e, heV, hae, hbe⟩
          have h1 : 1 ≤ ((EF V).filter (fun e => a e = v)).card :=
            Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨heV, hae⟩⟩
          have h2 : 1 ≤ ((EF V).filter (fun e => b e = v)).card :=
            Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨heV, hbe⟩⟩
          omega
        have hEE : ((EF V).filter (fun e => a e = v ∨ b e = v)).card = 1 := by
          have hdisj : Disjoint ((EF V).filter (fun e => a e = v))
              ((EF V).filter (fun e => b e = v)) := by
            rw [Finset.disjoint_left]
            intro e he1 he2
            simp only [Finset.mem_filter] at he1 he2
            exact hloop ⟨e, he1.1, he1.2, he2.2⟩
          rw [Finset.filter_or, Finset.card_union_of_disjoint hdisj]
          exact hsplit
        obtain ⟨e0, he0⟩ := Finset.card_eq_one.mp hEE
        have he0f : e0 ∈ (EF V).filter (fun e => a e = v ∨ b e = v) := by
          rw [he0]; simp
        have he0mem : e0 ∈ EF V := (Finset.mem_filter.mp he0f).1
        have he0or : a e0 = v ∨ b e0 = v := (Finset.mem_filter.mp he0f).2
        have hnotloop : ¬ (a e0 = v ∧ b e0 = v) := by
          rintro ⟨ha, hb⟩
          exact hloop ⟨e0, he0mem, ha, hb⟩
        have huniq : ∀ e ∈ EF V, (a e = v ∨ b e = v) → e = e0 := by
          intro e heV heor
          have hmem : e ∈ (EF V).filter (fun e => a e = v ∨ b e = v) :=
            Finset.mem_filter.mpr ⟨heV, heor⟩
          rw [he0] at hmem
          simpa using hmem
        let u0 : β := if a e0 = v then b e0 else a e0
        have hu0val : u0 = (if a e0 = v then b e0 else a e0) := rfl
        have hu0V : u0 ∈ V := by
          rw [hu0val]
          by_cases ha : a e0 = v
          · rw [if_pos ha]
            exact ((hEF V e0).mp he0mem).2
          · rw [if_neg ha]
            exact ((hEF V e0).mp he0mem).1
        have hu0nev : u0 ≠ v := by
          rw [hu0val]
          by_cases ha : a e0 = v
          · rw [if_pos ha]
            intro h
            exact hnotloop ⟨ha, h⟩
          · rw [if_neg ha]
            intro h
            exact ha h
        have he0ends : (a e0 = v ∧ b e0 = u0) ∨ (a e0 = u0 ∧ b e0 = v) := by
          rw [hu0val]
          by_cases ha : a e0 = v
          · exact Or.inl ⟨ha, by rw [if_pos ha]⟩
          · exact Or.inr ⟨by rw [if_neg ha], he0or.resolve_left ha⟩
        by_cases hA : HD V u0 = 1
        · have hsplitu : ((EF V).filter (fun e => a e = u0)).card
              + ((EF V).filter (fun e => b e = u0)).card = 1 := by
            have h := hHD V u0
            omega
          have hloopu : ¬ ∃ e ∈ EF V, a e = u0 ∧ b e = u0 := by
            rintro ⟨e, heV, hae, hbe⟩
            have h1 : 1 ≤ ((EF V).filter (fun e => a e = u0)).card :=
              Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨heV, hae⟩⟩
            have h2 : 1 ≤ ((EF V).filter (fun e => b e = u0)).card :=
              Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨heV, hbe⟩⟩
            omega
          have hEEu : ((EF V).filter (fun e => a e = u0 ∨ b e = u0)).card = 1 := by
            have hdisj : Disjoint ((EF V).filter (fun e => a e = u0))
                ((EF V).filter (fun e => b e = u0)) := by
              rw [Finset.disjoint_left]
              intro e he1 he2
              simp only [Finset.mem_filter] at he1 he2
              exact hloopu ⟨e, he1.1, he1.2, he2.2⟩
            rw [Finset.filter_or, Finset.card_union_of_disjoint hdisj]
            exact hsplitu
          obtain ⟨e1, he1⟩ := Finset.card_eq_one.mp hEEu
          have huniq1 : ∀ e ∈ EF V, (a e = u0 ∨ b e = u0) → e = e1 := by
            intro e heV heor
            have hmem : e ∈ (EF V).filter (fun e => a e = u0 ∨ b e = u0) :=
              Finset.mem_filter.mpr ⟨heV, heor⟩
            rw [he1] at hmem
            simpa using hmem
          have he0eqe1 : e0 = e1 := by
            rcases he0ends with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact huniq1 e0 he0mem (Or.inr h2)
            · exact huniq1 e0 he0mem (Or.inl h1)
          let eps : β → ℝ := fun u => if u = v then 1 else if u = u0 then -1 else 0
          have hepsval : ∀ u : β, eps u =
              (if u = v then (1 : ℝ) else if u = u0 then (-1 : ℝ) else 0) :=
            fun u => rfl
          have hepsv : eps v = 1 := by
            rw [hepsval v]; simp
          have hepsu : eps u0 = -1 := by
            rw [hepsval u0, if_neg hu0nev]; simp
          have heps0 : ∀ u, u ≠ v → u ≠ u0 → eps u = 0 := by
            intro u h1 h2
            rw [hepsval u, if_neg h1, if_neg h2]
          refine ⟨({v, u0} : Finset β), ?_, ⟨v, by simp⟩, ?_, ?_, eps, ?_, ?_, ?_⟩
          · intro u hu
            simp only [Finset.mem_insert, Finset.mem_singleton] at hu
            rcases hu with h | h
            · rw [h]; exact hvV
            · rw [h]; exact hu0V
          · by_contra hc
            push_neg at hc
            have hv0 : W v = 0 := hc v (by simp)
            have hu00 : W u0 = 0 := hc u0 (by simp)
            have hvZ : v ∈ V.filter (fun u => W u = 0) := Finset.mem_filter.mpr ⟨hvV, hv0⟩
            have huZ : u0 ∈ V.filter (fun u => W u = 0) := Finset.mem_filter.mpr ⟨hu0V, hu00⟩
            exact hu0nev ((Finset.card_le_one.mp hzero v hvZ u0 huZ).symm)
          · intro e haeV hbeV
            have heV : e ∈ EF V := (hEF V e).mpr ⟨haeV, hbeV⟩
            have hgeta : a e ∈ ({v, u0} : Finset β) → e = e0 := by
              intro hae
              have hor : a e = v ∨ a e = u0 := by
                simpa only [Finset.mem_insert, Finset.mem_singleton] using hae
              rcases hor with h | h
              · exact huniq e heV (Or.inl h)
              · exact (huniq1 e heV (Or.inl h)).trans he0eqe1.symm
            have hgetb : b e ∈ ({v, u0} : Finset β) → e = e0 := by
              intro hbe
              have hor : b e = v ∨ b e = u0 := by
                simpa only [Finset.mem_insert, Finset.mem_singleton] using hbe
              rcases hor with h | h
              · exact huniq e heV (Or.inr h)
              · exact (huniq1 e heV (Or.inr h)).trans he0eqe1.symm
            constructor
            · intro hae
              rw [hgeta hae]
              rcases he0ends with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h2] <;> simp
            · intro hbe
              rw [hgetb hbe]
              rcases he0ends with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1] <;> simp
          · intro u hu
            have huor : u = v ∨ u = u0 := by
              simpa only [Finset.mem_insert, Finset.mem_singleton] using hu
            rcases huor with h | h
            · left; rw [h]; exact hepsv
            · right; rw [h]; exact hepsu
          · intro u hu
            have h1 : u ≠ v := fun h => hu (by simp [h])
            have h2 : u ≠ u0 := fun h => hu (by simp [h])
            exact heps0 u h1 h2
          · intro e haeV hbeV haeS
            have heV : e ∈ EF V := (hEF V e).mpr ⟨haeV, hbeV⟩
            have hor : a e = v ∨ a e = u0 := by
              simpa only [Finset.mem_insert, Finset.mem_singleton] using haeS
            have hee0 : e = e0 := by
              rcases hor with h | h
              · exact huniq e heV (Or.inl h)
              · exact (huniq1 e heV (Or.inl h)).trans he0eqe1.symm
            rw [hee0]
            rcases he0ends with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · rw [h1, h2, hepsv, hepsu]; norm_num
            · rw [h1, h2, hepsu, hepsv]; norm_num
        · have hge : 2 ≤ HD V u0 := by
            have h1 := hdeg u0 hu0V
            omega
          have he0endV : a e0 ∈ ({v, u0} : Finset β) ∧ b e0 ∈ ({v, u0} : Finset β) := by
            rcases he0ends with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact ⟨by rw [h1]; simp, by rw [h2]; simp⟩
            · exact ⟨by rw [h1]; simp, by rw [h2]; simp⟩
          have hother : ∃ e' ∈ EF V, e' ≠ e0 ∧ (a e' = u0 ∨ b e' = u0) := by
            by_contra hc
            have hsubS : (EF V).filter (fun e => a e = u0 ∨ b e = u0) ⊆ ({e0} : Finset (Fin K)) := by
              intro e he
              rw [Finset.mem_singleton]
              by_contra hne
              exact hc ⟨e, (Finset.mem_filter.mp he).1, hne, (Finset.mem_filter.mp he).2⟩
            have hsubA : (EF V).filter (fun e => a e = u0) ⊆ ({e0} : Finset (Fin K)) := by
              intro e he
              exact hsubS (Finset.mem_filter.mpr
                ⟨(Finset.mem_filter.mp he).1, Or.inl (Finset.mem_filter.mp he).2⟩)
            have hsubB : (EF V).filter (fun e => b e = u0) ⊆ ({e0} : Finset (Fin K)) := by
              intro e he
              exact hsubS (Finset.mem_filter.mpr
                ⟨(Finset.mem_filter.mp he).1, Or.inr (Finset.mem_filter.mp he).2⟩)
            have hA1 : ((EF V).filter (fun e => a e = u0)).card ≤ 1 := by
              have hle := Finset.card_le_card hsubA
              have h2 : ({e0} : Finset (Fin K)).card = 1 := by simp
              omega
            have hB1 : ((EF V).filter (fun e => b e = u0)).card ≤ 1 := by
              have hle := Finset.card_le_card hsubB
              have h2 : ({e0} : Finset (Fin K)).card = 1 := by simp
              omega
            have hd := hHD V u0
            have hApos : 0 < ((EF V).filter (fun e => a e = u0)).card := by omega
            have hBpos : 0 < ((EF V).filter (fun e => b e = u0)).card := by omega
            obtain ⟨e1, he1⟩ := Finset.card_pos.mp hApos
            obtain ⟨e2, he2⟩ := Finset.card_pos.mp hBpos
            have h1e : e1 = e0 := by simpa using hsubA he1
            have h2e : e2 = e0 := by simpa using hsubB he2
            have ha0 : a e0 = u0 := by
              rw [← h1e]
              exact (Finset.mem_filter.mp he1).2
            have hb0 : b e0 = u0 := by
              rw [← h2e]
              exact (Finset.mem_filter.mp he2).2
            rcases he0or with h | h
            · exact hu0nev (ha0.symm.trans h)
            · exact hu0nev (hb0.symm.trans h)
          obtain ⟨e', he'V, he'ne, he'tou⟩ := hother
          have hEF' : EF (V.erase v) = (EF V).erase e0 := by
            ext e
            constructor
            · intro he
              have hpair := (hEF (V.erase v) e).mp he
              have hne : e ≠ e0 := by
                intro hee0
                rw [hee0] at hpair
                rcases he0ends with ⟨h1, h2⟩ | ⟨h1, h2⟩
                · exact (Finset.mem_erase.mp hpair.1).1 h1
                · exact (Finset.mem_erase.mp hpair.2).1 h2
              refine Finset.mem_erase.mpr ⟨hne, ?_⟩
              exact (hEF V e).mpr ⟨(Finset.mem_erase.mp hpair.1).2, (Finset.mem_erase.mp hpair.2).2⟩
            · intro he
              obtain ⟨hne, hmemV⟩ := Finset.mem_erase.mp he
              have hpair := (hEF V e).mp hmemV
              refine (hEF (V.erase v) e).mpr ⟨?_, ?_⟩
              · exact Finset.mem_erase.mpr ⟨fun h => hne (huniq e hmemV (Or.inl h)), hpair.1⟩
              · exact Finset.mem_erase.mpr ⟨fun h => hne (huniq e hmemV (Or.inr h)), hpair.2⟩
          have hV'ne : (V.erase v).Nonempty := ⟨u0, Finset.mem_erase.mpr ⟨hu0nev, hu0V⟩⟩
          have hV'card : (V.erase v).card ≤ n := by
            have hcardv : (V.erase v).card = V.card - 1 := Finset.card_erase_of_mem hvV
            omega
          have hHD' : ∀ u : β, HD (V.erase v) u =
              (((EF V).erase e0).filter (fun e => a e = u)).card
              + (((EF V).erase e0).filter (fun e => b e = u)).card := by
            intro u
            rw [hHD, hEF']
          have hcover : ∀ u ∈ V, ∃ e ∈ EF V, a e = u ∨ b e = u := by
            intro u hu
            have h1 := hdeg u hu
            by_cases hA0 : 0 < ((EF V).filter (fun e => a e = u)).card
            · obtain ⟨e, he⟩ := Finset.card_pos.mp hA0
              exact ⟨e, (Finset.mem_filter.mp he).1, Or.inl (Finset.mem_filter.mp he).2⟩
            · have hB0 : 0 < ((EF V).filter (fun e => b e = u)).card := by
                have hd := hHD V u
                omega
              obtain ⟨e, he⟩ := Finset.card_pos.mp hB0
              exact ⟨e, (Finset.mem_filter.mp he).1, Or.inr (Finset.mem_filter.mp he).2⟩
          have hdeg' : ∀ u ∈ V.erase v, 1 ≤ HD (V.erase v) u := by
            intro u hu
            obtain ⟨hunev, huV⟩ := Finset.mem_erase.mp hu
            rcases eq_or_ne u u0 with h | hne
            · rw [h, hHD']
              have heV' : e' ∈ (EF V).erase e0 := Finset.mem_erase.mpr ⟨he'ne, he'V⟩
              rcases he'tou with ht | ht
              · have hmem : e' ∈ ((EF V).erase e0).filter (fun e => a e = u0) :=
                  Finset.mem_filter.mpr ⟨heV', ht⟩
                have hp : 0 < (((EF V).erase e0).filter (fun e => a e = u0)).card :=
                  Finset.card_pos.mpr ⟨e', hmem⟩
                omega
              · have hmem : e' ∈ ((EF V).erase e0).filter (fun e => b e = u0) :=
                  Finset.mem_filter.mpr ⟨heV', ht⟩
                have hp : 0 < (((EF V).erase e0).filter (fun e => b e = u0)).card :=
                  Finset.card_pos.mpr ⟨e', hmem⟩
                omega
            · obtain ⟨e, heV, heu⟩ := hcover u huV
              have hene : e ≠ e0 := by
                intro hee0
                rw [hee0] at heu
                have hu2 : u = v ∨ u = u0 := by
                  rcases he0ends with ⟨h1, h2⟩ | ⟨h1, h2⟩
                  · rcases heu with hh | hh
                    · exact Or.inl (hh.symm.trans h1)
                    · exact Or.inr (hh.symm.trans h2)
                  · rcases heu with hh | hh
                    · exact Or.inr (hh.symm.trans h1)
                    · exact Or.inl (hh.symm.trans h2)
                rcases hu2 with hh | hh
                · exact hunev hh
                · exact hne hh
              have heV' : e ∈ (EF V).erase e0 := Finset.mem_erase.mpr ⟨hene, heV⟩
              rw [hHD']
              rcases heu with hh | hh
              · have hmem : e ∈ ((EF V).erase e0).filter (fun e => a e = u) :=
                  Finset.mem_filter.mpr ⟨heV', hh⟩
                have hp : 0 < (((EF V).erase e0).filter (fun e => a e = u)).card :=
                  Finset.card_pos.mpr ⟨e, hmem⟩
                omega
              · have hmem : e ∈ ((EF V).erase e0).filter (fun e => b e = u) :=
                  Finset.mem_filter.mpr ⟨heV', hh⟩
                have hp : 0 < (((EF V).erase e0).filter (fun e => b e = u)).card :=
                  Finset.card_pos.mpr ⟨e, hmem⟩
                omega
          have hsize' : (EF (V.erase v)).card ≤ (V.erase v).card - 1 := by
            have hV'le : 1 ≤ (V.erase v).card := Finset.card_pos.mpr hV'ne
            have hcardv : (V.erase v).card = V.card - 1 := Finset.card_erase_of_mem hvV
            have hcarde : (EF (V.erase v)).card = (EF V).card - 1 := by
              rw [hEF', Finset.card_erase_of_mem he0mem]
            rw [hcarde, hcardv]
            omega
          have hzero' : ((V.erase v).filter (fun u => W u = 0)).card ≤ 1 := by
            have hsub : (V.erase v).filter (fun u => W u = 0) ⊆ V.filter (fun u => W u = 0) := by
              intro u hu2
              obtain ⟨hu1, hu3⟩ := Finset.mem_filter.mp hu2
              exact Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp hu1).2, hu3⟩
            exact le_trans (Finset.card_le_card hsub) hzero
          obtain ⟨S', hS'sub, hS'ne, hS'real, hS'cl, ε', hε'S, hε'out, hε'prop⟩ :=
            ih (V.erase v) hV'card hV'ne hdeg' hsize' hzero'
          have hS'subV : S' ⊆ V := fun u hu2 => (Finset.mem_erase.mp (hS'sub hu2)).2
          have hvnotS' : v ∉ S' := fun hh => (Finset.mem_erase.mp (hS'sub hh)).1 rfl
          have hclV' : ∀ e, e ∈ EF (V.erase v) → (a e ∈ S' ↔ b e ∈ S') := by
            intro e he
            exact hS'cl e ((hEF (V.erase v) e).mp he).1 ((hEF (V.erase v) e).mp he).2
          have hproperV' : ∀ e, e ∈ EF (V.erase v) → a e ∈ S' → ε' (a e) ≠ ε' (b e) := by
            intro e he ha
            exact hε'prop e ((hEF (V.erase v) e).mp he).1 ((hEF (V.erase v) e).mp he).2 ha
          have he0case : ∀ e ∈ EF V, e = e0 ∨ e ∈ EF (V.erase v) := by
            intro e he
            by_cases hh : e = e0
            · exact Or.inl hh
            · exact Or.inr (by rw [hEF']; exact Finset.mem_erase.mpr ⟨hh, he⟩)
          have hmemconv : ∀ u : β, u ≠ v → (u ∈ insert v S' ↔ u ∈ S') := by
            intro u hh
            rw [Finset.mem_insert]
            exact ⟨fun hx => hx.elim (fun h1 => absurd h1 hh) (fun h1 => h1), fun hx => Or.inr hx⟩
          by_cases hu0S' : u0 ∈ S'
          · let eps : β → ℝ := fun u => if u = v then -(ε' u0) else ε' u
            have hepsval : ∀ u : β, eps u = (if u = v then -(ε' u0) else ε' u) := fun u => rfl
            have hepsv : eps v = -(ε' u0) := by rw [hepsval v]; simp
            have hepsne : ∀ u, u ≠ v → eps u = ε' u := by
              intro u hh; rw [hepsval u, if_neg hh]
            have hε'u0 : ε' u0 = 1 ∨ ε' u0 = -1 := hε'S u0 hu0S'
            refine ⟨insert v S', ?_, ?_, ?_, ?_, eps, ?_, ?_, ?_⟩
            · intro u hu2
              rcases Finset.mem_insert.mp hu2 with hh | hh
              · rw [hh]; exact hvV
              · exact hS'subV hh
            · exact ⟨u0, Finset.mem_insert.mpr (Or.inr hu0S')⟩
            · obtain ⟨u, hu2, hWu⟩ := hS'real
              exact ⟨u, Finset.mem_insert.mpr (Or.inr hu2), hWu⟩
            · intro e haeV hbeV
              have heV : e ∈ EF V := (hEF V e).mpr ⟨haeV, hbeV⟩
              rcases he0case e heV with hh | hh
              · rw [hh]
                rcases he0ends with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
                  rw [h1, h2] <;> simp [hu0nev, hu0S']
              · have hne1 : a e ≠ v := (Finset.mem_erase.mp ((hEF (V.erase v) e).mp hh).1).1
                have hne2 : b e ≠ v := (Finset.mem_erase.mp ((hEF (V.erase v) e).mp hh).2).1
                rw [hmemconv (a e) hne1, hmemconv (b e) hne2]
                exact hclV' e hh
            · intro u hu2
              rcases Finset.mem_insert.mp hu2 with hh | hh
              · rw [hh, hepsv]
                rcases hε'u0 with h1 | h1 <;> rw [h1] <;> norm_num
              · rw [hepsne u (fun hh2 => hvnotS' (hh2 ▸ hh))]
                exact hε'S u hh
            · intro u hu2
              have hne : u ≠ v := fun hh => hu2 (Finset.mem_insert.mpr (Or.inl hh))
              rw [hepsne u hne]
              exact hε'out u (fun hh => hu2 (Finset.mem_insert.mpr (Or.inr hh)))
            · intro e haeV hbeV haeS
              have heV : e ∈ EF V := (hEF V e).mpr ⟨haeV, hbeV⟩
              rcases he0case e heV with hh | hh
              · rw [hh] at haeS ⊢
                rcases he0ends with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
                  rw [h1, h2, hepsv, hepsne u0 hu0nev] <;>
                  (rcases hε'u0 with h3 | h3 <;> rw [h3] <;> norm_num)
              · have hne1 : a e ≠ v := (Finset.mem_erase.mp ((hEF (V.erase v) e).mp hh).1).1
                have hne2 : b e ≠ v := (Finset.mem_erase.mp ((hEF (V.erase v) e).mp hh).2).1
                rw [hepsne (a e) hne1, hepsne (b e) hne2]
                exact hproperV' e hh ((hmemconv (a e) hne1).mp haeS)
          · have hna : a e0 ∉ S' := by
              intro hh
              rcases Finset.mem_insert.mp he0endV.1 with h1 | h1
              · exact hvnotS' (h1.symm ▸ hh)
              · have h1' : a e0 = u0 := by simpa using h1
                exact hu0S' (h1'.symm ▸ hh)
            have hnb : b e0 ∉ S' := by
              intro hh
              rcases Finset.mem_insert.mp he0endV.2 with h1 | h1
              · exact hvnotS' (h1.symm ▸ hh)
              · have h1' : b e0 = u0 := by simpa using h1
                exact hu0S' (h1'.symm ▸ hh)
            refine ⟨S', hS'subV, hS'ne, hS'real, ?_, ε', hε'S, hε'out, ?_⟩
            · intro e haeV hbeV
              have heV : e ∈ EF V := (hEF V e).mpr ⟨haeV, hbeV⟩
              rcases he0case e heV with hh | hh
              · rw [hh]
                exact ⟨fun hx => absurd hx hna, fun hx => absurd hx hnb⟩
              · exact hclV' e hh
            · intro e haeV hbeV haeS
              have heV : e ∈ EF V := (hEF V e).mpr ⟨haeV, hbeV⟩
              rcases he0case e heV with hh | hh
              · rw [hh] at haeS
                exact absurd haeS hna
              · exact hproperV' e hh haeS
  have hdegU : ∀ u ∈ (Finset.univ : Finset β), 1 ≤ HD Finset.univ u := by
    intro u _
    obtain ⟨e, he⟩ := h5 u
    have hemem : e ∈ EF Finset.univ :=
      (hEF Finset.univ e).mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩
    rcases he with h | h
    · have hmem : e ∈ (EF Finset.univ).filter (fun e => a e = u) :=
        Finset.mem_filter.mpr ⟨hemem, h⟩
      have hc : 0 < ((EF Finset.univ).filter (fun e => a e = u)).card :=
        Finset.card_pos.mpr ⟨e, hmem⟩
      have hd := hHD Finset.univ u
      omega
    · have hmem : e ∈ (EF Finset.univ).filter (fun e => b e = u) :=
        Finset.mem_filter.mpr ⟨hemem, h⟩
      have hc : 0 < ((EF Finset.univ).filter (fun e => b e = u)).card :=
        Finset.card_pos.mpr ⟨e, hmem⟩
      have hd := hHD Finset.univ u
      omega
  have hsizeU : (EF Finset.univ).card ≤ (Finset.univ : Finset β).card - 1 := by
    have hsub : EF Finset.univ ⊆ (Finset.univ : Finset (Fin K)) := fun x _ => Finset.mem_univ x
    have hle : (EF Finset.univ).card ≤ K := by
      have h := Finset.card_le_card hsub
      rwa [Finset.card_univ, Fintype.card_fin] at h
    have hcu : (Finset.univ : Finset β).card = Fintype.card β := Finset.card_univ
    omega
  have hzeroU : ((Finset.univ : Finset β).filter (fun u => W u = 0)).card ≤ 1 := h6
  have hneU : (Finset.univ : Finset β).Nonempty := by
    obtain ⟨u, _⟩ := h1
    exact ⟨u, Finset.mem_univ u⟩
  obtain ⟨S, hSsub, hSne, hSreal, hclosed, ε, hεS, hεout, hεprop⟩ :=
    key (Finset.univ : Finset β) hneU hdegU hsizeU hzeroU
  refine ⟨S, hSne, hSreal, ?_, ε, hεS, hεout, ?_⟩
  · intro e
    exact hclosed e (Finset.mem_univ (a e)) (Finset.mem_univ (b e))
  · intro e haeS
    refine ⟨?_, hεprop e (Finset.mem_univ (a e)) (Finset.mem_univ (b e)) haeS⟩
    intro h
    exact hεprop e (Finset.mem_univ (a e)) (Finset.mem_univ (b e)) haeS (by rw [h])



  /- @proof-region region.target-node.session.6d75103721bb58ec end -/

end LiuBangXiangYu
