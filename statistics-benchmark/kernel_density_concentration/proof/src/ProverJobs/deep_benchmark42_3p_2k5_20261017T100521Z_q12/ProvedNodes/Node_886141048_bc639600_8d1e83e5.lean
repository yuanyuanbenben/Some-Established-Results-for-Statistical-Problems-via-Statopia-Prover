import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q12.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q12.Base

open MeasureTheory ProbabilityTheory

open MeasureTheory ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_886141048_bc639600 : ∀ (n : ℕ) (k : Fin n) (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (B0 : ℝ) (F : (Fin n → ℝ) → ℝ) (hF : Measurable F)
    (hF_bound : ∀ x : Fin n → ℝ, |F x| ≤ B0),
    ∫ x, F x ∂(Measure.pi μ)
      = ∫ (p : ({j : Fin n // j.val < k.val}) → ℝ),
          ∫ (y : ℝ),
            ∫ (w : ({i : Fin n // k.val < i.val}) → ℝ),
              F (fun i : Fin n =>
                  if hlt : k.val < i.val then w ⟨i, hlt⟩
                  else if hkeq : i = k then y
                  else p ⟨i, lt_of_le_of_ne (not_lt.mp hlt)
                        (fun hik => hkeq (Fin.ext hik))⟩)
              ∂(Measure.pi (fun i : {i : Fin n // k.val < i.val} => μ ↑i))
            ∂(μ k)
          ∂(Measure.pi (fun j : {j : Fin n // j.val < k.val} => μ ↑j)) := by
  /- @proof-region region.target-node.session.aa83d877e66d4faa begin -/
  intro n k μ hμ B0 F hF hF_bound
  classical
  let Pr := {j : Fin n // j.val < k.val}
  let Blk := {i : Fin n // ¬ i.val < k.val}
  let Q := {i : Blk // (↑i : Fin n) = k}
  let R := {i : Blk // ¬ (↑i : Fin n) = k}
  let Z := {i : Fin n // k.val < i.val}
  let νPr : Measure (Pr → ℝ) := Measure.pi fun j : Pr => μ j.val
  let νBlk : Measure (Blk → ℝ) := Measure.pi fun i : Blk => μ i.val
  let νQ : Measure (Q → ℝ) := Measure.pi fun q : Q => μ q.val.val
  let νR : Measure (R → ℝ) := Measure.pi fun r : R => μ r.val.val
  let νZ : Measure (Z → ℝ) := Measure.pi fun i : Z => μ i.val
  let νk : Measure ℝ := μ k
  have hbdd : ∀ x : Fin n → ℝ, ‖F x‖ ≤ B0 := fun x => by
    simpa [Real.norm_eq_abs] using hF_bound x
  let e1 : (Fin n → ℝ) ≃ᵐ (Pr → ℝ) × (Blk → ℝ) :=
    MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ) (fun i : Fin n => i.val < k.val)
  have hf1 : MeasurePreserving (⇑e1) (Measure.pi μ) (νPr.prod νBlk) :=
    measurePreserving_piEquivPiSubtypeProd (fun i : Fin n => μ i) (fun i : Fin n => i.val < k.val)
  let e2a : (Blk → ℝ) ≃ᵐ (Q → ℝ) × (R → ℝ) :=
    MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Blk => ℝ) (fun i : Blk => (↑i : Fin n) = k)
  have hf2a : MeasurePreserving (⇑e2a) νBlk (νQ.prod νR) :=
    measurePreserving_piEquivPiSubtypeProd (fun i : Blk => μ i.val) (fun i : Blk => (↑i : Fin n) = k)
  haveI hQuniq : Unique Q :=
    ⟨⟨⟨k, not_lt.mpr le_rfl⟩, rfl⟩,
      fun a => Subtype.ext (Subtype.ext (Fin.ext (congrArg Fin.val a.property)))⟩
  let q0 : Q := ⟨⟨k, not_lt.mpr le_rfl⟩, rfl⟩
  have hfQ' : MeasurePreserving (⇑(MeasurableEquiv.piUnique (fun _ : Q => ℝ))) νQ
      ((fun q : Q => μ q.val.val) default) :=
    measurePreserving_piUnique (fun q : Q => μ q.val.val)
  have hfQ : MeasurePreserving (⇑(MeasurableEquiv.piUnique (fun _ : Q => ℝ))) νQ νk := by
    have hq : default = q0 := (hQuniq.uniq q0).symm
    have hνk : (fun q : Q => μ q.val.val) default = μ k := by simp only [hq, q0]
    rw [hνk] at hfQ'
    exact hfQ'
  let f : R ≃ Z :=
    { toFun := fun r =>
        ⟨r.val.val, lt_of_le_of_ne (not_lt.mp r.val.property) (fun h => r.property (Fin.ext h.symm))⟩
      invFun := fun z => ⟨⟨z.val, not_lt.mpr (le_of_lt z.property)⟩, fun h => by
        have h1 : z.val = k := h
        have h2 : k.val < k.val := by
          have hz := z.property
          rwa [h1] at hz
        exact absurd h2 (lt_irrefl k.val)⟩
      left_inv := fun r => Subtype.ext (Subtype.ext rfl)
      right_inv := fun z => Subtype.ext rfl }
  have hfR : MeasurePreserving (⇑(MeasurableEquiv.piCongrLeft (fun _ : Z => ℝ) f)) νR νZ :=
    measurePreserving_piCongrLeft (fun z : Z => μ z.val) f
  let e2b : (Q → ℝ) × (R → ℝ) ≃ᵐ ℝ × (Z → ℝ) :=
    (MeasurableEquiv.piUnique (fun _ : Q => ℝ)).prodCongr
      (MeasurableEquiv.piCongrLeft (fun _ : Z => ℝ) f)
  have hf2b : MeasurePreserving (⇑e2b) (νQ.prod νR) (νk.prod νZ) := by
    have h := hfQ.prod hfR
    simpa only [e2b] using h
  let e2 : (Blk → ℝ) ≃ᵐ (ℝ × (Z → ℝ)) := e2a.trans e2b
  have hf2 : MeasurePreserving (⇑e2) νBlk (νk.prod νZ) := hf2b.comp hf2a
  let E : (Fin n → ℝ) ≃ᵐ (Pr → ℝ) × (ℝ × (Z → ℝ)) :=
    e1.trans (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (Pr → ℝ)) e2)
  have hE : MeasurePreserving (⇑E) (Measure.pi μ) (νPr.prod (νk.prod νZ)) :=
    ((MeasurePreserving.id νPr).prod hf2).comp hf1
  have hmain : ∫ x, F x ∂(Measure.pi μ)
      = ∫ a : (Pr → ℝ) × (ℝ × (Z → ℝ)), F (E.symm a) ∂(νPr.prod (νk.prod νZ)) := by
    have h := MeasureTheory.MeasurePreserving.integral_comp' (f := E) hE (fun a => F (E.symm a))
    simpa using h
  have haesm : AEStronglyMeasurable (fun a : (Pr → ℝ) × (ℝ × (Z → ℝ)) => F (E.symm a))
      (νPr.prod (νk.prod νZ)) :=
    (hF.comp E.symm.measurable).aestronglyMeasurable
  have hint : Integrable (fun a : (Pr → ℝ) × (ℝ × (Z → ℝ)) => F (E.symm a))
      (νPr.prod (νk.prod νZ)) :=
    Integrable.of_bound haesm B0 (Filter.Eventually.of_forall (fun a => hbdd (E.symm a)))
  have hstep1 : ∫ a : (Pr → ℝ) × (ℝ × (Z → ℝ)), F (E.symm a) ∂(νPr.prod (νk.prod νZ))
      = ∫ p : Pr → ℝ, ∫ yw : ℝ × (Z → ℝ), F (E.symm (p, yw)) ∂(νk.prod νZ) ∂νPr := by
    simpa only using integral_prod (fun a : (Pr → ℝ) × (ℝ × (Z → ℝ)) => F (E.symm a)) hint
  have hstep2 : ∀ p : Pr → ℝ, ∫ yw : ℝ × (Z → ℝ), F (E.symm (p, yw)) ∂(νk.prod νZ)
      = ∫ y : ℝ, ∫ w : Z → ℝ, F (E.symm (p, (y, w))) ∂νZ ∂νk := by
    intro p
    have hp : Measurable fun yw : ℝ × (Z → ℝ) => (p, yw) := by measurability
    have hm : Measurable fun yw : ℝ × (Z → ℝ) => F (E.symm (p, yw)) :=
      (hF.comp E.symm.measurable).comp hp
    have hi : Integrable (fun yw : ℝ × (Z → ℝ) => F (E.symm (p, yw))) (νk.prod νZ) :=
      Integrable.of_bound hm.aestronglyMeasurable B0
        (Filter.Eventually.of_forall (fun yw => hbdd (E.symm (p, yw))))
    simpa only using integral_prod (fun yw : ℝ × (Z → ℝ) => F (E.symm (p, yw))) hi
  have step_e1 : ∀ x : Fin n → ℝ,
      e1 x = ((fun j : Pr => x (↑j : Fin n)), fun i : Blk => x (↑i : Fin n)) := by
    intro x
    rfl
  have step_e2a : ∀ x : Blk → ℝ,
      e2a x = ((fun q : Q => x (↑q)), fun r : R => x (↑r)) := by
    intro x
    rfl
  have step_unique : ∀ x : Q → ℝ,
      (MeasurableEquiv.piUnique (fun _ : Q => ℝ)) x = x default := by
    intro x
    rfl
  have step_congrLeft : ∀ x : R → ℝ,
      (MeasurableEquiv.piCongrLeft (fun _ : Z => ℝ) f) x = fun a : Z => x (f.symm a) := by
    intro x
    funext a
    have h := MeasurableEquiv.piCongrLeft_apply_apply f (β := fun _ : Z => ℝ) x (f.symm a)
    rwa [Equiv.apply_symm_apply] at h
  have step_refl : ∀ (a : Pr → ℝ) (b : Blk → ℝ),
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (Pr → ℝ)) e2) (a, b) = (a, e2 b) := by
    intro a b
    rfl
  have step_prod2 : ∀ (q : Q → ℝ) (r : R → ℝ),
      e2b (q, r) = ((MeasurableEquiv.piUnique (fun _ : Q => ℝ)) q,
        (MeasurableEquiv.piCongrLeft (fun _ : Z => ℝ) f) r) := by
    intro q r
    rfl
  have hsymm : ∀ (p : Pr → ℝ) (y : ℝ) (w : Z → ℝ),
      E.symm (p, (y, w)) = fun i : Fin n =>
        if hlt : k.val < i.val then w ⟨i, hlt⟩
        else if hkeq : i = k then y
        else p ⟨i, lt_of_le_of_ne (not_lt.mp hlt) (fun hik => hkeq (Fin.ext hik))⟩ := by
    intro p y w
    set rec : Fin n → ℝ := fun i =>
      if hlt : k.val < i.val then w ⟨i, hlt⟩
      else if hkeq : i = k then y
      else p ⟨i, lt_of_le_of_ne (not_lt.mp hlt) (fun hik => hkeq (Fin.ext hik))⟩ with hrec
    have hPr : (fun j : Pr => rec (↑j : Fin n)) = p := by
      funext j
      have h1 : ¬ (k.val < (↑j : Fin n).val) := not_lt.mpr (le_of_lt j.property)
      have h2 : ¬ ((↑j : Fin n) = k) := by
        intro h
        have hz := j.property
        have h3 : (↑j : Fin n).val = k.val := by rw [h]
        rw [h3] at hz
        exact absurd hz (lt_irrefl k.val)
      rw [hrec]
      dsimp only
      rw [dif_neg h1, dif_neg h2]
    have hQ : ∀ q : Q, rec (↑(↑q) : Fin n) = y := by
      intro q
      have hq : (↑(↑q) : Fin n) = k := q.property
      have h1 : ¬ (k.val < (↑(↑q) : Fin n).val) := by
        rw [hq]
        exact not_lt.mpr le_rfl
      rw [hrec]
      dsimp only
      rw [dif_neg h1, dif_pos hq]
    have hR : ∀ a : Z, rec (↑(↑(f.symm a)) : Fin n) = w a := by
      intro a
      have hfa : (↑(↑(f.symm a)) : Fin n) = (↑a : Fin n) := rfl
      have h1 : k.val < (↑(↑(f.symm a)) : Fin n).val := by
        rw [hfa]
        exact a.property
      rw [hrec]
      dsimp only
      rw [dif_pos h1]
      rfl
    have he2 : e2 (fun i : Blk => rec (↑i : Fin n)) = (y, w) := by
      have ht : e2 = e2a.trans e2b := rfl
      rw [ht, MeasurableEquiv.coe_trans, Function.comp_apply, step_e2a, step_prod2, step_unique,
        step_congrLeft]
      refine Prod.ext ?_ ?_
      · exact hQ default
      · funext a
        exact hR a
    have hkey : E rec = (p, (y, w)) := by
      have hcomp : ⇑E = ⇑(MeasurableEquiv.prodCongr (MeasurableEquiv.refl (Pr → ℝ)) e2) ∘ ⇑e1 :=
        MeasurableEquiv.coe_trans _ _
      rw [hcomp, Function.comp_apply, step_e1, step_refl]
      exact Prod.ext hPr he2
    rw [← hkey, MeasurableEquiv.symm_apply_apply]
  rw [hmain, hstep1]
  simp only [hstep2]
  simp only [hsymm]
  rfl
  /- @proof-region region.target-node.session.aa83d877e66d4faa end -/
