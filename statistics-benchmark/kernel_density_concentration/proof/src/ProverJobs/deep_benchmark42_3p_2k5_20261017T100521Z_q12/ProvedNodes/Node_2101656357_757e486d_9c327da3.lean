import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q12.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q12.Base

open MeasureTheory ProbabilityTheory

open MeasureTheory ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_2101656357_757e486d : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : Fin n → Ω → ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X P)
    (B : ℝ) (hB : 0 ≤ B)
    (G : (Fin n → ℝ) → ℝ) (hG_meas : Measurable G)
    (hG_bound : ∀ u : Fin n → ℝ, |G u| ≤ B)
    (k : Fin n),
    let F : Fin (n + 1) → MeasurableSpace Ω :=
      fun j => ⨆ i : Fin n, ⨆ (_ : i.val < j.val), MeasurableSpace.comap (X i) inferInstance
    let Y : Ω → ℝ := fun ω => G (fun i => X i ω)
    let Z : Type := {i : Fin n // k.val < i.val}
    let νZ : Measure (Z → ℝ) := Measure.pi (fun i : Z => P.map (X (i : Fin n)))
    let Afun : Ω → ℝ → ℝ := fun ω y =>
      ∫ w : Z → ℝ,
        G (fun i : Fin n =>
          if h : k.val < i.val then w ⟨i, h⟩ else if i = k then y else X i ω) ∂νZ
    MeasureTheory.condExp (F k.succ) P Y =ᵐ[P] fun ω => Afun ω (X k ω) := by
  /- @proof-region region.target-node.session.3bab4251b17665dd begin -/
  intro Ω _ P _ n X hX_meas hX_indep B hB G hG_meas hG_bound k
  dsimp only
  classical
  set Z : Type := {i : Fin n // k.val < i.val} with hZ
  set νZ : Measure (Z → ℝ) := Measure.pi (fun i : Z => P.map (X (i : Fin n))) with hνZ
  set Yf : Ω → ℝ := (fun ω => G (fun i => X i ω)) with hYf
  set gf : Ω → ℝ := (fun ω => ∫ w : Z → ℝ,
    G (fun i : Fin n => if h : k.val < i.val then w ⟨i, h⟩ else X i ω) ∂νZ) with hgf
  haveI hprob : ∀ i : Fin n, IsProbabilityMeasure (P.map (X i)) := fun i =>
    (MeasureTheory.Measure.isProbabilityMeasure_map_iff (hX_meas i).aemeasurable).mpr inferInstance
  haveI hνZfin : SigmaFinite νZ := by
    rw [hνZ]
    infer_instance
  have hassoc : (fun ω : Ω => ∫ w : Z → ℝ,
      G (fun i : Fin n =>
        if h : k.val < i.val then w ⟨i, h⟩ else if i = k then X k ω else X i ω) ∂νZ) = gf := by
    funext ω
    show (∫ w : Z → ℝ, G (fun i : Fin n =>
        if h : k.val < i.val then w ⟨i, h⟩ else if i = k then X k ω else X i ω) ∂νZ)
      = (∫ w : Z → ℝ, G (fun i : Fin n =>
        if h : k.val < i.val then w ⟨i, h⟩ else X i ω) ∂νZ)
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    have hfun : (fun i : Fin n =>
        if h : k.val < i.val then w ⟨i, h⟩ else if i = k then X k ω else X i ω)
        = (fun i : Fin n => if h : k.val < i.val then w ⟨i, h⟩ else X i ω) := by
      funext i
      by_cases hlt : k.val < i.val
      · rw [dif_pos hlt, dif_pos hlt]
      · rw [dif_neg hlt, dif_neg hlt]
        by_cases hik : i = k
        · subst hik; simp
        · simp [hik]
    exact congrArg G hfun
  have hAEM : @AEStronglyMeasurable Ω ℝ _
      (⨆ i : Fin n, ⨆ (_ : i.val < (k.succ).val), MeasurableSpace.comap (X i) inferInstance) _
      gf P := by
    letI : MeasurableSpace Ω :=
      ⨆ i : Fin n, ⨆ (_ : i.val < (k.succ).val), MeasurableSpace.comap (X i) inferInstance
    set W : Type := {j : Fin n // ¬ k.val < j.val} with hW
    set pfx : Ω → (W → ℝ) := fun ω j => X (j : Fin n) ω with hpfx
    have hjoint : Measurable (Function.uncurry (fun (s : W → ℝ) (w : Z → ℝ) =>
        G (fun i : Fin n => if h : k.val < i.val then w ⟨i, h⟩ else s ⟨i, h⟩))) := by
      refine hG_meas.comp (measurable_pi_iff.mpr fun i => ?_)
      by_cases hlt : k.val < i.val
      · simp only [dif_pos hlt]
        have hev : Measurable (fun w : Z → ℝ => w ⟨i, hlt⟩) :=
          (measurable_pi_iff (g := fun w : Z → ℝ => w)).mp measurable_id ⟨i, hlt⟩
        exact hev.comp measurable_snd
      · simp only [dif_neg hlt]
        have hev : Measurable (fun s : W → ℝ => s ⟨i, hlt⟩) :=
          (measurable_pi_iff (g := fun s : W → ℝ => s)).mp measurable_id ⟨i, hlt⟩
        exact hev.comp measurable_fst
    have hΨs : StronglyMeasurable fun s : W → ℝ => ∫ w : Z → ℝ,
        G (fun i : Fin n => if h : k.val < i.val then w ⟨i, h⟩ else s ⟨i, h⟩) ∂νZ :=
      MeasureTheory.StronglyMeasurable.integral_prod_right (ν := νZ)
        (f := fun (s : W → ℝ) (w : Z → ℝ) =>
          G (fun i : Fin n => if h : k.val < i.val then w ⟨i, h⟩ else s ⟨i, h⟩))
        hjoint.stronglyMeasurable
    have hgf_eq : gf = fun ω => ∫ w : Z → ℝ,
        G (fun i : Fin n => if h : k.val < i.val then w ⟨i, h⟩ else pfx ω ⟨i, h⟩) ∂νZ := by
      rw [hgf]
    have hpfxm : Measurable pfx := by
      refine measurable_pi_iff.mpr fun j => ?_
      exact measurable_iff_comap_le.mpr
        (le_iSup_of_le (j : Fin n) (le_iSup_of_le
          (Nat.lt_succ_of_le (Nat.le_of_not_lt j.property)) (le_refl _)))
    have hme : Measurable gf := by
      rw [hgf_eq]
      exact hΨs.measurable.comp hpfxm
    exact hme.aestronglyMeasurable
  have hIntY : Integrable Yf P := by
    refine MeasureTheory.Integrable.of_bound ?_ B (Filter.Eventually.of_forall fun ω => ?_)
    · rw [hYf]
      exact (hG_meas.comp (measurable_pi_iff.mpr fun i => hX_meas i)).aestronglyMeasurable
    · rw [hYf]
      simpa only [Real.norm_eq_abs] using hG_bound (fun i => X i ω)
  have hbnd : ∀ ω : Ω, ‖gf ω‖ ≤ B := by
    haveI hνZp : IsProbabilityMeasure νZ := by
      rw [hνZ]
      infer_instance
    intro ω
    have h2 : ‖∫ w : Z → ℝ,
        G (fun i : Fin n => if h : k.val < i.val then w ⟨i, h⟩ else X i ω) ∂νZ‖
        ≤ B * νZ.real Set.univ :=
      MeasureTheory.norm_integral_le_of_norm_le_const
        (Filter.Eventually.of_forall (fun w => by
          simpa only [Real.norm_eq_abs] using
            hG_bound (fun i : Fin n => if h : k.val < i.val then w ⟨i, h⟩ else X i ω)))
    have h3 : νZ.real Set.univ = 1 := by
      simpa using (MeasureTheory.measure_univ : νZ Set.univ = 1)
    have h4 : ‖∫ w : Z → ℝ,
        G (fun i : Fin n => if h : k.val < i.val then w ⟨i, h⟩ else X i ω) ∂νZ‖ ≤ B := by
      rw [h3, mul_one] at h2
      exact h2
    simpa only [hgf] using h4
  have hAEM0 : AEStronglyMeasurable gf P := by
    have hFm : Measurable (fun p : Ω × (Z → ℝ) =>
        G (fun i : Fin n => if h : k.val < i.val then p.2 ⟨i, h⟩ else X i p.1)) := by
      refine hG_meas.comp (measurable_pi_iff.mpr fun i => ?_)
      by_cases hlt : k.val < i.val
      · simp only [dif_pos hlt]
        have hev : Measurable (fun w : Z → ℝ => w ⟨i, hlt⟩) :=
          (measurable_pi_iff (g := fun w : Z → ℝ => w)).mp measurable_id ⟨i, hlt⟩
        exact hev.comp measurable_snd
      · simp only [dif_neg hlt]
        exact (hX_meas i).comp measurable_fst
    have hres := MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (μ := P) (ν := νZ)
      (f := fun p : Ω × (Z → ℝ) =>
        G (fun i : Fin n => if h : k.val < i.val then p.2 ⟨i, h⟩ else X i p.1))
      hFm.aestronglyMeasurable
    simpa only [hgf] using hres
  have hIntg : Integrable gf P :=
    MeasureTheory.Integrable.of_bound hAEM0 B (Filter.Eventually.of_forall hbnd)
  have hmFk : (⨆ i : Fin n, ⨆ (_ : i.val < (k.succ).val), MeasurableSpace.comap (X i) inferInstance)
      ≤ ‹MeasurableSpace Ω› := by
    exact iSup_le fun i => iSup_le fun _ => measurable_iff_comap_le.mp (hX_meas i)
  haveI htrimm : SigmaFinite (P.trim hmFk) := by
    haveI h0 : IsFiniteMeasure (P.trim hmFk) := MeasureTheory.isFiniteMeasure_trim hmFk
    infer_instance
  set νW : Measure ({j : Fin n // ¬ k.val < j.val} → ℝ) :=
    Measure.pi (fun j : {j : Fin n // ¬ k.val < j.val} => P.map (X (j : Fin n))) with hνW
  have hpair : Measure.map
      (fun ω => ((fun i : Z => X (i : Fin n) ω),
        (fun j : {j : Fin n // ¬ k.val < j.val} => X (j : Fin n) ω))) P = νZ.prod νW := by
    have hV : Measure.map (fun ω (i : Fin n) => X i ω) P
        = Measure.pi (fun i : Fin n => P.map (X i)) :=
      (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
        (f := X) (fun i => (hX_meas i).aemeasurable)).mp hX_indep
    have heq : Measure.map
        (⇑(MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ) (fun i : Fin n => k.val < i.val)))
        (Measure.pi (fun i : Fin n => P.map (X i))) = νZ.prod νW :=
      (MeasureTheory.measurePreserving_piEquivPiSubtypeProd
        (fun i : Fin n => P.map (X i)) (fun i : Fin n => k.val < i.val)).map_eq
    have hcomp : (fun ω => ((fun i : Z => X (i : Fin n) ω),
        (fun j : {j : Fin n // ¬ k.val < j.val} => X (j : Fin n) ω)))
        = (⇑(MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ)
            (fun i : Fin n => k.val < i.val)))
          ∘ (fun ω (i : Fin n) => X i ω) := rfl
    rw [hcomp, ← MeasureTheory.Measure.map_map, hV]
    exact heq
    exact (MeasurableEquiv.measurable _)
    exact measurable_pi_iff.mpr fun i => hX_meas i
  have hνWprob : IsProbabilityMeasure νW := by
    rw [hνW]
    infer_instance

  have key : gf =ᵐ[P] MeasureTheory.condExp
      (⨆ i : Fin n, ⨆ (_ : i.val < (k.succ).val), MeasurableSpace.comap (X i) inferInstance) P Yf := by
    refine MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq (μ := P)
      (m := ⨆ i : Fin n, ⨆ (_ : i.val < (k.succ).val), MeasurableSpace.comap (X i) inferInstance)
      (f := Yf) (g := gf) hmFk hIntY ?_ ?_ hAEM
    · intro s hs hfin
      exact hIntg.integrableOn
    · intro s hs hfin
      have hle : ∀ (i : Fin n), i.val < (k.succ).val →
          MeasurableSpace.comap (X i) inferInstance ≤ MeasurableSpace.comap
            (fun ω (j : {j : Fin n // ¬ k.val < j.val}) => X (j : Fin n) ω) inferInstance := by
        intro i hi
        refine (measurable_iff_comap_le (m₁ := MeasurableSpace.comap
          (fun ω (j : {j : Fin n // ¬ k.val < j.val}) => X (j : Fin n) ω) inferInstance)
          (f := X i)).mp ?_
        have hev : Measurable (fun q : {j : Fin n // ¬ k.val < j.val} → ℝ =>
            q ⟨i, Nat.not_lt.mpr (Nat.lt_succ_iff.mp hi)⟩) :=
          (measurable_pi_iff (g := fun q : {j : Fin n // ¬ k.val < j.val} → ℝ => q)).mp
            measurable_id ⟨i, Nat.not_lt.mpr (Nat.lt_succ_iff.mp hi)⟩
        have hpfx' : @Measurable Ω ({j : Fin n // ¬ k.val < j.val} → ℝ)
            (MeasurableSpace.comap (fun ω (j : {j : Fin n // ¬ k.val < j.val}) => X (j : Fin n) ω)
              inferInstance) inferInstance
            (fun ω (j : {j : Fin n // ¬ k.val < j.val}) => X (j : Fin n) ω) :=
          (measurable_iff_comap_le (m₁ := MeasurableSpace.comap
            (fun ω (j : {j : Fin n // ¬ k.val < j.val}) => X (j : Fin n) ω) inferInstance)
            (f := fun ω (j : {j : Fin n // ¬ k.val < j.val}) => X (j : Fin n) ω)).mpr (le_refl _)
        have hXi : (X i) = (fun q : {j : Fin n // ¬ k.val < j.val} → ℝ =>
            q ⟨i, Nat.not_lt.mpr (Nat.lt_succ_iff.mp hi)⟩) ∘
            (fun ω (j : {j : Fin n // ¬ k.val < j.val}) => X (j : Fin n) ω) := rfl
        rw [hXi]
        exact hev.comp hpfx'
      have hFk_le : (⨆ i : Fin n, ⨆ (_ : i.val < (k.succ).val),
          MeasurableSpace.comap (X i) inferInstance) ≤ MeasurableSpace.comap
            (fun ω (j : {j : Fin n // ¬ k.val < j.val}) => X (j : Fin n) ω) inferInstance :=
        iSup_le fun i => iSup_le fun hi => hle i hi
      have hs' : @MeasurableSet Ω (MeasurableSpace.comap
          (fun ω (j : {j : Fin n // ¬ k.val < j.val}) => X (j : Fin n) ω) inferInstance) s :=
        hFk_le s hs
      obtain ⟨S, hS, hSs⟩ := MeasurableSpace.measurableSet_comap.mp hs'
      rw [← hSs]
      have hset : (fun ω => ((fun i : Z => X (i : Fin n) ω),
          (fun j : {j : Fin n // ¬ k.val < j.val} => X (j : Fin n) ω))) ⁻¹' (Set.univ ×ˢ S)
          = (fun ω (j : {j : Fin n // ¬ k.val < j.val}) => X (j : Fin n) ω) ⁻¹' S := by
        ext x
        simp [Set.mem_prod]
      have hgffac : ∀ x : Ω, gf x =
          (fun p : (Z → ℝ) × ({j : Fin n // ¬ k.val < j.val} → ℝ) =>
            ∫ w : Z → ℝ, G (fun i : Fin n =>
              if h : k.val < i.val then w ⟨i, h⟩ else p.2 ⟨i, h⟩) ∂νZ)
          ((fun i : Z => X (i : Fin n) x),
            (fun j : {j : Fin n // ¬ k.val < j.val} => X (j : Fin n) x)) := by
        intro x
        rw [hgf]
      have hYffac : ∀ x : Ω, Yf x =
          (fun p : (Z → ℝ) × ({j : Fin n // ¬ k.val < j.val} → ℝ) =>
            G (fun i : Fin n =>
              if h : k.val < i.val then p.1 ⟨i, h⟩ else p.2 ⟨i, h⟩))
          ((fun i : Z => X (i : Fin n) x),
            (fun j : {j : Fin n // ¬ k.val < j.val} => X (j : Fin n) x)) := by
        intro x
        rw [hYf]
        simp only []
        refine congrArg G (funext fun i => ?_)
        by_cases hlt : k.val < i.val
        · simp only [dif_pos hlt, Subtype.coe_mk]
        · simp only [dif_neg hlt, Subtype.coe_mk]
      rw [← hset]
      have hind : ∀ {α : Type} [MeasurableSpace α] (μ : Measure α) (s : Set α) (F : α → ℝ),
          MeasurableSet s → ∫ x, s.indicator F x ∂μ = ∫ x in s, F x ∂μ := by
        intro α _ μ s F hs
        simpa using (MeasureTheory.setIntegral_indicator (s := Set.univ) (t := s) (f := F)
          (μ := μ) hs)
      have hpair_meas : Measurable (fun ω => ((fun i : Z => X (i : Fin n) ω),
          (fun j : {j : Fin n // ¬ k.val < j.val} => X (j : Fin n) ω))) :=
        (MeasurableEquiv.measurable (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ)
          (fun i : Fin n => k.val < i.val))).comp (measurable_pi_iff.mpr fun i => hX_meas i)
      have htransfer : ∀ (F : ((Z → ℝ) × ({j : Fin n // ¬ k.val < j.val} → ℝ)) → ℝ),
          AEStronglyMeasurable F (Measure.map (fun ω => ((fun i : Z => X (i : Fin n) ω),
            (fun j : {j : Fin n // ¬ k.val < j.val} => X (j : Fin n) ω))) P) →
          ∫ p, F p ∂(Measure.map (fun ω => ((fun i : Z => X (i : Fin n) ω),
            (fun j : {j : Fin n // ¬ k.val < j.val} => X (j : Fin n) ω))) P)
            = ∫ x, F ((fun i : Z => X (i : Fin n) x),
              (fun j : {j : Fin n // ¬ k.val < j.val} => X (j : Fin n) x)) ∂P := by
        intro F hF
        exact MeasureTheory.integral_map hpair_meas.aemeasurable hF
      set pr : Ω → (Z → ℝ) × ({j : Fin n // ¬ k.val < j.val} → ℝ) :=
        fun ω => ((fun i : Z => X (i : Fin n) ω),
          (fun j : {j : Fin n // ¬ k.val < j.val} => X (j : Fin n) ω)) with hprdef
      let Fgf : (Z → ℝ) × ({j : Fin n // ¬ k.val < j.val} → ℝ) → ℝ := fun p =>
        ∫ z : Z → ℝ, G (fun i : Fin n =>
          if h : k.val < i.val then z ⟨i, h⟩ else p.2 ⟨i, h⟩) ∂νZ
      let FYf : (Z → ℝ) × ({j : Fin n // ¬ k.val < j.val} → ℝ) → ℝ := fun p =>
        G (fun i : Fin n => if h : k.val < i.val then p.1 ⟨i, h⟩ else p.2 ⟨i, h⟩)
      have hpr : Measurable pr := by
        rw [hprdef]
        exact hpair_meas
      have hC : MeasurableSet ((Set.univ : Set (Z → ℝ)) ×ˢ S) :=
        MeasurableSet.prod MeasurableSet.univ hS
      have hfacg : ∀ x : Ω, gf x = Fgf (pr x) := fun x => hgffac x
      have hfacY : ∀ x : Ω, Yf x = FYf (pr x) := fun x => hYffac x
      have ind_g : (pr ⁻¹' (Set.univ ×ˢ S)).indicator gf
          = fun x => (Set.univ ×ˢ S).indicator Fgf (pr x) := by
        funext x
        by_cases hx : pr x ∈ Set.univ ×ˢ S <;> simp [Set.indicator, hx, hfacg x]
      have ind_Y : (pr ⁻¹' (Set.univ ×ˢ S)).indicator Yf
          = fun x => (Set.univ ×ˢ S).indicator FYf (pr x) := by
        funext x
        by_cases hx : pr x ∈ Set.univ ×ˢ S <;> simp [Set.indicator, hx, hfacY x]
      have hCpr : MeasurableSet (pr ⁻¹' ((Set.univ : Set (Z → ℝ)) ×ˢ S)) := hpr hC
      have hFYfm : Measurable FYf := by
        refine hG_meas.comp (measurable_pi_iff.mpr fun i => ?_)
        by_cases hlt : k.val < i.val
        · simp only [dif_pos hlt]
          exact ((measurable_pi_iff (g := fun z : Z → ℝ => z)).mp measurable_id ⟨i, hlt⟩).comp
            measurable_fst
        · simp only [dif_neg hlt]
          exact ((measurable_pi_iff
            (g := fun s : {j : Fin n // ¬ k.val < j.val} → ℝ => s)).mp measurable_id
            ⟨i, hlt⟩).comp measurable_snd
      have hFgfm : Measurable Fgf := by
        have huncurry : Measurable (Function.uncurry
            (fun (s : {j : Fin n // ¬ k.val < j.val} → ℝ) (z : Z → ℝ) =>
              G (fun i : Fin n => if h : k.val < i.val then z ⟨i, h⟩ else s ⟨i, h⟩))) := by
          refine hG_meas.comp (measurable_pi_iff.mpr fun i => ?_)
          by_cases hlt : k.val < i.val
          · simp only [dif_pos hlt]
            exact ((measurable_pi_iff (g := fun z : Z → ℝ => z)).mp measurable_id ⟨i, hlt⟩).comp
              measurable_snd
          · simp only [dif_neg hlt]
            exact ((measurable_pi_iff
              (g := fun s : {j : Fin n // ¬ k.val < j.val} → ℝ => s)).mp measurable_id
              ⟨i, hlt⟩).comp measurable_fst
        have hΨm : Measurable (fun s : {j : Fin n // ¬ k.val < j.val} → ℝ =>
            ∫ w : Z → ℝ, G (fun i : Fin n =>
              if h : k.val < i.val then w ⟨i, h⟩ else s ⟨i, h⟩) ∂νZ) :=
          (MeasureTheory.StronglyMeasurable.integral_prod_right (ν := νZ)
            (f := fun (s : {j : Fin n // ¬ k.val < j.val} → ℝ) (w : Z → ℝ) =>
              G (fun i : Fin n => if h : k.val < i.val then w ⟨i, h⟩ else s ⟨i, h⟩))
            huncurry.stronglyMeasurable).measurable
        exact hΨm.comp measurable_snd
      have hmapr : Measure.map pr (P.restrict (pr ⁻¹' ((Set.univ : Set (Z → ℝ)) ×ˢ S)))
          = (νZ.prod νW).restrict ((Set.univ : Set (Z → ℝ)) ×ˢ S) := by
        rw [← MeasureTheory.Measure.restrict_map hpr hC, hprdef, hpair]
      have hAEg : AEStronglyMeasurable Fgf
          (Measure.map pr (P.restrict (pr ⁻¹' ((Set.univ : Set (Z → ℝ)) ×ˢ S)))) := by
        rw [hmapr]
        exact hFgfm.aestronglyMeasurable.mono_measure Measure.restrict_le_self
      have hAEY : AEStronglyMeasurable FYf
          (Measure.map pr (P.restrict (pr ⁻¹' ((Set.univ : Set (Z → ℝ)) ×ˢ S)))) := by
        rw [hmapr]
        exact hFYfm.aestronglyMeasurable.mono_measure Measure.restrict_le_self
      have hgf_tr : ∫ x in pr ⁻¹' ((Set.univ : Set (Z → ℝ)) ×ˢ S), gf x ∂P
          = ∫ p in (Set.univ : Set (Z → ℝ)) ×ˢ S, Fgf p ∂(νZ.prod νW) := by
        have h1 : ∫ x in pr ⁻¹' ((Set.univ : Set (Z → ℝ)) ×ˢ S), gf x ∂P
            = ∫ x in pr ⁻¹' ((Set.univ : Set (Z → ℝ)) ×ˢ S), Fgf (pr x) ∂P :=
          MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => hfacg x)
        rw [h1, ← MeasureTheory.integral_map hpr.aemeasurable hAEg
          (f := Fgf), hmapr]
      have hYf_tr : ∫ x in pr ⁻¹' ((Set.univ : Set (Z → ℝ)) ×ˢ S), Yf x ∂P
          = ∫ p in (Set.univ : Set (Z → ℝ)) ×ˢ S, FYf p ∂(νZ.prod νW) := by
        have h1 : ∫ x in pr ⁻¹' ((Set.univ : Set (Z → ℝ)) ×ˢ S), Yf x ∂P
            = ∫ x in pr ⁻¹' ((Set.univ : Set (Z → ℝ)) ×ˢ S), FYf (pr x) ∂P :=
          MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => hfacY x)
        rw [h1, ← MeasureTheory.integral_map hpr.aemeasurable hAEY
          (f := FYf), hmapr]
      rw [hgf_tr, hYf_tr]
      haveI hνZp : IsProbabilityMeasure νZ := by
        rw [hνZ]
        infer_instance
      have hνZreal : νZ.real Set.univ = 1 := by
        simpa using (MeasureTheory.measure_univ : νZ Set.univ = 1)
      have hbF : ∀ p : (Z → ℝ) × ({j : Fin n // ¬ k.val < j.val} → ℝ), ‖Fgf p‖ ≤ B := by
        intro p
        have h2 : ‖∫ z : Z → ℝ, G (fun i : Fin n =>
            if h : k.val < i.val then z ⟨i, h⟩ else p.2 ⟨i, h⟩) ∂νZ‖
            ≤ B * νZ.real Set.univ :=
          MeasureTheory.norm_integral_le_of_norm_le_const (C := B)
            (Filter.Eventually.of_forall (fun z => by
              simpa only [Real.norm_eq_abs] using
                hG_bound (fun i : Fin n =>
                  if h : k.val < i.val then z ⟨i, h⟩ else p.2 ⟨i, h⟩)))
        rw [hνZreal, mul_one] at h2
        exact h2
      have hbY : ∀ p : (Z → ℝ) × ({j : Fin n // ¬ k.val < j.val} → ℝ), ‖FYf p‖ ≤ B := by
        intro p
        simpa only [Real.norm_eq_abs] using
          hG_bound (fun i : Fin n =>
            if h : k.val < i.val then p.1 ⟨i, h⟩ else p.2 ⟨i, h⟩)
      have hAEg' : AEStronglyMeasurable Fgf
          ((νZ.prod νW).restrict ((Set.univ : Set (Z → ℝ)) ×ˢ S)) :=
        hFgfm.aestronglyMeasurable.mono_measure Measure.restrict_le_self
      have hAEY' : AEStronglyMeasurable FYf
          ((νZ.prod νW).restrict ((Set.univ : Set (Z → ℝ)) ×ˢ S)) :=
        hFYfm.aestronglyMeasurable.mono_measure Measure.restrict_le_self
      have hIntOn_g : IntegrableOn Fgf ((Set.univ : Set (Z → ℝ)) ×ˢ S) (νZ.prod νW) :=
        MeasureTheory.Integrable.of_bound hAEg' B (Filter.Eventually.of_forall hbF)
      have hIntOn_Y : IntegrableOn FYf ((Set.univ : Set (Z → ℝ)) ×ˢ S) (νZ.prod νW) :=
        MeasureTheory.Integrable.of_bound hAEY' B (Filter.Eventually.of_forall hbY)
      have hgf_prod : ∫ p in (Set.univ : Set (Z → ℝ)) ×ˢ S, Fgf p ∂(νZ.prod νW)
          = ∫ w in S, (∫ z : Z → ℝ, FYf (z, w) ∂νZ) ∂νW := by
        rw [MeasureTheory.setIntegral_prod Fgf hIntOn_g]
        have hinner : ∀ z : Z → ℝ, (∫ w in S, Fgf (z, w) ∂νW)
            = ∫ w in S, (∫ z' : Z → ℝ, FYf (z', w) ∂νZ) ∂νW := by
          intro z
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
          rfl
        simp only [hinner]
        rw [Measure.restrict_univ, MeasureTheory.integral_const, hνZreal, one_smul]
      have hYf_prod : ∫ p in (Set.univ : Set (Z → ℝ)) ×ˢ S, FYf p ∂(νZ.prod νW)
          = ∫ w in S, (∫ z : Z → ℝ, FYf (z, w) ∂νZ) ∂νW := by
        rw [MeasureTheory.setIntegral_prod FYf hIntOn_Y, Measure.restrict_univ]
        rw [MeasureTheory.integral_integral_swap
          (f := fun (z : Z → ℝ) (w : {j : Fin n // ¬ k.val < j.val} → ℝ) => FYf (z, w)) ?_]
        exact MeasureTheory.Integrable.of_bound hFYfm.aestronglyMeasurable B
          (Filter.Eventually.of_forall hbY)
      rw [hgf_prod, hYf_prod]
  exact key.symm.trans (Filter.EventuallyEq.of_eq hassoc.symm)
  /- @proof-region region.target-node.session.3bab4251b17665dd end -/
