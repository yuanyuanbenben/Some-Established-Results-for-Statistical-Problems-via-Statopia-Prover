import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q12.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q12.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q12.ProvedNodes.Node_2101656357_757e486d_9c327da3
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q12.ProvedNodes.Node_612610791_f42c035b_22136fe3
open MeasureTheory ProbabilityTheory

open MeasureTheory ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_3593846891_8b5f0b2e : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : Fin n → Ω → ℝ)
    (hX_meas : ∀ i, Measurable (X i)) (hX_indep : iIndepFun X P)
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
    let μk : Measure ℝ := P.map (X k)
    (P[Y | F k.succ] =ᵐ[P] fun ω => Afun ω (X k ω)) ∧
    (P[Y | F k.castSucc] =ᵐ[P] fun ω => ∫ y : ℝ, Afun ω y ∂μk) := by
  /- @proof-region region.target-node.session.bab3c4e0c773615e begin -/
  intro Ω _ P _ n X hX_meas hX_indep B hB G hG_meas hG_bound k
  dsimp only
  haveI hPmap : ∀ i : Fin n, IsProbabilityMeasure (Measure.map (X i) P) :=
    fun i => Measure.isProbabilityMeasure_map (hX_meas i).aemeasurable
  haveI hfinZ : IsFiniteMeasure
      (Measure.pi (fun i : {i : Fin n // k.val < i.val} => Measure.map (X (i : Fin n)) P)) :=
    ⟨by simp⟩
  have hAfun_bound : ∀ (ω : Ω) (y : ℝ),
      |∫ w : {i : Fin n // k.val < i.val} → ℝ,
        G (fun i : Fin n =>
          if h : k.val < i.val then w ⟨i, h⟩ else if i = k then y else X i ω)
        ∂(Measure.pi (fun i : {i : Fin n // k.val < i.val} => Measure.map (X (i : Fin n)) P))| ≤ B := by
    intro ω y
    have hle : ‖∫ w : {i : Fin n // k.val < i.val} → ℝ,
        G (fun i : Fin n =>
          if h : k.val < i.val then w ⟨i, h⟩ else if i = k then y else X i ω)
        ∂(Measure.pi (fun i : {i : Fin n // k.val < i.val} => Measure.map (X (i : Fin n)) P))‖
        ≤ ∫ _w : {i : Fin n // k.val < i.val} → ℝ, B
          ∂(Measure.pi (fun i : {i : Fin n // k.val < i.val} => Measure.map (X (i : Fin n)) P)) :=
      norm_integral_le_of_norm_le
        (f := fun w : {i : Fin n // k.val < i.val} → ℝ =>
          G (fun i : Fin n =>
            if h : k.val < i.val then w ⟨i, h⟩ else if i = k then y else X i ω))
        (g := fun _ => B) (integrable_const B)
        (Filter.Eventually.of_forall fun w => by
          simpa [Real.norm_eq_abs] using hG_bound (fun i : Fin n =>
            if h : k.val < i.val then w ⟨i, h⟩ else if i = k then y else X i ω))
    have hconst : (∫ _w : {i : Fin n // k.val < i.val} → ℝ, B
          ∂(Measure.pi (fun i : {i : Fin n // k.val < i.val} => Measure.map (X (i : Fin n)) P))) = B := by
      simp [integral_const, measure_univ]
    rw [hconst] at hle
    simpa [Real.norm_eq_abs] using hle
  have hV_meas : Measurable (fun ω : Ω => fun i : Fin n => X i ω) :=
    measurable_pi_iff.2 hX_meas
  have hjoint : Measure.map (fun ω : Ω => fun i : Fin n => X i ω) P
      = Measure.pi (fun i : Fin n => Measure.map (X i) P) :=
    (iIndepFun_iff_map_fun_eq_pi_map (f := X) (fun i => (hX_meas i).aemeasurable)).mp hX_indep
  have hA1_meas : Measurable fun u : Fin n → ℝ =>
      ∫ w : {i : Fin n // k.val < i.val} → ℝ,
        G (fun i : Fin n =>
          if h : k.val < i.val then w ⟨i, h⟩ else if i = k then u k else u i)
        ∂(Measure.pi (fun i : {i : Fin n // k.val < i.val} => Measure.map (X (i : Fin n)) P)) := by
    have hfun : Measurable (Function.uncurry fun (u : Fin n → ℝ)
        (w : {i : Fin n // k.val < i.val} → ℝ) =>
        G (fun i : Fin n =>
          if h : k.val < i.val then w ⟨i, h⟩ else if i = k then u k else u i)) := by
      refine hG_meas.comp (measurable_pi_iff.mpr ?_)
      intro i
      by_cases hi : k.val < i.val
      · simp only [hi, dif_pos]
        exact (measurable_pi_apply (⟨i, hi⟩ : {i : Fin n // k.val < i.val})).comp measurable_snd
      · simp only [hi]
        by_cases hik : i = k
        · simp only [if_pos hik]
          exact (measurable_pi_apply k).comp measurable_fst
        · simp only [if_neg hik]
          exact (measurable_pi_apply i).comp measurable_fst
    exact (hfun.stronglyMeasurable.integral_prod_right).measurable
  have hA1_aesm : AEStronglyMeasurable (fun ω : Ω =>
      ∫ w : {i : Fin n // k.val < i.val} → ℝ,
        G (fun i : Fin n =>
          if h : k.val < i.val then w ⟨i, h⟩ else if i = k then X k ω else X i ω)
        ∂(Measure.pi (fun i : {i : Fin n // k.val < i.val} => Measure.map (X (i : Fin n)) P))) P :=
    (hA1_meas.comp hV_meas).aestronglyMeasurable
  have hA2_meas : Measurable fun u : Fin n → ℝ =>
      ∫ y : ℝ, (∫ w : {i : Fin n // k.val < i.val} → ℝ,
        G (fun i : Fin n =>
          if h : k.val < i.val then w ⟨i, h⟩ else if i = k then y else u i)
        ∂(Measure.pi (fun i : {i : Fin n // k.val < i.val} => Measure.map (X (i : Fin n)) P)))
      ∂(Measure.map (X k) P) := by
    have hfun : Measurable (Function.uncurry fun (p : (Fin n → ℝ) × ℝ)
        (w : {i : Fin n // k.val < i.val} → ℝ) =>
        G (fun i : Fin n =>
          if h : k.val < i.val then w ⟨i, h⟩ else if i = k then p.2 else p.1 i)) := by
      refine hG_meas.comp (measurable_pi_iff.mpr ?_)
      intro i
      by_cases hi : k.val < i.val
      · simp only [hi, dif_pos]
        exact (measurable_pi_apply (⟨i, hi⟩ : {i : Fin n // k.val < i.val})).comp measurable_snd
      · simp only [dif_neg hi]
        by_cases hik : i = k
        · simp only [if_pos hik]
          exact measurable_snd.comp measurable_fst
        · simp only [if_neg hik]
          exact (measurable_pi_apply i).comp (measurable_fst.comp measurable_fst)
    have hinner : StronglyMeasurable fun p : (Fin n → ℝ) × ℝ =>
        ∫ w : {i : Fin n // k.val < i.val} → ℝ,
          G (fun i : Fin n =>
            if h : k.val < i.val then w ⟨i, h⟩ else if i = k then p.2 else p.1 i)
          ∂(Measure.pi (fun i : {i : Fin n // k.val < i.val} => Measure.map (X (i : Fin n)) P)) :=
      hfun.stronglyMeasurable.integral_prod_right
    exact (StronglyMeasurable.integral_prod_right' (ν := Measure.map (X k) P) hinner).measurable
  have hA2_aesm : AEStronglyMeasurable (fun ω : Ω =>
      ∫ y : ℝ, (∫ w : {i : Fin n // k.val < i.val} → ℝ,
        G (fun i : Fin n =>
          if h : k.val < i.val then w ⟨i, h⟩ else if i = k then y else X i ω)
        ∂(Measure.pi (fun i : {i : Fin n // k.val < i.val} => Measure.map (X (i : Fin n)) P)))
      ∂(Measure.map (X k) P)) P :=
    (hA2_meas.comp hV_meas).aestronglyMeasurable
  have hA2_bound : ∀ ω : Ω,
      |∫ y : ℝ, (∫ w : {i : Fin n // k.val < i.val} → ℝ,
        G (fun i : Fin n =>
          if h : k.val < i.val then w ⟨i, h⟩ else if i = k then y else X i ω)
        ∂(Measure.pi (fun i : {i : Fin n // k.val < i.val} => Measure.map (X (i : Fin n)) P)))
      ∂(Measure.map (X k) P)| ≤ B := by
    intro ω
    have hle : ‖∫ y : ℝ, (∫ w : {i : Fin n // k.val < i.val} → ℝ,
        G (fun i : Fin n =>
          if h : k.val < i.val then w ⟨i, h⟩ else if i = k then y else X i ω)
        ∂(Measure.pi (fun i : {i : Fin n // k.val < i.val} => Measure.map (X (i : Fin n)) P)))
      ∂(Measure.map (X k) P)‖
        ≤ ∫ _y : ℝ, B ∂(Measure.map (X k) P) :=
      norm_integral_le_of_norm_le
        (f := fun y : ℝ => (∫ w : {i : Fin n // k.val < i.val} → ℝ,
          G (fun i : Fin n =>
            if h : k.val < i.val then w ⟨i, h⟩ else if i = k then y else X i ω)
          ∂(Measure.pi (fun i : {i : Fin n // k.val < i.val} => Measure.map (X (i : Fin n)) P))))
        (g := fun _ => B) (integrable_const B)
        (Filter.Eventually.of_forall fun y => by
          simpa [Real.norm_eq_abs] using hAfun_bound ω y)
    have hconst : (∫ _y : ℝ, B ∂(Measure.map (X k) P)) = B := by
      simp [integral_const, measure_univ]
    rw [hconst] at hle
    simpa [Real.norm_eq_abs] using hle
  haveI hfinP : IsFiniteMeasure P := ⟨by simp⟩
  have hY_int : Integrable (fun ω : Ω => G (fun i : Fin n => X i ω)) P :=
    Integrable.of_bound ((hG_meas.comp hV_meas).aestronglyMeasurable) B
      (Filter.Eventually.of_forall fun ω => by
        simpa [Real.norm_eq_abs] using hG_bound (fun i : Fin n => X i ω))
  have hA1_int : Integrable (fun ω : Ω =>
      ∫ w : {i : Fin n // k.val < i.val} → ℝ,
        G (fun i : Fin n =>
          if h : k.val < i.val then w ⟨i, h⟩ else if i = k then X k ω else X i ω)
        ∂(Measure.pi (fun i : {i : Fin n // k.val < i.val} => Measure.map (X (i : Fin n)) P))) P :=
    Integrable.of_bound hA1_aesm B
      (Filter.Eventually.of_forall fun ω => by
        simpa [Real.norm_eq_abs] using hAfun_bound ω (X k ω))
  have hA2_int : Integrable (fun ω : Ω =>
      ∫ y : ℝ, (∫ w : {i : Fin n // k.val < i.val} → ℝ,
        G (fun i : Fin n =>
          if h : k.val < i.val then w ⟨i, h⟩ else if i = k then y else X i ω)
        ∂(Measure.pi (fun i : {i : Fin n // k.val < i.val} => Measure.map (X (i : Fin n)) P)))
      ∂(Measure.map (X k) P)) P :=
    Integrable.of_bound hA2_aesm B
      (Filter.Eventually.of_forall fun ω => by
        simpa [Real.norm_eq_abs] using hA2_bound ω)
  have hprod1 : Measure.map (fun ω : Ω =>
      ((fun i : {i : Fin n // i.val < k.val + 1} => X (i : Fin n) ω),
       (fun i : {i : Fin n // ¬ i.val < k.val + 1} => X (i : Fin n) ω))) P
      = (Measure.pi (fun i : {i : Fin n // i.val < k.val + 1} => P.map (X (i : Fin n)))).prod
        (Measure.pi (fun i : {i : Fin n // ¬ i.val < k.val + 1} => P.map (X (i : Fin n)))) := by
    have hmp := measurePreserving_piEquivPiSubtypeProd
      (μ := fun i : Fin n => P.map (X i)) (p := fun i : Fin n => i.val < k.val + 1)
    have step1 : Measure.map (⇑(MeasurableEquiv.piEquivPiSubtypeProd (fun (_ : Fin n) => ℝ)
          (fun i : Fin n => i.val < k.val + 1)))
        (Measure.map (fun ω : Ω => fun i : Fin n => X i ω) P)
        = Measure.map (fun ω : Ω =>
            ((fun i : {i : Fin n // i.val < k.val + 1} => X (i : Fin n) ω),
             (fun i : {i : Fin n // ¬ i.val < k.val + 1} => X (i : Fin n) ω))) P :=
      Measure.map_map (MeasurableEquiv.measurable _) hV_meas
    rw [hjoint] at step1
    rw [← step1]
    exact hmp.map_eq
  have hprod2 : Measure.map (fun ω : Ω =>
      ((fun i : {i : Fin n // i.val < k.val} => X (i : Fin n) ω),
       (fun i : {i : Fin n // ¬ i.val < k.val} => X (i : Fin n) ω))) P
      = (Measure.pi (fun i : {i : Fin n // i.val < k.val} => P.map (X (i : Fin n)))).prod
        (Measure.pi (fun i : {i : Fin n // ¬ i.val < k.val} => P.map (X (i : Fin n)))) := by
    have hmp := measurePreserving_piEquivPiSubtypeProd
      (μ := fun i : Fin n => P.map (X i)) (p := fun i : Fin n => i.val < k.val)
    have step1 : Measure.map (⇑(MeasurableEquiv.piEquivPiSubtypeProd (fun (_ : Fin n) => ℝ)
          (fun i : Fin n => i.val < k.val)))
        (Measure.map (fun ω : Ω => fun i : Fin n => X i ω) P)
        = Measure.map (fun ω : Ω =>
            ((fun i : {i : Fin n // i.val < k.val} => X (i : Fin n) ω),
             (fun i : {i : Fin n // ¬ i.val < k.val} => X (i : Fin n) ω))) P :=
      Measure.map_map (MeasurableEquiv.measurable _) hV_meas
    rw [hjoint] at step1
    rw [← step1]
    exact hmp.map_eq
  have hcomap_le : ∀ (m : ℕ) (i : Fin n) (hi : i.val < m),
      MeasurableSpace.comap (X i) inferInstance ≤
        MeasurableSpace.comap (fun ω : Ω => fun j : {j : Fin n // j.val < m} => X j ω)
          inferInstance := by
    intro m i hi
    have heval : MeasurableSpace.comap (fun q : {j : Fin n // j.val < m} → ℝ => q ⟨i, hi⟩)
        (inferInstance : MeasurableSpace ℝ)
        ≤ (inferInstance : MeasurableSpace ({j : Fin n // j.val < m} → ℝ)) :=
      measurable_iff_comap_le.mp (measurable_pi_apply (⟨i, hi⟩ : {j : Fin n // j.val < m}))
    have h1 := MeasurableSpace.comap_mono
      (g := fun ω : Ω => fun j : {j : Fin n // j.val < m} => X j ω) heval
    rwa [MeasurableSpace.comap_comp] at h1
  have hF_le1 : (⨆ i : Fin n, ⨆ (_ : i.val < k.val + 1),
        MeasurableSpace.comap (X i) inferInstance)
      ≤ MeasurableSpace.comap (fun ω : Ω => fun j : {j : Fin n // j.val < k.val + 1} => X j ω)
        inferInstance :=
    iSup_le fun i => iSup_le fun hi => hcomap_le (k.val + 1) i hi
  have hF_le2 : (⨆ i : Fin n, ⨆ (_ : i.val < k.val),
        MeasurableSpace.comap (X i) inferInstance)
      ≤ MeasurableSpace.comap (fun ω : Ω => fun j : {j : Fin n // j.val < k.val} => X j ω)
        inferInstance :=
    iSup_le fun i => iSup_le fun hi => hcomap_le k.val i hi
  have hcomap_ge : ∀ (m : ℕ),
      MeasurableSpace.comap (fun ω : Ω => fun j : {j : Fin n // j.val < m} => X j ω)
        inferInstance
        ≤ (⨆ i : Fin n, ⨆ (_ : i.val < m), MeasurableSpace.comap (X i) inferInstance) := by
    intro m
    letI : MeasurableSpace Ω :=
      ⨆ i : Fin n, ⨆ (_ : i.val < m), MeasurableSpace.comap (X i) inferInstance
    refine measurable_iff_comap_le.mp ?_
    refine measurable_pi_iff.mpr fun i => ?_
    have a := le_iSup (fun i : Fin n => ⨆ (_ : i.val < m),
      MeasurableSpace.comap (X i) inferInstance) (i : Fin n)
    have b := le_iSup (fun _ : (i : Fin n).val < m =>
      MeasurableSpace.comap (X (i : Fin n)) inferInstance) i.2
    exact measurable_iff_comap_le.mpr (b.trans a)
  have hF_eq1 : (⨆ i : Fin n, ⨆ (_ : i.val < k.val + 1),
        MeasurableSpace.comap (X i) inferInstance)
      = MeasurableSpace.comap (fun ω : Ω => fun j : {j : Fin n // j.val < k.val + 1} => X j ω)
        inferInstance :=
    le_antisymm hF_le1 (hcomap_ge (k.val + 1))
  have hF_eq2 : (⨆ i : Fin n, ⨆ (_ : i.val < k.val),
        MeasurableSpace.comap (X i) inferInstance)
      = MeasurableSpace.comap (fun ω : Ω => fun j : {j : Fin n // j.val < k.val} => X j ω)
        inferInstance :=
    le_antisymm hF_le2 (hcomap_ge k.val)
  have hpre1 : ∀ A : Set Ω,
      MeasurableSet[⨆ i : Fin n, ⨆ (_ : i.val < k.val + 1),
        MeasurableSpace.comap (X i) inferInstance] A →
      ∃ S : Set ({j : Fin n // j.val < k.val + 1} → ℝ), MeasurableSet S ∧
        (fun ω : Ω => fun j : {j : Fin n // j.val < k.val + 1} => X j ω) ⁻¹' S = A := by
    intro A hA
    have hA' : MeasurableSet[MeasurableSpace.comap
        (fun ω : Ω => fun j : {j : Fin n // j.val < k.val + 1} => X j ω) inferInstance] A := by
      rw [← hF_eq1]
      exact hA
    exact MeasurableSpace.measurableSet_comap.mp hA'
  have hpre2 : ∀ A : Set Ω,
      MeasurableSet[⨆ i : Fin n, ⨆ (_ : i.val < k.val),
        MeasurableSpace.comap (X i) inferInstance] A →
      ∃ S : Set ({j : Fin n // j.val < k.val} → ℝ), MeasurableSet S ∧
        (fun ω : Ω => fun j : {j : Fin n // j.val < k.val} => X j ω) ⁻¹' S = A := by
    intro A hA
    have hA' : MeasurableSet[MeasurableSpace.comap
        (fun ω : Ω => fun j : {j : Fin n // j.val < k.val} => X j ω) inferInstance] A := by
      rw [← hF_eq2]
      exact hA
    exact MeasurableSpace.measurableSet_comap.mp hA'
  refine ⟨?_, ?_⟩
  · exact statopia_math_node_2101656357_757e486d P n X hX_meas hX_indep B hB G hG_meas hG_bound k
  · exact statopia_math_node_612610791_f42c035b P n X hX_meas hX_indep B hB G hG_meas hG_bound k
  /- @proof-region region.target-node.session.bab3c4e0c773615e end -/
