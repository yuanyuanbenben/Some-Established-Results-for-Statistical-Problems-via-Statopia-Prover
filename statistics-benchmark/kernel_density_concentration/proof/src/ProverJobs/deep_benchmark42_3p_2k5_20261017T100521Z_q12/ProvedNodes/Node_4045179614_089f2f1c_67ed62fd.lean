import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q12.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q12.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q12.ProvedNodes.Node_3593846891_8b5f0b2e_64ab2bf3
open MeasureTheory ProbabilityTheory

open MeasureTheory ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_4045179614_089f2f1c : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : Fin n → Ω → ℝ)
    (hX_meas : ∀ i, Measurable (X i)) (hX_indep : iIndepFun X P)
    (c B : ℝ) (hc : 0 ≤ c) (hB : 0 ≤ B)
    (G : (Fin n → ℝ) → ℝ) (hG_meas : Measurable G)
    (hG_bound : ∀ u : Fin n → ℝ, |G u| ≤ B)
    (hG_stab : ∀ (k : Fin n) (u : Fin n → ℝ) (t : ℝ),
      |G u - G (Function.update u k t)| ≤ c)
    (k : Fin n),
    let F : Fin (n + 1) → MeasurableSpace Ω :=
      fun j => ⨆ i : Fin n, ⨆ (_ : i.val < j.val),
        MeasurableSpace.comap (X i) inferInstance
    let Y : Ω → ℝ := fun ω => G (fun i => X i ω)
    let Z : Type := {i : Fin n // k.val < i.val}
    let νZ : Measure (Z → ℝ) := Measure.pi (fun i : Z => P.map (X (i : Fin n)))
    let Afun : Ω → ℝ → ℝ := fun ω y =>
      ∫ w : Z → ℝ,
        G (fun i : Fin n =>
          if h : k.val < i.val then w ⟨i, h⟩ else if i = k then y else X i ω) ∂νZ
    let μk : Measure ℝ := P.map (X k)
    (P[Y | F k.succ] =ᵐ[P] fun ω => Afun ω (X k ω)) ∧
    (P[Y | F k.castSucc] =ᵐ[P] fun ω => ∫ y : ℝ, Afun ω y ∂μk) ∧
    (∀ (ω : Ω) (y : ℝ), |Afun ω y| ≤ B) ∧
    (∀ (ω : Ω) (y y' : ℝ), |Afun ω y - Afun ω y'| ≤ c) ∧
    (∀ ω : Ω, Integrable (fun y : ℝ => Afun ω y) μk) := by
  /- @proof-region region.target-node.session.c23fcba9be17739b begin -/
  intro Ω _ P _ n X hX_meas hX_indep c B hc hB G hG_meas hG_bound hG_stab k
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (statopia_math_node_3593846891_8b5f0b2e P n X hX_meas hX_indep B hB G hG_meas hG_bound k).1
  · exact (statopia_math_node_3593846891_8b5f0b2e P n X hX_meas hX_indep B hB G hG_meas hG_bound k).2
  · intro ω y
    haveI hZ : ∀ i : {i : Fin n // k.val < i.val}, IsProbabilityMeasure (Measure.map (X (i : Fin n)) P) :=
      fun i => MeasureTheory.Measure.isProbabilityMeasure_map (hX_meas (i : Fin n)).aemeasurable
    have hb : ∀ w : {i : Fin n // k.val < i.val} → ℝ,
        ‖G (fun i : Fin n => if h : k.val < i.val then w ⟨i, h⟩ else if i = k then y else X i ω)‖ ≤ B :=
      fun w => by
        rw [Real.norm_eq_abs]
        exact hG_bound _
    have hmain := MeasureTheory.norm_integral_le_of_norm_le_const
      (μ := Measure.pi fun i : {i : Fin n // k.val < i.val} => Measure.map (X (i : Fin n)) P)
      (f := fun w : {i : Fin n // k.val < i.val} → ℝ =>
        G (fun i : Fin n => if h : k.val < i.val then w ⟨i, h⟩ else if i = k then y else X i ω))
      (C := B)
      (by filter_upwards with w using hb w)
    have hreal :
        (Measure.pi fun i : {i : Fin n // k.val < i.val} => Measure.map (X (i : Fin n)) P).real Set.univ = 1 := by
      simp
    simpa [Real.norm_eq_abs, hreal] using hmain
  · intro ω y y'
    haveI hZ : ∀ i : {i : Fin n // k.val < i.val}, IsProbabilityMeasure (Measure.map (X (i : Fin n)) P) :=
      fun i => MeasureTheory.Measure.isProbabilityMeasure_map (hX_meas (i : Fin n)).aemeasurable
    have hreal :
        (Measure.pi fun i : {i : Fin n // k.val < i.val} => Measure.map (X (i : Fin n)) P).real Set.univ
          = 1 := by simp
    have hGmeas : ∀ r : ℝ, Measurable (fun w : {i : Fin n // k.val < i.val} → ℝ =>
        G (fun i : Fin n => if h : k.val < i.val then w ⟨i, h⟩ else if i = k then r else X i ω)) := by
      intro r
      refine hG_meas.comp ?_
      rw [measurable_pi_iff]
      intro i
      by_cases hlt : k.val < i.val
      · simp only [dif_pos hlt]
        measurability
      · simp only [dif_neg hlt]
        by_cases hik : i = k
        · simp only [if_pos hik]
          measurability
        · simp only [if_neg hik]
          measurability
    have hGint : ∀ r : ℝ, Integrable (fun w : {i : Fin n // k.val < i.val} → ℝ =>
        G (fun i : Fin n => if h : k.val < i.val then w ⟨i, h⟩ else if i = k then r else X i ω))
        (Measure.pi fun i : {i : Fin n // k.val < i.val} => Measure.map (X (i : Fin n)) P) := by
      intro r
      refine (MeasureTheory.integrable_const (μ := Measure.pi fun i : {i : Fin n // k.val < i.val} =>
        Measure.map (X (i : Fin n)) P) B).mono' (hGmeas r).aestronglyMeasurable ?_
      filter_upwards with w
      simpa [Real.norm_eq_abs] using hG_bound _
    have hfar : ∀ r r' : ℝ,
        |∫ w, (G (fun i : Fin n => if h : k.val < i.val then w ⟨i, h⟩ else if i = k then r else X i ω)
          - G (fun i : Fin n => if h : k.val < i.val then w ⟨i, h⟩ else if i = k then r' else X i ω))
          ∂(Measure.pi fun i : {i : Fin n // k.val < i.val} => Measure.map (X (i : Fin n)) P)| ≤ c := by
      intro r r'
      have hb : ∀ w : {i : Fin n // k.val < i.val} → ℝ,
          ‖G (fun i : Fin n => if h : k.val < i.val then w ⟨i, h⟩ else if i = k then r else X i ω)
            - G (fun i : Fin n => if h : k.val < i.val then w ⟨i, h⟩ else if i = k then r' else X i ω)‖ ≤ c := by
        intro w
        rw [Real.norm_eq_abs, abs_sub_comm]
        have hupd : (fun i : Fin n => if h : k.val < i.val then w ⟨i, h⟩ else if i = k then r else X i ω)
            = Function.update
                (fun i : Fin n => if h : k.val < i.val then w ⟨i, h⟩ else if i = k then r' else X i ω) k r := by
          funext i
          by_cases hik : i = k
          · subst hik
            simp [Function.update]
          · simp [Function.update, hik]
        rw [hupd]
        exact hG_stab k _ r
      have hmain := MeasureTheory.norm_integral_le_of_norm_le_const
        (μ := Measure.pi fun i : {i : Fin n // k.val < i.val} => Measure.map (X (i : Fin n)) P)
        (f := fun w : {i : Fin n // k.val < i.val} → ℝ =>
          G (fun i : Fin n => if h : k.val < i.val then w ⟨i, h⟩ else if i = k then r else X i ω)
            - G (fun i : Fin n => if h : k.val < i.val then w ⟨i, h⟩ else if i = k then r' else X i ω))
        (C := c)
        (by filter_upwards with w using hb w)
      simpa [Real.norm_eq_abs, hreal] using hmain
    have hmix :
        |∫ w, G (fun i : Fin n => if h : k.val < i.val then w ⟨i, h⟩ else if i = k then y else X i ω)
            ∂(Measure.pi fun i : {i : Fin n // k.val < i.val} => Measure.map (X (i : Fin n)) P)
          - ∫ w, G (fun i : Fin n => if h : k.val < i.val then w ⟨i, h⟩ else if i = k then y' else X i ω)
            ∂(Measure.pi fun i : {i : Fin n // k.val < i.val} => Measure.map (X (i : Fin n)) P)|
          = |∫ w, (G (fun i : Fin n => if h : k.val < i.val then w ⟨i, h⟩ else if i = k then y else X i ω)
            - G (fun i : Fin n => if h : k.val < i.val then w ⟨i, h⟩ else if i = k then y' else X i ω))
            ∂(Measure.pi fun i : {i : Fin n // k.val < i.val} => Measure.map (X (i : Fin n)) P)| := by
      rw [MeasureTheory.integral_sub (hGint y) (hGint y')]
    exact hmix.trans_le (hfar y y')
  · intro ω
    haveI hZ : ∀ i : {i : Fin n // k.val < i.val}, IsProbabilityMeasure (Measure.map (X (i : Fin n)) P) :=
      fun i => MeasureTheory.Measure.isProbabilityMeasure_map (hX_meas (i : Fin n)).aemeasurable
    haveI hk : IsProbabilityMeasure (Measure.map (X k) P) :=
      MeasureTheory.Measure.isProbabilityMeasure_map (hX_meas k).aemeasurable
    have hjoint : Measurable (fun p : ℝ × ({i : Fin n // k.val < i.val} → ℝ) =>
        G (fun i : Fin n => if h : k.val < i.val then p.2 ⟨i, h⟩ else if i = k then p.1 else X i ω)) := by
      refine hG_meas.comp ?_
      rw [measurable_pi_iff]
      intro i
      by_cases hlt : k.val < i.val
      · simp only [dif_pos hlt]
        measurability
      · simp only [dif_neg hlt]
        by_cases hik : i = k
        · simp only [if_pos hik]
          measurability
        · simp only [if_neg hik]
          measurability
    have hstrong : StronglyMeasurable (fun y : ℝ => ∫ w : {i : Fin n // k.val < i.val} → ℝ,
        G (fun i : Fin n => if h : k.val < i.val then w ⟨i, h⟩ else if i = k then y else X i ω)
        ∂(Measure.pi fun i : {i : Fin n // k.val < i.val} => Measure.map (X (i : Fin n)) P)) :=
      hjoint.stronglyMeasurable.integral_prod_right
    refine (MeasureTheory.integrable_const (μ := Measure.map (X k) P) B).mono'
      hstrong.aestronglyMeasurable ?_
    filter_upwards with y
    have hreal :
        (Measure.pi fun i : {i : Fin n // k.val < i.val} => Measure.map (X (i : Fin n)) P).real Set.univ
          = 1 := by simp
    have hmain := MeasureTheory.norm_integral_le_of_norm_le_const
      (μ := Measure.pi fun i : {i : Fin n // k.val < i.val} => Measure.map (X (i : Fin n)) P)
      (f := fun w : {i : Fin n // k.val < i.val} → ℝ =>
        G (fun i : Fin n => if h : k.val < i.val then w ⟨i, h⟩ else if i = k then y else X i ω))
      (C := B)
      (by filter_upwards with w; simpa [Real.norm_eq_abs] using hG_bound _)
    simpa [Real.norm_eq_abs, hreal] using hmain
  /- @proof-region region.target-node.session.c23fcba9be17739b end -/
