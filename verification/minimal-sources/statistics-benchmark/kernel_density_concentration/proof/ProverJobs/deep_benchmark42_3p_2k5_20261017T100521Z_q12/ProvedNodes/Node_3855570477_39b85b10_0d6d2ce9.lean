import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q12.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q12.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q12.ProvedNodes.Node_4045179614_089f2f1c_67ed62fd
open MeasureTheory ProbabilityTheory

open MeasureTheory ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_3855570477_39b85b10 : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 1 ≤ n)
    (X : Fin n → Ω → ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X P)
    (c B : ℝ) (hc : 0 ≤ c) (hB : 0 ≤ B)
    (G : (Fin n → ℝ) → ℝ) (hG_meas : Measurable G)
    (hG_bound : ∀ u : Fin n → ℝ, |G u| ≤ B)
    (hG_stab : ∀ (k : Fin n) (u : Fin n → ℝ) (t : ℝ),
      |G u - G (Function.update u k t)| ≤ c),
    let F : Fin (n + 1) → MeasurableSpace Ω :=
      fun j => ⨆ i : Fin n, ⨆ (_ : i.val < j.val), MeasurableSpace.comap (X i) inferInstance
    let Y : Ω → ℝ := fun ω => G (fun i => X i ω)
    ∀ k : Fin n, ∀ᵐ ω ∂P,
      |(P[Y | F k.succ]) ω - (P[Y | F k.castSucc]) ω| ≤ c := by
  /- @proof-region region.target-node.session.57c1069342cd59cf begin -/
  intro Ω _inst P _instP n _hn X hX_meas hX_indep c B _hc _hB G hG_meas hG_bound hG_stab
  let F : Fin (n + 1) → MeasurableSpace Ω :=
    fun j => ⨆ i : Fin n, ⨆ (_ : i.val < j.val), MeasurableSpace.comap (X i) inferInstance
  let Y : Ω → ℝ := fun ω => G (fun i => X i ω)
  show ∀ k : Fin n, ∀ᵐ ω ∂P, |(P[Y | F k.succ]) ω - (P[Y | F k.castSucc]) ω| ≤ c
  intro k
  have hXvec_meas : Measurable (fun ω => fun i => X i ω) := measurable_pi_iff.mpr hX_meas
  have hY_meas : Measurable Y := hG_meas.comp hXvec_meas
  have hY_bound : ∀ ω, |Y ω| ≤ B := fun ω => hG_bound (fun i => X i ω)
  have hY_int : Integrable Y P := by
    have hlin : ∫⁻ ω, ENNReal.ofReal ‖Y ω‖ ∂P ≤ ENNReal.ofReal B := by
      calc ∫⁻ ω, ENNReal.ofReal ‖Y ω‖ ∂P
          ≤ ∫⁻ _ : Ω, ENNReal.ofReal B ∂P := by
            refine lintegral_mono_ae ?_
            filter_upwards with ω
            exact ENNReal.ofReal_le_ofReal (by rw [Real.norm_eq_abs]; exact hY_bound ω)
        _ = ENNReal.ofReal B * P Set.univ := lintegral_const (ENNReal.ofReal B)
        _ = ENNReal.ofReal B := by rw [measure_univ, mul_one]
    refine ⟨hY_meas.aestronglyMeasurable, ?_⟩
    have hle : ∫⁻ ω, ‖Y ω‖ₑ ∂P ≤ ENNReal.ofReal B := by
      simpa only [Real.enorm_eq_ofReal_abs, Real.norm_eq_abs] using hlin
    exact lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top)
  have hF_le : ∀ j : Fin (n + 1), F j ≤ (inferInstance : MeasurableSpace Ω) := by
    intro j
    refine iSup_le fun i => iSup_le fun _ => ?_
    exact measurable_iff_comap_le.mp (hX_meas i)
  let Z : Type := {i : Fin n // k.val < i.val}
  let νZ : Measure (Z → ℝ) := Measure.pi (fun i : Z => P.map (X (i : Fin n)))
  let Afun : Ω → ℝ → ℝ := fun ω y =>
    ∫ w : Z → ℝ,
      G (fun i : Fin n => if h : k.val < i.val then w ⟨i, h⟩ else if i = k then y else X i ω)
      ∂νZ
  let μk : Measure ℝ := P.map (X k)
  have hcore :
      (P[Y | F k.succ] =ᵐ[P] fun ω => Afun ω (X k ω)) ∧
      (P[Y | F k.castSucc] =ᵐ[P] fun ω => ∫ y : ℝ, Afun ω y ∂μk) ∧
      (∀ (ω : Ω) (y : ℝ), |Afun ω y| ≤ B) ∧
      (∀ (ω : Ω) (y y' : ℝ), |Afun ω y - Afun ω y'| ≤ c) ∧
      (∀ ω : Ω, Integrable (fun y : ℝ => Afun ω y) μk) := by
    exact statopia_math_node_4045179614_089f2f1c P n X hX_meas hX_indep c B _hc _hB G
      hG_meas hG_bound hG_stab k
  obtain ⟨hid1, hid2, hAbnd, hAstab, hAint⟩ := hcore
  filter_upwards [hid1, hid2] with ω h1 h2
  rw [h1, h2]
  have hμk_univ : μk Set.univ = 1 := by
    rw [Measure.map_apply (hX_meas k) MeasurableSet.univ]
    simp
  have hμk_real : μk.real Set.univ = 1 := by
    have h2 : (μk Set.univ).toReal = 1 := by rw [hμk_univ]; simp
    exact h2
  haveI : IsProbabilityMeasure μk := ⟨hμk_univ⟩
  have hconst : ∫ y : ℝ, Afun ω (X k ω) ∂μk = Afun ω (X k ω) := by
    rw [integral_const, hμk_real]
    simp
  have hint_sub : Integrable (fun y : ℝ => Afun ω (X k ω) - Afun ω y) μk :=
    (integrable_const (Afun ω (X k ω))).sub (hAint ω)
  have hdiff : ∫ y : ℝ, (Afun ω (X k ω) - Afun ω y) ∂μk
      = Afun ω (X k ω) - ∫ y : ℝ, Afun ω y ∂μk := by
    rw [integral_sub (integrable_const _) (hAint ω), hconst]
  have habs_int : Integrable (fun y : ℝ => |Afun ω (X k ω) - Afun ω y|) μk := by
    simpa only [Real.norm_eq_abs] using hint_sub.norm
  calc |Afun ω (X k ω) - ∫ y : ℝ, Afun ω y ∂μk|
      = |∫ y : ℝ, (Afun ω (X k ω) - Afun ω y) ∂μk| := by rw [hdiff]
    _ ≤ ∫ y : ℝ, |Afun ω (X k ω) - Afun ω y| ∂μk := abs_integral_le_integral_abs
    _ ≤ ∫ _ : ℝ, c ∂μk := by
        refine integral_mono_ae habs_int (integrable_const c) ?_
        filter_upwards with y
        exact hAstab ω (X k ω) y
    _ = c := by
        rw [integral_const, hμk_real]
        simp
  /- @proof-region region.target-node.session.57c1069342cd59cf end -/
