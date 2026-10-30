import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q03.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q03.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q03.ProvedNodes.Node_3904179399_f59de535_8039d034
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q03.ProvedNodes.Node_859487190_88621b65_8a0d7230

open MeasureTheory Matrix ProbabilityTheory

open MeasureTheory Matrix ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_4173097495_a654df71 : ∀ (a b : ℝ) (ha : 0 < a) (hb : 0 < b),
    (((volume : Measure ℝ).withDensity
          (fun s : ℝ => ENNReal.ofReal (gammaConvDensity a s))).prod
        ((volume : Measure ℝ).withDensity
          (fun s : ℝ => ENNReal.ofReal (gammaConvDensity b s)))).map
        (fun p : ℝ × ℝ => p.1 + p.2)
      = (volume : Measure ℝ).withDensity
          (fun s : ℝ => ENNReal.ofReal (gammaConvDensity (a + b) s)) := by
  /- @proof-region region.target-node.session.8bf448e9ea1e8125 begin -/
  intro a b ha hb
  set Fa : ℝ → ENNReal := fun s => ENNReal.ofReal (gammaConvDensity a s) with hFa_def
  set Fb : ℝ → ENNReal := fun s => ENNReal.ofReal (gammaConvDensity b s) with hFb_def
  set Fab : ℝ → ENNReal := fun s => ENNReal.ofReal (gammaConvDensity (a + b) s) with hFab_def
  have hmeas_density (c : ℝ) :
      Measurable (fun s : ℝ => ENNReal.ofReal (gammaConvDensity c s)) := by
    have h_eq : (fun s : ℝ => ENNReal.ofReal (gammaConvDensity c s))
        = fun s : ℝ => ENNReal.ofReal
            (if 0 < s then
              Real.exp (Real.log s * (c - 1)) * Real.exp (-(s / 2)) /
                (Real.rpow 2 c * Real.Gamma c)
            else 0) := by
      funext s
      unfold gammaConvDensity
      by_cases hs : 0 < s
      · simp only [if_pos hs]
        change ENNReal.ofReal (s ^ (c - 1) * Real.exp (-(s / 2)) / (Real.rpow 2 c * Real.Gamma c)) =
          ENNReal.ofReal (Real.exp (Real.log s * (c - 1)) * Real.exp (-(s / 2)) / (Real.rpow 2 c * Real.Gamma c))
        rw [Real.rpow_def_of_pos hs]
      · simp only [if_neg hs]
    rw [h_eq]
    apply Measurable.ennreal_ofReal
    refine Measurable.ite (measurableSet_lt measurable_const measurable_id) ?_ measurable_const
    apply Measurable.div
    · apply Measurable.mul
      · exact Real.measurable_exp.comp (Real.measurable_log.mul measurable_const)
      · exact Real.measurable_exp.comp (by measurability)
    · exact measurable_const
  have hFa : Measurable Fa := by rw [hFa_def]; exact hmeas_density a
  have hFb : Measurable Fb := by rw [hFb_def]; exact hmeas_density b
  have hFab : Measurable Fab := by rw [hFab_def]; exact hmeas_density (a + b)
  set μ : Measure ℝ := volume.withDensity Fa with hμ_def
  set ν : Measure ℝ := volume.withDensity Fb with hν_def
  set P : Measure (ℝ × ℝ) := μ.prod ν with hP_def
  have hprod : P = (volume.prod volume).withDensity (fun p : ℝ × ℝ => Fa p.1 * Fb p.2) := by
    rw [hP_def, hμ_def, hν_def, MeasureTheory.prod_withDensity hFa hFb]
  have hmain : ∀ A : Set ℝ, MeasurableSet A →
      P ((fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' A) = ∫⁻ s in A, Fab s := by
    intro A hA
    set indA : ℝ → ENNReal := A.indicator (fun _ => 1) with hindA
    set B : Set (ℝ × ℝ) := (fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' A with hB_def
    have hB : MeasurableSet B := by rw [hB_def]; exact hA.preimage measurable_add
    have hindA_meas : Measurable indA := by rw [hindA]; exact measurable_const.indicator hA
    have h_ind : ∀ p : ℝ × ℝ,
        B.indicator (fun p => Fa p.1 * Fb p.2) p = indA (p.1 + p.2) * (Fa p.1 * Fb p.2) := by
      intro p
      rw [hindA, hB_def]
      by_cases hp : p.1 + p.2 ∈ A <;> simp [Set.indicator, hp]
    have h_meas_prod : AEMeasurable (fun p : ℝ × ℝ => indA (p.1 + p.2) * (Fa p.1 * Fb p.2)) (volume.prod volume) :=
      ((hindA_meas.comp (measurable_fst.add measurable_snd)).mul ((hFa.comp measurable_fst).mul (hFb.comp measurable_snd))).aemeasurable
    have h_meas_fun : AEMeasurable (Function.uncurry (fun x s : ℝ => Fa x * (indA s * Fb (s - x)))) (volume.prod volume) :=
      ((hFa.comp measurable_fst).mul ((hindA_meas.comp measurable_snd).mul (hFb.comp (measurable_snd.sub measurable_fst)))).aemeasurable
    have h1 : P B = ∫⁻ p, indA (p.1 + p.2) * (Fa p.1 * Fb p.2) ∂(volume.prod volume) := by
      rw [hprod]
      rw [MeasureTheory.withDensity_apply' (fun p : ℝ × ℝ => Fa p.1 * Fb p.2) B]
      rw [← MeasureTheory.lintegral_indicator hB (fun p => Fa p.1 * Fb p.2)]
      rw [show (fun p => B.indicator (fun p => Fa p.1 * Fb p.2) p) = (fun p => indA (p.1 + p.2) * (Fa p.1 * Fb p.2)) by
            funext p; exact h_ind p]
    have h2 : ∫⁻ p, indA (p.1 + p.2) * (Fa p.1 * Fb p.2) ∂(volume.prod volume) = ∫⁻ p, indA (p.1 + p.2) * (Fa p.1 * Fb p.2) ∂(volume.prod volume) := rfl
    have h3 : ∫⁻ p, indA (p.1 + p.2) * (Fa p.1 * Fb p.2) ∂(volume.prod volume) = ∫⁻ x, ∫⁻ y, indA (x + y) * (Fa x * Fb y) ∂volume ∂volume := by
      exact MeasureTheory.lintegral_prod (f := fun p : ℝ × ℝ => indA (p.1 + p.2) * (Fa p.1 * Fb p.2)) h_meas_prod
    have h4 : ∫⁻ x, ∫⁻ y, indA (x + y) * (Fa x * Fb y) ∂volume ∂volume = ∫⁻ x, Fa x * (∫⁻ y, indA (x + y) * Fb y) ∂volume := by
      rw [show (fun x => ∫⁻ y, indA (x + y) * (Fa x * Fb y)) = (fun x => Fa x * (∫⁻ y, indA (x + y) * Fb y)) by
            funext x
            rw [show (fun y => indA (x + y) * (Fa x * Fb y)) = (fun y => Fa x * (indA (x + y) * Fb y)) by
                  funext y; rw [← mul_assoc, mul_comm (indA (x + y)), mul_assoc]]
            exact MeasureTheory.lintegral_const_mul (Fa x) (by measurability)]
    have h5 : ∫⁻ x, Fa x * (∫⁻ y, indA (x + y) * Fb y) ∂volume = ∫⁻ x, Fa x * (∫⁻ s, indA s * Fb (s - x)) ∂volume := by
      rw [show (fun x => Fa x * (∫⁻ y, indA (x + y) * Fb y)) = (fun x => Fa x * (∫⁻ s, indA s * Fb (s - x))) by
            funext x
            congr 1
            rw [← MeasureTheory.lintegral_add_right_eq_self (fun s => indA s * Fb (s - x)) x]
            rw [show (fun y => (fun s => indA s * Fb (s - x)) (y + x)) = (fun y => indA (x + y) * Fb y) by
                  funext y; simp [add_comm, add_left_comm, add_assoc]]]
    have h6 : ∫⁻ x, Fa x * (∫⁻ s, indA s * Fb (s - x)) ∂volume = ∫⁻ x, ∫⁻ s, Fa x * (indA s * Fb (s - x)) ∂volume ∂volume := by
      rw [show (fun x => Fa x * (∫⁻ s, indA s * Fb (s - x))) = (fun x => ∫⁻ s, Fa x * (indA s * Fb (s - x))) by
            funext x
            exact (MeasureTheory.lintegral_const_mul (Fa x) (f := fun s => indA s * Fb (s - x)) (hindA_meas.mul (hFb.comp (measurable_id.sub measurable_const)))).symm]
    have h7 : ∫⁻ x, ∫⁻ s, Fa x * (indA s * Fb (s - x)) ∂volume ∂volume = ∫⁻ s, ∫⁻ x, Fa x * (indA s * Fb (s - x)) ∂volume ∂volume := by
      exact MeasureTheory.lintegral_lintegral_swap (f := fun x s => Fa x * (indA s * Fb (s - x))) h_meas_fun
    have h8 : ∫⁻ s, ∫⁻ x, Fa x * (indA s * Fb (s - x)) ∂volume ∂volume = ∫⁻ s, indA s * (∫⁻ x, Fa x * Fb (s - x)) ∂volume := by
      rw [show (fun s => ∫⁻ x, Fa x * (indA s * Fb (s - x))) = (fun s => indA s * (∫⁻ x, Fa x * Fb (s - x))) by
            funext s
            rw [show (fun x => Fa x * (indA s * Fb (s - x))) = (fun x => (Fa x * Fb (s - x)) * indA s) by
                  funext x; rw [← mul_assoc, mul_comm (Fa x), mul_assoc, mul_comm (indA s)]]
            calc
              ∫⁻ x, (Fa x * Fb (s - x)) * indA s = (∫⁻ x, Fa x * Fb (s - x)) * indA s := MeasureTheory.lintegral_mul_const (indA s) (f := fun x => Fa x * Fb (s - x)) (hFa.mul (hFb.comp ((measurable_const : Measurable fun _ : ℝ => s).sub measurable_id)))
              _ = indA s * (∫⁻ x, Fa x * Fb (s - x)) := mul_comm _ _]
    have h9 : ∫⁻ s, indA s * (∫⁻ x, Fa x * Fb (s - x)) ∂volume = ∫⁻ s, indA s * Fab s ∂volume := by
      rw [show (fun s => indA s * (∫⁻ x, Fa x * Fb (s - x))) = (fun s => indA s * Fab s) by
            funext s
            rw [show (fun x => Fa x * Fb (s - x)) = (fun x => ENNReal.ofReal (gammaConvDensity a x) * ENNReal.ofReal (gammaConvDensity b (s - x))) by
                  funext x; simp only [hFa_def, hFb_def]]
            rw [statopia_math_node_3904179399_f59de535 a b ha hb s]
            ]
    have h10 : ∫⁻ s, indA s * Fab s ∂volume = ∫⁻ s in A, Fab s := by
      rw [← MeasureTheory.lintegral_indicator hA]
      rw [show (fun s => indA s * Fab s) = (fun s => A.indicator (fun s => Fab s) s) by
            funext s
            rw [hindA]
            by_cases hs : s ∈ A <;> simp [Set.indicator, hs]]
    rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply measurable_add hA, hmain A hA]
  rw [MeasureTheory.withDensity_apply Fab hA]
  /- @proof-region region.target-node.session.8bf448e9ea1e8125 end -/
