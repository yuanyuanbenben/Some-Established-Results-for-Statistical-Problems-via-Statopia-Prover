import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q03.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q03.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q03.ProvedNodes.Node_3499294657_adafef55_978ab895

open MeasureTheory Matrix ProbabilityTheory

open MeasureTheory Matrix ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_1894322428_a8d5bf89 : ∀ (nu : ℝ) (hnu : 0 < nu)
    (G : ℝ → ENNReal) (hG : Measurable G),
    ∫⁻ v, ENNReal.ofReal (gammaConvDensity (nu / 2) v) *
        (∫⁻ z, ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(z ^ 2 / 2))) *
          G (z / Real.sqrt (v / nu)) ∂volume) ∂volume
      = ∫⁻ t, ENNReal.ofReal (Real.Gamma ((nu + 1) / 2) /
            (Real.sqrt (nu * Real.pi) * Real.Gamma (nu / 2)) *
          Real.rpow (1 + t ^ 2 / nu) (-(nu + 1) / 2)) * G t ∂volume := by
  /- @proof-region region.target-node.session.16ffc0b0d15e8f33 begin -/
  intro nu hnu G hG
  set φ : ℝ → ENNReal := fun z => ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(z ^ 2 / 2))) with hφ
  have hφm : Measurable φ := by
    rw [hφ]
    exact ENNReal.measurable_ofReal.comp (by measurability)
  have hgcd : Measurable fun v : ℝ => gammaConvDensity (nu / 2) v := by
    have hmain : Measurable fun v : ℝ =>
        Real.exp (Real.log v * (nu / 2 - 1)) * Real.exp (-(v / 2)) /
          (Real.rpow 2 (nu / 2) * Real.Gamma (nu / 2)) := by
      have h1 : Measurable fun v : ℝ => Real.exp (Real.log v * (nu / 2 - 1)) :=
        Real.continuous_exp.measurable.comp (Real.measurable_log.mul measurable_const)
      have h2 : Measurable fun v : ℝ => Real.exp (-(v / 2)) :=
        Real.continuous_exp.measurable.comp (measurable_id.div_const 2).neg
      exact (h1.mul h2).div measurable_const
    have h : (fun v : ℝ => gammaConvDensity (nu / 2) v)
        = fun v => if 0 < v then
            Real.exp (Real.log v * (nu / 2 - 1)) * Real.exp (-(v / 2)) /
              (Real.rpow 2 (nu / 2) * Real.Gamma (nu / 2))
          else 0 := by
      funext v
      by_cases hv : 0 < v
      · have hkey : Real.rpow v (nu / 2 - 1) = Real.exp (Real.log v * (nu / 2 - 1)) :=
          Real.rpow_def_of_pos hv (nu / 2 - 1)
        rw [gammaConvDensity, if_pos hv, if_pos hv, hkey]
      · rw [gammaConvDensity, if_neg hv, if_neg hv]
    rw [h]
    exact Measurable.ite measurableSet_Ioi hmain measurable_const
  have hzero : ∀ v : ℝ, ¬ 0 < v → ENNReal.ofReal (gammaConvDensity (nu / 2) v) = 0 := by
    intro v hv
    rw [gammaConvDensity, if_neg hv, ENNReal.ofReal_zero]
  change ∫⁻ v, ENNReal.ofReal (gammaConvDensity (nu / 2) v) * (∫⁻ z, φ z * G (z / Real.sqrt (v / nu))) ∂volume
      = ∫⁻ t, ENNReal.ofReal (Real.Gamma ((nu + 1) / 2) /
            (Real.sqrt (nu * Real.pi) * Real.Gamma (nu / 2)) *
          Real.rpow (1 + t ^ 2 / nu) (-(nu + 1) / 2)) * G t ∂volume
  have hdil : ∀ v : ℝ, 0 < v →
      (∫⁻ z, φ z * G (z / Real.sqrt (v / nu)))
        = ENNReal.ofReal (Real.sqrt (v / nu)) *
            (∫⁻ t, φ (Real.sqrt (v / nu) * t) * G t) := by
    intro v hv
    have hs : 0 < Real.sqrt (v / nu) := Real.sqrt_pos.2 (by positivity)
    set s : ℝ := Real.sqrt (v / nu) with hsdef
    have hne : s ≠ 0 := ne_of_gt hs
    have hΨm : Measurable fun z : ℝ => φ z * G (z / s) :=
      hφm.mul (hG.comp (measurable_id.div_const s))
    have hmap : ENNReal.ofReal |s| • Measure.map (fun x : ℝ => s * x) (volume : Measure ℝ) = volume :=
      Real.smul_map_volume_mul_left hne
    have h1 : ∫⁻ z, φ z * G (z / s) ∂volume
        = ∫⁻ z, φ z * G (z / s) ∂(ENNReal.ofReal |s| • Measure.map (fun x : ℝ => s * x) volume) :=
      congrArg (fun μ : Measure ℝ => ∫⁻ z, φ z * G (z / s) ∂μ) hmap.symm
    have h2 : ∫⁻ z, φ z * G (z / s) ∂(ENNReal.ofReal |s| • Measure.map (fun x : ℝ => s * x) volume)
        = ENNReal.ofReal s * ∫⁻ t, φ (s * t) * G t ∂volume := by
      have hsm : Measurable fun x : ℝ => s * x := measurable_const.mul measurable_id
      have hstep1 : ∫⁻ z, φ z * G (z / s) ∂(ENNReal.ofReal |s| • Measure.map (fun x : ℝ => s * x) volume)
          = ENNReal.ofReal |s| •
              ∫⁻ z, φ z * G (z / s) ∂(Measure.map (fun x : ℝ => s * x) volume) :=
        MeasureTheory.lintegral_smul_measure (ENNReal.ofReal |s|) (fun z => φ z * G (z / s))
      have hst : ∀ t : ℝ, s * t / s = t := by
        intro t
        field_simp
      have hstep2 : ∫⁻ z, φ z * G (z / s) ∂(Measure.map (fun x : ℝ => s * x) volume)
          = ∫⁻ t, φ (s * t) * G (s * t / s) ∂volume :=
        MeasureTheory.lintegral_map hΨm hsm
      calc ∫⁻ z, φ z * G (z / s) ∂(ENNReal.ofReal |s| • Measure.map (fun x : ℝ => s * x) volume)
          = ENNReal.ofReal |s| •
              ∫⁻ z, φ z * G (z / s) ∂(Measure.map (fun x : ℝ => s * x) volume) := hstep1
        _ = ENNReal.ofReal |s| • ∫⁻ t, φ (s * t) * G (s * t / s) ∂volume := by rw [hstep2]
        _ = ENNReal.ofReal |s| • ∫⁻ t, φ (s * t) * G t ∂volume := by simp only [hst]
        _ = ENNReal.ofReal s * ∫⁻ t, φ (s * t) * G t ∂volume := by
              rw [abs_of_pos hs, smul_eq_mul]
    exact h1.trans h2
  have hglob : ∀ (v t : ℝ),
      ENNReal.ofReal (gammaConvDensity (nu / 2) v) *
          (ENNReal.ofReal (Real.sqrt (v / nu)) * (φ (Real.sqrt (v / nu) * t) * G t))
        = ENNReal.ofReal (gammaConvDensity (nu / 2) v * Real.sqrt (v / nu) *
            ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(t ^ 2 * v / (2 * nu))))) * G t := by
    intro v t
    by_cases hv : 0 < v
    · have hgd0 : 0 ≤ gammaConvDensity (nu / 2) v := by
        have h1 : 0 < Real.rpow v (nu / 2 - 1) := Real.rpow_pos_of_pos hv _
        have h2 : 0 < Real.exp (-(v / 2)) := Real.exp_pos _
        have h3 : 0 < Real.rpow 2 (nu / 2) := Real.rpow_pos_of_pos (by norm_num) _
        have h4 : 0 < Real.Gamma (nu / 2) := Real.Gamma_pos_of_pos (by linarith)
        rw [gammaConvDensity, if_pos hv]
        exact div_nonneg (mul_nonneg h1.le h2.le) (mul_pos h3 h4).le
      have hs0 : 0 ≤ Real.sqrt (v / nu) := Real.sqrt_nonneg _
      have hsq : Real.sqrt (v / nu) * Real.sqrt (v / nu) = v / nu :=
        Real.mul_self_sqrt (by positivity)
      have hexp : -((Real.sqrt (v / nu) * t) ^ 2 / 2) = -(t ^ 2 * v / (2 * nu)) := by
        congr 1
        rw [mul_pow, pow_two (Real.sqrt (v / nu)), hsq]
        field_simp
      have hφv : φ (Real.sqrt (v / nu) * t)
          = ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ *
              Real.exp (-((Real.sqrt (v / nu) * t) ^ 2 / 2))) := by
        rw [hφ]
      rw [hφv, hexp]
      have hc : 0 ≤ (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(t ^ 2 * v / (2 * nu))) := by positivity
      rw [ENNReal.ofReal_mul (mul_nonneg hgd0 hs0), ENNReal.ofReal_mul hgd0]
      ac_rfl
    · have h0 : gammaConvDensity (nu / 2) v = 0 := by
        rw [gammaConvDensity, if_neg hv]
      simp only [h0, ENNReal.ofReal_zero, zero_mul]
  have hA : ∫⁻ v, ENNReal.ofReal (gammaConvDensity (nu / 2) v) * (∫⁻ z, φ z * G (z / Real.sqrt (v / nu))) ∂volume
      = ∫⁻ v in Set.Ioi (0 : ℝ), ENNReal.ofReal (gammaConvDensity (nu / 2) v) *
          (∫⁻ z, φ z * G (z / Real.sqrt (v / nu))) ∂volume := by
    rw [← MeasureTheory.lintegral_indicator measurableSet_Ioi]
    apply MeasureTheory.lintegral_congr
    intro v
    by_cases hv : 0 < v
    · simp only [Set.indicator_of_mem (Set.mem_Ioi.2 hv)]
    · have h0 : ENNReal.ofReal (gammaConvDensity (nu / 2) v) *
          (∫⁻ z, φ z * G (z / Real.sqrt (v / nu))) = 0 := by
        rw [hzero v hv, zero_mul]
      have hmem : v ∉ Set.Ioi (0 : ℝ) := by simpa using hv
      rw [h0, Set.indicator_of_notMem hmem]
  have hB : ∫⁻ v in Set.Ioi (0 : ℝ), ENNReal.ofReal (gammaConvDensity (nu / 2) v) *
          (∫⁻ z, φ z * G (z / Real.sqrt (v / nu))) ∂volume
      = ∫⁻ v in Set.Ioi (0 : ℝ), ENNReal.ofReal (gammaConvDensity (nu / 2) v) *
          (ENNReal.ofReal (Real.sqrt (v / nu)) *
            ∫⁻ t, φ (Real.sqrt (v / nu) * t) * G t ∂volume) ∂volume := by
    apply MeasureTheory.lintegral_congr
    intro v
    by_cases hv : 0 < v
    · rw [hdil v hv]
    · simp only [hzero v hv, zero_mul]
  have hC : ∫⁻ v in Set.Ioi (0 : ℝ), ENNReal.ofReal (gammaConvDensity (nu / 2) v) *
          (ENNReal.ofReal (Real.sqrt (v / nu)) *
            ∫⁻ t, φ (Real.sqrt (v / nu) * t) * G t ∂volume) ∂volume
      = ∫⁻ v in Set.Ioi (0 : ℝ), ∫⁻ t, ENNReal.ofReal (gammaConvDensity (nu / 2) v) *
          (ENNReal.ofReal (Real.sqrt (v / nu)) *
            (φ (Real.sqrt (v / nu) * t) * G t)) ∂volume ∂volume := by
    apply MeasureTheory.lintegral_congr
    intro v
    have k1 : (∫⁻ t, ENNReal.ofReal (gammaConvDensity (nu / 2) v) *
          (ENNReal.ofReal (Real.sqrt (v / nu)) * (φ (Real.sqrt (v / nu) * t) * G t)) ∂volume)
        = ∫⁻ t, (φ (Real.sqrt (v / nu) * t) * G t) *
            (ENNReal.ofReal (gammaConvDensity (nu / 2) v) *
              ENNReal.ofReal (Real.sqrt (v / nu))) ∂volume := by
      apply MeasureTheory.lintegral_congr
      intro t
      ac_rfl
    have k2 : (∫⁻ t, (φ (Real.sqrt (v / nu) * t) * G t) *
            (ENNReal.ofReal (gammaConvDensity (nu / 2) v) *
              ENNReal.ofReal (Real.sqrt (v / nu))) ∂volume)
        = (∫⁻ t, φ (Real.sqrt (v / nu) * t) * G t ∂volume) *
            (ENNReal.ofReal (gammaConvDensity (nu / 2) v) *
              ENNReal.ofReal (Real.sqrt (v / nu))) :=
      by
        have hf2 : Measurable fun t : ℝ => φ (Real.sqrt (v / nu) * t) * G t :=
          (hφm.comp (measurable_const.mul measurable_id)).mul hG
        exact MeasureTheory.lintegral_mul_const _ hf2
    have k3 : (∫⁻ t, φ (Real.sqrt (v / nu) * t) * G t ∂volume) *
            (ENNReal.ofReal (gammaConvDensity (nu / 2) v) *
              ENNReal.ofReal (Real.sqrt (v / nu)))
        = ENNReal.ofReal (gammaConvDensity (nu / 2) v) *
            (ENNReal.ofReal (Real.sqrt (v / nu)) *
              ∫⁻ t, φ (Real.sqrt (v / nu) * t) * G t ∂volume) := by
      ac_rfl
    exact (k1.trans (k2.trans k3)).symm
  have hD : ∫⁻ v in Set.Ioi (0 : ℝ), ∫⁻ t, ENNReal.ofReal (gammaConvDensity (nu / 2) v) *
          (ENNReal.ofReal (Real.sqrt (v / nu)) *
            (φ (Real.sqrt (v / nu) * t) * G t)) ∂volume ∂volume
      = ∫⁻ t, ∫⁻ v in Set.Ioi (0 : ℝ), ENNReal.ofReal (gammaConvDensity (nu / 2) v) *
          (ENNReal.ofReal (Real.sqrt (v / nu)) *
            (φ (Real.sqrt (v / nu) * t) * G t)) ∂volume ∂volume := by
    have hm : AEMeasurable (Function.uncurry (fun (v t : ℝ) =>
        ENNReal.ofReal (gammaConvDensity (nu / 2) v) *
          (ENNReal.ofReal (Real.sqrt (v / nu)) * (φ (Real.sqrt (v / nu) * t) * G t))))
        ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume) := by
      refine Measurable.aemeasurable ?_
      change Measurable fun p : ℝ × ℝ =>
        ENNReal.ofReal (gammaConvDensity (nu / 2) p.1) *
          (ENNReal.ofReal (Real.sqrt (p.1 / nu)) * (φ (Real.sqrt (p.1 / nu) * p.2) * G p.2))
      have h1m : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (gammaConvDensity (nu / 2) p.1) :=
        ENNReal.measurable_ofReal.comp (hgcd.comp measurable_fst)
      have h2m : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (Real.sqrt (p.1 / nu)) :=
        ENNReal.measurable_ofReal.comp
          (Real.continuous_sqrt.measurable.comp (measurable_fst.div_const nu))
      have h3m : Measurable fun p : ℝ × ℝ => φ (Real.sqrt (p.1 / nu) * p.2) :=
        hφm.comp ((Real.continuous_sqrt.measurable.comp (measurable_fst.div_const nu)).mul
          measurable_snd)
      have h4m : Measurable fun p : ℝ × ℝ => G p.2 := hG.comp measurable_snd
      exact h1m.mul (h2m.mul (h3m.mul h4m))
    have hswap := MeasureTheory.lintegral_lintegral_swap
      (μ := volume.restrict (Set.Ioi (0 : ℝ))) (ν := volume)
      (f := fun (v t : ℝ) => ENNReal.ofReal (gammaConvDensity (nu / 2) v) *
        (ENNReal.ofReal (Real.sqrt (v / nu)) * (φ (Real.sqrt (v / nu) * t) * G t))) hm
    exact hswap
  have hE : ∫⁻ t, ∫⁻ v in Set.Ioi (0 : ℝ), ENNReal.ofReal (gammaConvDensity (nu / 2) v) *
          (ENNReal.ofReal (Real.sqrt (v / nu)) *
            (φ (Real.sqrt (v / nu) * t) * G t)) ∂volume ∂volume
      = ∫⁻ t, ∫⁻ v in Set.Ioi (0 : ℝ), ENNReal.ofReal (gammaConvDensity (nu / 2) v *
            Real.sqrt (v / nu) *
            ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(t ^ 2 * v / (2 * nu))))) *
          G t ∂volume ∂volume := by
    apply MeasureTheory.lintegral_congr
    intro t
    apply MeasureTheory.lintegral_congr
    intro v
    exact hglob v t
  have hF : ∫⁻ t, ∫⁻ v in Set.Ioi (0 : ℝ), ENNReal.ofReal (gammaConvDensity (nu / 2) v *
            Real.sqrt (v / nu) *
            ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(t ^ 2 * v / (2 * nu))))) *
          G t ∂volume ∂volume
      = ∫⁻ t, ENNReal.ofReal (Real.Gamma ((nu + 1) / 2) /
            (Real.sqrt (nu * Real.pi) * Real.Gamma (nu / 2)) *
          Real.rpow (1 + t ^ 2 / nu) (-(nu + 1) / 2)) * G t ∂volume := by
    apply MeasureTheory.lintegral_congr
    intro t
    have hmc : (∫⁻ v in Set.Ioi (0 : ℝ), ENNReal.ofReal (gammaConvDensity (nu / 2) v *
              Real.sqrt (v / nu) *
              ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(t ^ 2 * v / (2 * nu))))) * G t ∂volume)
        = (∫⁻ v in Set.Ioi (0 : ℝ), ENNReal.ofReal (gammaConvDensity (nu / 2) v *
              Real.sqrt (v / nu) *
              ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(t ^ 2 * v / (2 * nu))))) ∂volume) * G t :=
      by
        have hexpm : Measurable fun v : ℝ => Real.exp (-(t ^ 2 * v / (2 * nu))) := by measurability
        have hsqrt : Measurable fun v : ℝ => Real.sqrt (v / nu) :=
          Real.continuous_sqrt.measurable.comp (measurable_id.div_const nu)
        have hmp : Measurable fun v : ℝ => ENNReal.ofReal (gammaConvDensity (nu / 2) v *
              Real.sqrt (v / nu) *
              ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(t ^ 2 * v / (2 * nu))))) :=
          ENNReal.measurable_ofReal.comp ((hgcd.mul hsqrt).mul (measurable_const.mul hexpm))
        first
          | exact MeasureTheory.lintegral_mul_const _ hmp
          | exact MeasureTheory.lintegral_mul_const hmp _
          | exact MeasureTheory.lintegral_mul_const _ hmp.aemeasurable
          | exact MeasureTheory.lintegral_mul_const hmp.aemeasurable _
    rw [hmc, statopia_math_node_3499294657_adafef55 nu hnu t]
  exact hA.trans (hB.trans (hC.trans (hD.trans (hE.trans hF))))
  /- @proof-region region.target-node.session.16ffc0b0d15e8f33 end -/
