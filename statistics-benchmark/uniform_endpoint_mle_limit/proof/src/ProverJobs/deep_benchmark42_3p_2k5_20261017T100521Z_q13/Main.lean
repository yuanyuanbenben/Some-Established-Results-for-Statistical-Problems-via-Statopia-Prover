import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q13.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q13.ProvedNodes
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q13.Base

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

theorem uniform_endpoint_mle_limit
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (θ : ℝ) (hθ : 0 < θ)
    (X : ℕ → Ω → ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X P)
    (hX_uniform : ∀ i, MeasureTheory.pdf.IsUniform (X i) (Set.Ioo 0 θ) P)
    (Z : Ω → ℝ) (hZ_meas : Measurable Z)
    (hZ_law : HasLaw Z (expMeasure θ⁻¹) P) :
    let M : ℕ → Ω → ℝ := fun r ω ↦
      (Finset.univ : Finset (Fin (r + 1))).sup'
        Finset.univ_nonempty (fun i ↦ X i.1 ω)
    TendstoInDistribution
      (fun r ω ↦ ((r + 1 : ℕ) : ℝ) * (θ - M r ω))
      atTop Z P
:= by
  /- @proof-region region.root.8a9d20703ed9 begin -/
  classical
  dsimp only
  have hM_meas : ∀ r : ℕ, Measurable (fun ω : Ω =>
      (Finset.univ : Finset (Fin (r + 1))).sup' Finset.univ_nonempty (fun i => X i.1 ω)) := by
    intro r
    have hsup : (fun ω : Ω => (Finset.univ : Finset (Fin (r + 1))).sup'
        Finset.univ_nonempty (fun i => X i.1 ω))
        = (Finset.univ : Finset (Fin (r + 1))).sup'
          Finset.univ_nonempty (fun i => X i.1) := by
      funext ω
      exact (Finset.sup'_apply (s := (Finset.univ : Finset (Fin (r + 1))))
        Finset.univ_nonempty (fun i => X i.1) ω).symm
    rw [hsup]
    exact Finset.measurable_sup' Finset.univ_nonempty (fun i _ => hX_meas i.1)
  have hV_meas : ∀ r : ℕ, AEMeasurable (fun ω : Ω =>
      ((r + 1 : ℕ) : ℝ) *
        (θ - (Finset.univ : Finset (Fin (r + 1))).sup' Finset.univ_nonempty
          (fun i => X i.1 ω))) P :=
    fun r => ((measurable_const.sub (hM_meas r)).const_mul ((r + 1 : ℕ) : ℝ)).aemeasurable
  have hZmap : Measure.map Z P = expMeasure θ⁻¹ :=
    (hZ_law.measurePreserving hZ_meas).map_eq
  have hθinv : 0 < θ⁻¹ := inv_pos.mpr hθ
  have hν_prob : IsProbabilityMeasure (expMeasure θ⁻¹) :=
    (statopia_math_node_3356630755_4409a240 θ⁻¹ hθinv).1
  have hν_cdf : ∀ t : ℝ, (expMeasure θ⁻¹) (Set.Iic t) =
      if t ≤ 0 then 0 else ENNReal.ofReal (1 - Real.exp (-(θ⁻¹ * t))) :=
    (statopia_math_node_3356630755_4409a240 θ⁻¹ hθinv).2
  have hconv : ∀ t : ℝ, Tendsto (fun r : ℕ => (P.map (fun ω => ((r + 1 : ℕ) : ℝ) *
      (θ - (Finset.univ : Finset (Fin (r + 1))).sup' Finset.univ_nonempty
        (fun i => X i.1 ω)))) (Set.Iic t)) atTop (𝓝 ((expMeasure θ⁻¹) (Set.Iic t))) := by
    intro t
    by_cases ht : t ≤ 0
    · have hμ0 := fun r : ℕ =>
        statopia_math_node_3661166939_5226b67c P θ hθ X hX_meas hX_indep hX_uniform r t ht
      rw [hν_cdf, if_pos ht]
      simp only [hμ0]
      exact tendsto_const_nhds
    · have ht0 : 0 < t := by linarith
      have hν_eq : (expMeasure θ⁻¹) (Set.Iic t) =
          ENNReal.ofReal (1 - Real.exp (-t / θ)) := by
        rw [hν_cdf, if_neg ht]
        have harg : -(θ⁻¹ * t) = -t / θ := by ring
        rw [harg]
      rw [hν_eq]
      have hreal :=
        (statopia_math_node_2515949496_7d7e9f51 P θ hθ X hX_meas hX_indep hX_uniform t ht0).2
      have hcont : Tendsto ENNReal.ofReal (𝓝 (1 - Real.exp (-t / θ)))
          (𝓝 (ENNReal.ofReal (1 - Real.exp (-t / θ)))) :=
        ENNReal.continuous_ofReal.tendsto (1 - Real.exp (-t / θ))
      have hfun : (fun r : ℕ => (P.map (fun ω => ((r + 1 : ℕ) : ℝ) *
          (θ - (Finset.univ : Finset (Fin (r + 1))).sup' Finset.univ_nonempty
            (fun i => X i.1 ω)))) (Set.Iic t))
          = fun r : ℕ => ENNReal.ofReal (((P.map (fun ω => ((r + 1 : ℕ) : ℝ) *
            (θ - (Finset.univ : Finset (Fin (r + 1))).sup' Finset.univ_nonempty
              (fun i => X i.1 ω)))) (Set.Iic t)).toReal) := by
        funext r
        exact (ENNReal.ofReal_toReal (measure_lt_top _ _).ne).symm
      rw [hfun]
      exact hcont.comp hreal
  have hconvZ : ∀ t : ℝ, Tendsto (fun r : ℕ => (P.map (fun ω => ((r + 1 : ℕ) : ℝ) *
      (θ - (Finset.univ : Finset (Fin (r + 1))).sup' Finset.univ_nonempty
        (fun i => X i.1 ω)))) (Set.Iic t)) atTop (𝓝 ((Measure.map Z P) (Set.Iic t))) := by
    intro t
    rw [hZmap]
    exact hconv t
  refine ⟨fun r => hV_meas r, hZ_meas.aemeasurable, ?_⟩
  exact statopia_math_node_2594530977_cabbe74c
    (fun r => Measure.map (fun ω => ((r + 1 : ℕ) : ℝ) *
      (θ - (Finset.univ : Finset (Fin (r + 1))).sup' Finset.univ_nonempty
        (fun i => X i.1 ω))) P)
    (fun r => Measure.isProbabilityMeasure_map (hV_meas r))
    (Measure.map Z P) (Measure.isProbabilityMeasure_map hZ_meas.aemeasurable) hconvZ
  /- @proof-region region.root.8a9d20703ed9 end -/
