import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q31.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q31.Base

open MeasureTheory ProbabilityTheory

open MeasureTheory ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_4101882941_149a37f4 : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Measurable X) (hXnonneg : ∀ ω, 0 ≤ X ω)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (hsurvival : ∀ t : ℝ, 0 ≤ t →
      P {ω | t < X ω} = ENNReal.ofReal (Real.exp (-lambda * t))),
    ∀ c : ℝ, 0 ≤ c →
      (∫⁻ ω, ENNReal.ofReal (Real.exp (-c * X ω)) ∂P
          = ENNReal.ofReal (lambda / (lambda + c))) ∧
      (∫⁻ ω, ENNReal.ofReal (1 - Real.exp (-c * X ω)) ∂P
          = ENNReal.ofReal (c / (lambda + c))) := by
  /- @proof-region region.target-node.session.48a77032a23ee48e begin -/
  intro Ω mΩ P hP X hX hXnonneg lambda hlambda hsurvival c hc
  have hpt : ∀ s : ℝ, 0 ≤ s →
      ENNReal.ofReal (1 - Real.exp (-c * s))
        = ∫⁻ t, (Set.Ioo (0:ℝ) s).indicator
            (fun t => ENNReal.ofReal (c * Real.exp (-c * t))) t ∂volume := by
    intro s hs
    have hderiv : ∀ t : ℝ, HasDerivAt (fun x : ℝ => -Real.exp (-c * x)) (c * Real.exp (-c * t)) t := by
      intro t
      have h1 : HasDerivAt (fun x : ℝ => -c * x) (-c) t := by
        simpa using (hasDerivAt_id t).const_mul (-c)
      have h2 : HasDerivAt (fun x : ℝ => Real.exp (-c * x)) (Real.exp (-c * t) * (-c)) t :=
        (Real.hasDerivAt_exp (-c * t)).comp t h1
      have h3 : HasDerivAt (fun x : ℝ => -Real.exp (-c * x))
          (-(Real.exp (-c * t) * (-c))) t := h2.neg
      convert h3 using 1
      ring
    have hCont : Continuous (fun t : ℝ => c * Real.exp (-c * t)) := by continuity
    have hII : IntervalIntegrable (fun t : ℝ => c * Real.exp (-c * t)) volume (0:ℝ) s :=
      hCont.intervalIntegrable 0 s
    have hreal : ∫ t in (0:ℝ)..s, c * Real.exp (-c * t) = 1 - Real.exp (-c * s) := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t) hII]
      simp only [mul_zero, Real.exp_zero]
      ring
    have hIoc : ∫ t in Set.Ioc (0:ℝ) s, c * Real.exp (-c * t)
        = ∫ t in (0:ℝ)..s, c * Real.exp (-c * t) := by
      rw [intervalIntegral.integral_of_le hs]
    have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ s := by
      rw [MeasureTheory.ae_iff]
      simp
    have hIooIoc : ∫ t in Set.Ioo (0:ℝ) s, c * Real.exp (-c * t)
        = ∫ t in Set.Ioc (0:ℝ) s, c * Real.exp (-c * t) := by
      rw [← MeasureTheory.integral_indicator measurableSet_Ioo,
        ← MeasureTheory.integral_indicator measurableSet_Ioc]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [hae] with t ht
      by_cases h : (0:ℝ) < t ∧ t < s
      · have h1 : t ∈ Set.Ioo (0:ℝ) s := h
        have h2 : t ∈ Set.Ioc (0:ℝ) s := ⟨h.1, le_of_lt h.2⟩
        simp [h1, h2]
      · have h1 : t ∉ Set.Ioo (0:ℝ) s := h
        have h2 : t ∉ Set.Ioc (0:ℝ) s := by
          intro hc
          exact h ⟨hc.1, lt_of_le_of_ne hc.2 ht⟩
        simp [h1, h2]
    have hval : ∫ t in Set.Ioo (0:ℝ) s, c * Real.exp (-c * t) = 1 - Real.exp (-c * s) := by
      rw [hIooIoc, hIoc, hreal]
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioo (0:ℝ) s)]
        (fun t : ℝ => c * Real.exp (-c * t)) :=
      Filter.Eventually.of_forall (fun t => by positivity)
    have hInt : IntegrableOn (fun t : ℝ => c * Real.exp (-c * t)) (Set.Ioo (0:ℝ) s) := by
      have h2 : IntegrableOn (fun t : ℝ => c * Real.exp (-c * t)) (Set.Icc (0:ℝ) s) :=
        hCont.integrableOn_Icc
      exact h2.mono_set Set.Ioo_subset_Icc_self
    have hkey := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hnn
    have hA : ENNReal.ofReal (1 - Real.exp (-c * s))
        = ENNReal.ofReal (∫ t, c * Real.exp (-c * t) ∂(volume.restrict (Set.Ioo (0:ℝ) s))) := by
      congr 1
      exact hval.symm
    have hB : (∫⁻ t, (Set.Ioo (0:ℝ) s).indicator
          (fun t => ENNReal.ofReal (c * Real.exp (-c * t))) t ∂volume)
        = ∫⁻ t, ENNReal.ofReal (c * Real.exp (-c * t)) ∂(volume.restrict (Set.Ioo (0:ℝ) s)) := by
      rw [MeasureTheory.lintegral_indicator measurableSet_Ioo]
    rw [hA, hB]
    exact hkey
  have hmeas : AEMeasurable
      (Function.uncurry fun (ω : Ω) (t : ℝ) =>
        (Set.Ioo (0:ℝ) (X ω)).indicator (fun t => ENNReal.ofReal (c * Real.exp (-c * t))) t)
      (P.prod volume) := by
    apply Measurable.aemeasurable
    have hF : Measurable (fun p : Ω × ℝ => ENNReal.ofReal (c * Real.exp (-c * p.2))) := by
      measurability
    have hset : MeasurableSet {p : Ω × ℝ | p.2 ∈ Set.Ioo (0:ℝ) (X p.1)} := by
      have h2 : MeasurableSet {p : Ω × ℝ | p.2 < X p.1} :=
        StronglyMeasurable.measurableSet_lt measurable_snd.stronglyMeasurable
          (hX.comp measurable_fst).stronglyMeasurable
      have h1 : MeasurableSet {p : Ω × ℝ | (0:ℝ) < p.2} := measurable_snd measurableSet_Ioi
      exact h1.inter h2
    exact hF.indicator hset
  have hswap :
      (∫⁻ ω, ∫⁻ t, (Set.Ioo (0:ℝ) (X ω)).indicator
          (fun t => ENNReal.ofReal (c * Real.exp (-c * t))) t ∂volume ∂P)
        = ∫⁻ t, ∫⁻ ω, (Set.Ioo (0:ℝ) (X ω)).indicator
          (fun t => ENNReal.ofReal (c * Real.exp (-c * t))) t ∂P ∂volume := by
    exact MeasureTheory.lintegral_lintegral_swap hmeas
  have hcompl : ∫⁻ ω, ENNReal.ofReal (1 - Real.exp (-c * X ω)) ∂P
      = ENNReal.ofReal (c / (lambda + c)) := by
    calc ∫⁻ ω, ENNReal.ofReal (1 - Real.exp (-c * X ω)) ∂P
        = ∫⁻ ω, ∫⁻ t, (Set.Ioo (0:ℝ) (X ω)).indicator
            (fun t => ENNReal.ofReal (c * Real.exp (-c * t))) t ∂volume ∂P := by
          refine lintegral_congr (fun ω => hpt (X ω) (hXnonneg ω))
      _ = ∫⁻ t, ∫⁻ ω, (Set.Ioo (0:ℝ) (X ω)).indicator
            (fun t => ENNReal.ofReal (c * Real.exp (-c * t))) t ∂P ∂volume := hswap
      _ = ∫⁻ t, ENNReal.ofReal (c * Real.exp (-c * t)) * P {ω | 0 < t ∧ t < X ω} ∂volume := by
          refine lintegral_congr (fun t => ?_)
          have hset : MeasurableSet {ω : Ω | 0 < t ∧ t < X ω} := by
            by_cases h0 : (0:ℝ) < t
            · have h' : {ω : Ω | 0 < t ∧ t < X ω} = {ω : Ω | t < X ω} := by
                ext ω; simp [h0]
              rw [h']
              exact hX measurableSet_Ioi
            · have h' : {ω : Ω | 0 < t ∧ t < X ω} = (∅ : Set Ω) := by
                ext ω; simp [h0]
              rw [h']
              exact MeasurableSet.empty
          rw [show (∫⁻ ω : Ω, (Set.Ioo (0:ℝ) (X ω)).indicator
                (fun t => ENNReal.ofReal (c * Real.exp (-c * t))) t ∂P)
              = ∫⁻ ω : Ω, {ω : Ω | 0 < t ∧ t < X ω}.indicator
                  (fun _ => ENNReal.ofReal (c * Real.exp (-c * t))) ω ∂P from by
            refine lintegral_congr (fun ω => ?_)
            by_cases h : 0 < t ∧ t < X ω
            · simp [Set.mem_Ioo, h]
            · simp [Set.mem_Ioo, h]]
          rw [MeasureTheory.lintegral_indicator_const hset
            (ENNReal.ofReal (c * Real.exp (-c * t)))]
      _ = ∫⁻ t in Set.Ioi (0:ℝ),
            ENNReal.ofReal (c * Real.exp (-c * t)) * P {ω | t < X ω} ∂volume := by
          rw [← MeasureTheory.lintegral_indicator measurableSet_Ioi]
          refine lintegral_congr (fun t => ?_)
          by_cases ht : (0:ℝ) < t
          · have h' : {ω : Ω | 0 < t ∧ t < X ω} = {ω : Ω | t < X ω} := by
              ext ω; simp [ht]
            rw [h', Set.indicator_of_mem (show t ∈ Set.Ioi (0:ℝ) from ht)]
          · have h' : {ω : Ω | 0 < t ∧ t < X ω} = (∅ : Set Ω) := by
              ext ω; simp [ht]
            rw [h', MeasureTheory.measure_empty, mul_zero]
            simp [ht]
      _ = ∫⁻ t in Set.Ioi (0:ℝ),
            ENNReal.ofReal (c * Real.exp (-c * t)) *
              ENNReal.ofReal (Real.exp (-lambda * t)) ∂volume := by
          rw [← MeasureTheory.lintegral_indicator measurableSet_Ioi,
            ← MeasureTheory.lintegral_indicator measurableSet_Ioi]
          refine lintegral_congr (fun t => ?_)
          by_cases ht : t ∈ Set.Ioi (0:ℝ)
          · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht,
              hsurvival t (le_of_lt ht)]
          · have h0 : ¬ ((0:ℝ) < t) := by simpa using ht
            simp [h0]
      _ = ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (c * Real.exp (-(c + lambda) * t)) ∂volume := by
          rw [← MeasureTheory.lintegral_indicator measurableSet_Ioi,
            ← MeasureTheory.lintegral_indicator measurableSet_Ioi]
          refine lintegral_congr (fun t => ?_)
          by_cases ht : t ∈ Set.Ioi (0:ℝ)
          · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht,
              ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ c * Real.exp (-c * t))]
            rw [mul_assoc, ← Real.exp_add,
              show -c * t + -lambda * t = -(c + lambda) * t by ring]
          · have h0 : ¬ ((0:ℝ) < t) := by simpa using ht
            simp [h0]
      _ = ENNReal.ofReal (c / (c + lambda)) := by
          have hpos : (0:ℝ) < c + lambda := by linarith
          have hne : -(c + lambda) < 0 := by linarith
          have hInt : IntegrableOn (fun x : ℝ => c * Real.exp (-(c + lambda) * x))
              (Set.Ioi 0) := by
            have hb : IntegrableOn (fun x : ℝ => Real.exp (-(c + lambda) * x))
                (Set.Ioi 0) :=
              integrableOn_exp_mul_Ioi hne 0
            exact hb.const_mul c
          have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0:ℝ))]
              (fun x : ℝ => c * Real.exp (-(c + lambda) * x)) :=
            Filter.Eventually.of_forall (fun x => by positivity)
          have hexp : ∫ x in Set.Ioi (0:ℝ), Real.exp (-(c + lambda) * x) =
              1 / (c + lambda) := by
            have hcl : c + lambda ≠ 0 := by linarith
            rw [integral_exp_mul_Ioi hne 0, mul_zero, Real.exp_zero]
            field_simp
          have hval : ∫ x, (c * Real.exp (-(c + lambda) * x)) ∂
                (volume.restrict (Set.Ioi (0:ℝ))) = c / (c + lambda) := by
            rw [integral_const_mul]
            rw [show (∫ x, Real.exp (-(c + lambda) * x) ∂
                  (volume.restrict (Set.Ioi (0:ℝ))))
                = ∫ x in Set.Ioi (0:ℝ), Real.exp (-(c + lambda) * x) from rfl]
            rw [hexp]
            ring
          have hkey := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hnn
          show ∫⁻ x, ENNReal.ofReal (c * Real.exp (-(c + lambda) * x)) ∂
              (volume.restrict (Set.Ioi (0:ℝ))) = ENNReal.ofReal (c / (c + lambda))
          rw [← hkey, hval]
      _ = ENNReal.ofReal (c / (lambda + c)) := by
          rw [add_comm c lambda]
  have hmain : ∫⁻ ω, ENNReal.ofReal (Real.exp (-c * X ω)) ∂P
      = ENNReal.ofReal (lambda / (lambda + c)) := by
    have hpt2 : ∀ ω : Ω, ENNReal.ofReal (Real.exp (-c * X ω))
        + ENNReal.ofReal (1 - Real.exp (-c * X ω)) = 1 := by
      intro ω
      have h1 : (0:ℝ) ≤ Real.exp (-c * X ω) := (Real.exp_pos _).le
      have hmul : (0:ℝ) ≤ c * X ω := mul_nonneg hc (hXnonneg ω)
      have h2 : Real.exp (-c * X ω) ≤ 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by linarith)
      have h3 : (0:ℝ) ≤ 1 - Real.exp (-c * X ω) := by linarith
      rw [← ENNReal.ofReal_add h1 h3]
      rw [show Real.exp (-c * X ω) + (1 - Real.exp (-c * X ω)) = 1 by ring]
      exact ENNReal.ofReal_one
    have hAmeas : Measurable (fun ω : Ω => ENNReal.ofReal (Real.exp (-c * X ω))) := by
      measurability
    have hsum : (∫⁻ ω, ENNReal.ofReal (Real.exp (-c * X ω)) ∂P)
        + ∫⁻ ω, ENNReal.ofReal (1 - Real.exp (-c * X ω)) ∂P = 1 := by
      rw [← MeasureTheory.lintegral_add_left hAmeas]
      rw [show (∫⁻ ω, (ENNReal.ofReal (Real.exp (-c * X ω))
          + ENNReal.ofReal (1 - Real.exp (-c * X ω))) ∂P) = ∫⁻ ω, (1 : ENNReal) ∂P from
        lintegral_congr hpt2]
      simp
    have htarget : ENNReal.ofReal (lambda / (lambda + c))
        + ENNReal.ofReal (c / (lambda + c)) = 1 := by
      have h1 : (0:ℝ) ≤ lambda / (lambda + c) := by positivity
      have h2 : (0:ℝ) ≤ c / (lambda + c) := by positivity
      rw [← ENNReal.ofReal_add h1 h2]
      rw [show lambda / (lambda + c) + c / (lambda + c) = 1 by
        rw [← add_div, div_self (by positivity)]]
      exact ENNReal.ofReal_one
    have hsum' : (∫⁻ ω, ENNReal.ofReal (Real.exp (-c * X ω)) ∂P)
        + ENNReal.ofReal (c / (lambda + c)) = 1 := by
      rw [← hcompl]
      exact hsum
    have hBtop : ENNReal.ofReal (c / (lambda + c)) ≠ ⊤ := ENNReal.ofReal_ne_top
    have key : (∫⁻ ω, ENNReal.ofReal (Real.exp (-c * X ω)) ∂P)
        + ENNReal.ofReal (c / (lambda + c))
        = ENNReal.ofReal (lambda / (lambda + c))
          + ENNReal.ofReal (c / (lambda + c)) := by
      rw [hsum', htarget]
    refine (ENNReal.add_right_inj hBtop).mp ?_
    rw [add_comm (ENNReal.ofReal (c / (lambda + c)))]
    rw [add_comm (ENNReal.ofReal (c / (lambda + c)))]
    exact key
  exact ⟨hmain, hcompl⟩
  /- @proof-region region.target-node.session.48a77032a23ee48e end -/
