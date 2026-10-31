import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q03.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q03.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q03.ProvedNodes.Node_859487190_88621b65_8a0d7230

open MeasureTheory Matrix ProbabilityTheory

open MeasureTheory Matrix ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_3904179399_f59de535 : ∀ (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (s : ℝ),
    (∫⁻ (x : ℝ),
        ENNReal.ofReal (gammaConvDensity a x) * ENNReal.ofReal (gammaConvDensity b (s - x)))
      = ENNReal.ofReal (gammaConvDensity (a + b) s) := by
  /- @proof-region region.target-node.session.af497e1c2f3bad33 begin -/
  intro a b ha hb s
  have hnonneg : ∀ (c : ℝ), 0 < c → ∀ t : ℝ, 0 ≤ gammaConvDensity c t := by
    intro c hc t
    by_cases ht : 0 < t
    · simp only [gammaConvDensity, if_pos ht]
      exact div_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le)
        (mul_pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) c)
          (Real.Gamma_pos_of_pos hc)).le
    · simp [gammaConvDensity, if_neg ht]
  have hzero : ∀ (c t : ℝ), t ≤ 0 → gammaConvDensity c t = 0 := by
    intro c t ht
    simp [gammaConvDensity, if_neg (not_lt.mpr ht)]
  by_cases hs : 0 < s
  swap
  · have hs0 : s ≤ 0 := not_lt.mp hs
    have hz : ∀ x : ℝ,
        ENNReal.ofReal (gammaConvDensity a x) * ENNReal.ofReal (gammaConvDensity b (s - x)) = 0 := by
      intro x
      by_cases hx : 0 < x
      · rw [hzero b (s - x) (by linarith), ENNReal.ofReal_zero, mul_zero]
      · rw [hzero a x (not_lt.mp hx), ENNReal.ofReal_zero, zero_mul]
    rw [show (∫⁻ x : ℝ,
        ENNReal.ofReal (gammaConvDensity a x) * ENNReal.ofReal (gammaConvDensity b (s - x))) = 0 from by
      simp [hz],
      hzero (a + b) s hs0, ENNReal.ofReal_zero]
  · have hprod_nonneg : ∀ x : ℝ, 0 ≤ gammaConvDensity a x * gammaConvDensity b (s - x) :=
      fun x => mul_nonneg (hnonneg a ha x) (hnonneg b hb (s - x))
    have hofReal : ∀ x : ℝ,
        ENNReal.ofReal (gammaConvDensity a x) * ENNReal.ofReal (gammaConvDensity b (s - x))
          = ENNReal.ofReal (gammaConvDensity a x * gammaConvDensity b (s - x)) :=
      fun x => (ENNReal.ofReal_mul (hnonneg a ha x)).symm
    have hout : ∀ x : ℝ, x ∉ Set.Ioo (0 : ℝ) s →
        ENNReal.ofReal (gammaConvDensity a x * gammaConvDensity b (s - x)) = 0 := by
      intro x hx
      have hx' : x ≤ 0 ∨ s ≤ x := by
        simpa only [Set.mem_Ioo, not_and_or, not_lt] using hx
      have hp : gammaConvDensity a x * gammaConvDensity b (s - x) = 0 := by
        rcases hx' with h | h
        · rw [hzero a x h, zero_mul]
        · rw [hzero b (s - x) (by linarith), mul_zero]
      rw [hp, ENNReal.ofReal_zero]
    have hsupp : (∫⁻ x,
          ENNReal.ofReal (gammaConvDensity a x * gammaConvDensity b (s - x)))
        = ∫⁻ x in Set.Ioo (0 : ℝ) s,
          ENNReal.ofReal (gammaConvDensity a x * gammaConvDensity b (s - x)) := by
      have hfun : (fun x : ℝ =>
            ENNReal.ofReal (gammaConvDensity a x * gammaConvDensity b (s - x)))
          = (Set.Ioo (0 : ℝ) s).indicator (fun x : ℝ =>
              ENNReal.ofReal (gammaConvDensity a x * gammaConvDensity b (s - x))) := by
        funext x
        by_cases hx : x ∈ Set.Ioo (0 : ℝ) s
        · simp [Set.indicator, hx]
        · simp [Set.indicator, hx, hout x hx]
      refine Eq.trans (congrArg (fun g : ℝ → ENNReal => ∫⁻ x, g x) hfun) ?_
      exact MeasureTheory.lintegral_indicator isOpen_Ioo.measurableSet _
    have hdep := statopia_math_node_859487190_88621b65 a b ha hb s hs
    have hint : MeasureTheory.Integrable
        (fun x : ℝ => gammaConvDensity a x * gammaConvDensity b (s - x))
        (volume.restrict (Set.Ioo (0 : ℝ) s)) := by
      by_contra h
      have h0 : ∫ x in Set.Ioo (0 : ℝ) s,
          gammaConvDensity a x * gammaConvDensity b (s - x) = 0 :=
        MeasureTheory.integral_undef h
      rw [hdep] at h0
      have hpos : 0 < gammaConvDensity (a + b) s := by
        simp only [gammaConvDensity, if_pos hs]
        exact div_pos (mul_pos (Real.rpow_pos_of_pos hs _) (Real.exp_pos _))
          (mul_pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (a + b))
            (Real.Gamma_pos_of_pos (by linarith)))
      linarith
    calc (∫⁻ x, ENNReal.ofReal (gammaConvDensity a x) * ENNReal.ofReal (gammaConvDensity b (s - x)))
        = ∫⁻ x, ENNReal.ofReal (gammaConvDensity a x * gammaConvDensity b (s - x)) := by
          simp only [hofReal]
      _ = ∫⁻ x in Set.Ioo (0 : ℝ) s,
            ENNReal.ofReal (gammaConvDensity a x * gammaConvDensity b (s - x)) := hsupp
      _ = ENNReal.ofReal (∫ x in Set.Ioo (0 : ℝ) s,
            gammaConvDensity a x * gammaConvDensity b (s - x)) :=
          (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
            (Filter.Eventually.of_forall hprod_nonneg)).symm
      _ = ENNReal.ofReal (gammaConvDensity (a + b) s) := by rw [hdep]
  /- @proof-region region.target-node.session.af497e1c2f3bad33 end -/
