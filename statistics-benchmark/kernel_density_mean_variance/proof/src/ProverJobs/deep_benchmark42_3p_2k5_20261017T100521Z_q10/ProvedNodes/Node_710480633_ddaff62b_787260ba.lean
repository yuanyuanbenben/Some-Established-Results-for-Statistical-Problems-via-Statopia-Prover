import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q10.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q10.Base

open MeasureTheory ProbabilityTheory

open MeasureTheory ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_710480633_ddaff62b : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ → ℝ) (hp_meas : Measurable p)
    (pmax : ℝ) (hpmax : 0 ≤ pmax)
    (hp_nonneg : ∀ᵐ y ∂volume, 0 ≤ p y)
    (hp_bound : ∀ᵐ y ∂volume, p y ≤ pmax)
    (X : Ω → ℝ) (hX_meas : Measurable X)
    (hX_law : HasLaw X
      (volume.withDensity (fun y ↦ ENNReal.ofReal (p y))) P)
    (g : ℝ → ℝ) (hg_meas : Measurable g)
    (hg_int : Integrable g volume)
    (x h : ℝ) (hh : 0 < h),
    (Integrable (fun u : ℝ ↦ |g u| * p (x + h * u)) volume ∧
        (∀ᵐ u ∂volume, |g u * p (x + h * u)| ≤ pmax * |g u|)) ∧
      Integrable (fun u : ℝ ↦ g u * p (x + h * u)) volume ∧
      Integrable (fun ω ↦ g ((X ω - x) / h)) P ∧
      (∫ ω, g ((X ω - x) / h) ∂P
        = h * ∫ u, g u * p (x + h * u) ∂volume) := by
  /- @proof-region region.target-node.session.9359a4f1bebc1d4d begin -/
  intro Ω _ P _ p hp_meas pmax hpmax hp_nonneg hp_bound X hX_meas hX_law g hg_meas hg_int x h hh
  have hhne : h ≠ 0 := ne_of_gt hh
  have hφ_meas : Measurable fun u : ℝ => x + h * u := by fun_prop
  have hmeas_pu : Measurable fun u : ℝ => p (x + h * u) := hp_meas.comp hφ_meas
  have hp_enn : Measurable fun y : ℝ => ENNReal.ofReal (p y) := hp_meas.ennreal_ofReal
  have hp_lt_top : ∀ᵐ y ∂volume, ENNReal.ofReal (p y) < ⊤ := by
    filter_upwards with y using ENNReal.ofReal_lt_top
  have hμ_eq : P.map X = volume.withDensity (fun y : ℝ => ENNReal.ofReal (p y)) := hX_law.map_eq
  have hNullImg : ∀ s : Set ℝ, volume s = 0 →
      volume ((fun y : ℝ => (y - x) / h) '' s) = 0 := by
    intro s hs
    exact MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
      (μ := volume) (f := fun y : ℝ => (y - x) / h) (s := s) (by fun_prop) hs
  have hpre : ∀ s : Set ℝ, volume s = 0 →
      volume ((fun u : ℝ => x + h * u) ⁻¹' s) = 0 := by
    intro s hs
    have hset : ((fun y : ℝ => (y - x) / h) '' s) = ((fun u : ℝ => x + h * u) ⁻¹' s) := by
      ext u
      constructor
      · rintro ⟨y, hy, hyu⟩
        have hy' : x + h * u = y := by
          rw [← hyu, mul_div_cancel₀ (y - x) hhne]
          ring
        show x + h * u ∈ s
        rw [hy']
        exact hy
      · intro hu
        refine ⟨x + h * u, hu, ?_⟩
        show ((x + h * u) - x) / h = u
        rw [add_sub_cancel_left, mul_div_cancel_left₀ u hhne]
    rw [← hset]
    exact hNullImg s hs
  have hae_transfer : ∀ (q : ℝ → Prop), (∀ᵐ y ∂volume, q y) → ∀ᵐ u ∂volume, q (x + h * u) := by
    intro q hq
    rw [MeasureTheory.ae_iff] at hq ⊢
    have h := hpre {y : ℝ | ¬ q y} hq
    simpa using h
  have hae_nonneg : ∀ᵐ u ∂volume, 0 ≤ p (x + h * u) := hae_transfer _ hp_nonneg
  have hae_le : ∀ᵐ u ∂volume, p (x + h * u) ≤ pmax := hae_transfer _ hp_bound
  have hAbsInt : Integrable (fun u : ℝ => |g u|) volume := hg_int.abs
  have hmaj : Integrable (fun u : ℝ => pmax * |g u|) volume := by
    simpa using hAbsInt.const_mul pmax
  have hInt_abs : Integrable (fun u : ℝ => |g u| * p (x + h * u)) volume := by
    refine hmaj.mono' ((hg_meas.abs.mul hmeas_pu).aestronglyMeasurable) ?_
    filter_upwards [hae_nonneg, hae_le] with u h1 h2
    have h3 : |g u| * p (x + h * u) ≤ pmax * |g u| := by
      rw [mul_comm pmax]
      exact mul_le_mul_of_nonneg_left h2 (abs_nonneg (g u))
    rwa [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg h1]
  have hbound_ae : ∀ᵐ u ∂volume, |g u * p (x + h * u)| ≤ pmax * |g u| := by
    filter_upwards [hae_nonneg, hae_le] with u h1 h2
    have h3 : |g u| * p (x + h * u) ≤ pmax * |g u| := by
      rw [mul_comm pmax]
      exact mul_le_mul_of_nonneg_left h2 (abs_nonneg (g u))
    rwa [abs_mul, abs_of_nonneg h1]
  have hInt_prod : Integrable (fun u : ℝ => g u * p (x + h * u)) volume := by
    refine hmaj.mono' ((hg_meas.mul hmeas_pu).aestronglyMeasurable) ?_
    filter_upwards [hbound_ae] with u hu
    rwa [Real.norm_eq_abs]
  have hG_meas : Measurable fun y : ℝ => g ((y - x) / h) := hg_meas.comp (by fun_prop)
  have hTmap : ∀ (a : ℝ), MeasureTheory.Measure.map (fun v : ℝ => a + v) volume = volume := by
    intro a
    exact MeasureTheory.Measure.IsAddLeftInvariant.map_add_left_eq_self a
  have hTint : ∀ (F : ℝ → ℝ), Measurable F →
      ∫ v, F (x + v) ∂volume = ∫ y, F y ∂volume := by
    intro F hF
    have hmi : ∫ y, F y ∂(MeasureTheory.Measure.map (fun v : ℝ => x + v) volume)
        = ∫ v, F (x + v) ∂volume :=
      MeasureTheory.integral_map_of_stronglyMeasurable (φ := fun v : ℝ => x + v)
        (by fun_prop) hF.stronglyMeasurable
    rw [← hmi, hTmap x]
  have hDint : ∀ (F : ℝ → ℝ), Measurable F →
      ∫ u, F (h * u) ∂volume = h⁻¹ * ∫ y, F y ∂volume := by
    intro F hF
    have hm : MeasureTheory.Measure.map (fun u : ℝ => h * u) volume
        = ENNReal.ofReal h⁻¹ • volume := by
      have h1 := MeasureTheory.Measure.map_addHaar_smul (volume : Measure ℝ) (r := h) hhne
      simpa [abs_of_pos (inv_pos.mpr hh)] using h1
    have hmi : ∫ y, F y ∂(MeasureTheory.Measure.map (fun u : ℝ => h * u) volume)
        = ∫ u, F (h * u) ∂volume :=
      MeasureTheory.integral_map_of_stronglyMeasurable (φ := fun u : ℝ => h * u)
        (by fun_prop) hF.stronglyMeasurable
    rw [← hmi, hm, MeasureTheory.integral_smul_measure, smul_eq_mul,
      ENNReal.toReal_ofReal (le_of_lt (inv_pos.mpr hh))]
  have hsubst : ∀ (F : ℝ → ℝ), Measurable F →
      ∫ u, F (x + h * u) ∂volume = h⁻¹ * ∫ y, F y ∂volume := by
    intro F hF
    have hG : Measurable fun v : ℝ => F (x + v) := hF.comp (by fun_prop)
    have h2 : ∫ u, F (x + h * u) ∂volume = h⁻¹ * ∫ v, F (x + v) ∂volume :=
      hDint (fun v : ℝ => F (x + v)) hG
    rw [h2, hTint F hF]
  have hsubst_int : ∀ (F : ℝ → ℝ), Measurable F →
      Integrable (fun u : ℝ => F (x + h * u)) volume → Integrable F volume := by
    intro F hFmeas hFi
    have hD_meas : Measurable fun u : ℝ => h * u := by fun_prop
    have hT_meas : Measurable fun v : ℝ => x + v := by fun_prop
    have hFT_meas : Measurable fun v : ℝ => F (x + v) := hFmeas.comp hT_meas
    have hm : MeasureTheory.Measure.map (fun u : ℝ => h * u) volume
        = ENNReal.ofReal h⁻¹ • volume := by
      have h1 := MeasureTheory.Measure.map_addHaar_smul (volume : Measure ℝ) (r := h) hhne
      simpa [abs_of_pos (inv_pos.mpr hh)] using h1
    have hc0 : ENNReal.ofReal h⁻¹ ≠ 0 := by
      have hpos : 0 < ENNReal.ofReal h⁻¹ := ENNReal.ofReal_pos.mpr (inv_pos.mpr hh)
      exact hpos.ne'
    have step1 : Integrable (fun v : ℝ => F (x + v))
        (MeasureTheory.Measure.map (fun u : ℝ => h * u) volume) :=
      (MeasureTheory.integrable_map_measure (f := fun u : ℝ => h * u)
        (g := fun v : ℝ => F (x + v)) hFT_meas.aestronglyMeasurable
        hD_meas.aemeasurable).mpr (by simpa [Function.comp] using hFi)
    have step2 : Integrable (fun v : ℝ => F (x + v)) volume := by
      refine (MeasureTheory.integrable_smul_measure (f := fun v : ℝ => F (x + v))
        (c := ENNReal.ofReal h⁻¹) hc0 ENNReal.ofReal_ne_top).mp ?_
      rw [← hm]
      exact step1
    have step3 : Integrable F (MeasureTheory.Measure.map (fun v : ℝ => x + v) volume) :=
      (MeasureTheory.integrable_map_measure (f := fun v : ℝ => x + v) (g := F)
        hFmeas.aestronglyMeasurable hT_meas.aemeasurable).mpr step2
    rw [hTmap x] at step3
    exact step3
  have hsubst_eq : ∀ u : ℝ, (x + h * u - x) / h = u := by
    intro u
    rw [add_sub_cancel_left, mul_div_cancel_left₀ u hhne]
  have hF_int : Integrable (fun y : ℝ => g ((y - x) / h) * p y) volume := by
    refine hsubst_int (fun y : ℝ => g ((y - x) / h) * p y) (hG_meas.mul hp_meas) ?_
    refine hInt_prod.congr ?_
    filter_upwards with u
    rw [hsubst_eq u]
  have h_g_μ_int : Integrable (fun y : ℝ => g ((y - x) / h))
      (volume.withDensity (fun y : ℝ => ENNReal.ofReal (p y))) := by
    rw [MeasureTheory.integrable_withDensity_iff hp_enn hp_lt_top]
    refine hF_int.congr ?_
    filter_upwards [hp_nonneg] with y hy
    rw [ENNReal.toReal_ofReal hy]
  have hP_abs_int : Integrable (fun ω => |g ((X ω - x) / h)|) P := by
    refine ⟨(hG_meas.abs.comp hX_meas).aestronglyMeasurable, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_ofReal (f := fun ω => |g ((X ω - x) / h)|)
      (by filter_upwards with ω; exact abs_nonneg _)]
    have hkey : ∫⁻ ω, ENNReal.ofReal (|g ((X ω - x) / h)|) ∂P
        = ∫⁻ y, ENNReal.ofReal (|g ((y - x) / h)|) ∂(P.map X) :=
      (MeasureTheory.lintegral_map (μ := P) (g := X)
        (f := fun y : ℝ => ENNReal.ofReal (|g ((y - x) / h)|)) (by measurability) hX_meas).symm
    rw [hkey, hμ_eq]
    rw [← MeasureTheory.hasFiniteIntegral_iff_ofReal (f := fun y : ℝ => |g ((y - x) / h)|)
      (by filter_upwards with y; exact abs_nonneg _)]
    exact h_g_μ_int.abs.2
  have hP_int : Integrable (fun ω => g ((X ω - x) / h)) P := by
    refine hP_abs_int.mono' ((hG_meas.comp hX_meas).aestronglyMeasurable) ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs]
  have hstepC : ∫ y, g ((y - x) / h) ∂(volume.withDensity (fun y : ℝ => ENNReal.ofReal (p y)))
      = ∫ y, g ((y - x) / h) * p y ∂volume := by
    rw [integral_withDensity_eq_integral_toReal_smul hp_enn hp_lt_top]
    refine integral_congr_ae ?_
    filter_upwards [hp_nonneg] with y hy
    rw [smul_eq_mul, ENNReal.toReal_ofReal hy, mul_comm]
  have hstepB : ∫ y, g ((y - x) / h) * p y ∂volume = h * ∫ u, g u * p (x + h * u) ∂volume := by
    have hsb := hsubst (fun y : ℝ => g ((y - x) / h) * p y) (hG_meas.mul hp_meas)
    have hpt : (fun u : ℝ => g ((x + h * u - x) / h) * p (x + h * u))
        = (fun u : ℝ => g u * p (x + h * u)) := by
      funext u
      rw [hsubst_eq u]
    rw [hpt] at hsb
    have h2 : h * ∫ u, g u * p (x + h * u) ∂volume = ∫ y, g ((y - x) / h) * p y ∂volume := by
      rw [hsb, ← mul_assoc, mul_inv_cancel₀ hhne, one_mul]
    exact h2.symm
  have hstepD : ∫ ω, g ((X ω - x) / h) ∂P
      = ∫ y, g ((y - x) / h) ∂(volume.withDensity (fun y : ℝ => ENNReal.ofReal (p y))) := by
    have h := MeasureTheory.integral_map_of_stronglyMeasurable (μ := P) (φ := X)
      (f := fun y : ℝ => g ((y - x) / h)) hX_meas hG_meas.stronglyMeasurable
    rw [hμ_eq] at h
    exact h.symm
  have hSmap : MeasureTheory.Measure.map (fun u : ℝ => h * u) volume
      = ENNReal.ofReal h⁻¹ • volume := by
    have h1 := MeasureTheory.Measure.map_addHaar_smul (volume : Measure ℝ) (r := h) hhne
    simpa [abs_of_pos (inv_pos.mpr hh)] using h1
  refine ⟨⟨hInt_abs, hbound_ae⟩, hInt_prod, hP_int, ?_⟩
  rw [hstepD, hstepC, hstepB]
  /- @proof-region region.target-node.session.9359a4f1bebc1d4d end -/
