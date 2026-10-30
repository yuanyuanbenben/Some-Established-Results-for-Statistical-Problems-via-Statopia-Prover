import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q03.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q03.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q03.ProvedNodes.Node_1894322428_a8d5bf89_48a8e5f7
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q03.ProvedNodes.Node_3499294657_adafef55_978ab895
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q03.ProvedNodes.Node_3678446978_c1498b57_7ef4111b

open MeasureTheory Matrix ProbabilityTheory

open MeasureTheory Matrix ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_2309641057_5900fd9f : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (nu : ℝ) (hnu : 0 < nu)
    (Z V : Ω → ℝ)
    (hZV : HasLaw (fun ω => (Z ω, V ω))
      ((gaussianReal 0 1).prod
        (volume.withDensity
          (fun v => ENNReal.ofReal (gammaConvDensity (nu / 2) v)))) P),
    let density : ℝ → ℝ := fun t =>
      Real.Gamma ((nu + 1) / 2) /
          (Real.sqrt (nu * Real.pi) * Real.Gamma (nu / 2)) *
        Real.rpow (1 + t ^ 2 / nu) (-(nu + 1) / 2)
    HasLaw (fun ω => Z ω / Real.sqrt (V ω / nu))
      (volume.withDensity (fun t => ENNReal.ofReal (density t))) P := by
  /- @proof-region region.target-node.session.b91ee561a120d575 begin -/
  intro _ _ P _ nu hnu Z V hZV
  show HasLaw (fun ω => Z ω / Real.sqrt (V ω / nu))
      (volume.withDensity (fun t => ENNReal.ofReal (Real.Gamma ((nu + 1) / 2) /
          (Real.sqrt (nu * Real.pi) * Real.Gamma (nu / 2)) *
        Real.rpow (1 + t ^ 2 / nu) (-(nu + 1) / 2)))) P
  set fd : ℝ → ENNReal := fun t => ENNReal.ofReal (Real.Gamma ((nu + 1) / 2) /
      (Real.sqrt (nu * Real.pi) * Real.Gamma (nu / 2)) *
    Real.rpow (1 + t ^ 2 / nu) (-(nu + 1) / 2)) with hfd
  set gd : ℝ → ENNReal := fun v => ENNReal.ofReal (gammaConvDensity (nu / 2) v) with hgd
  set hfun : ℝ × ℝ → ℝ := fun p => p.1 / Real.sqrt (p.2 / nu) with hhfun
  have hm : Measurable hfun := by rw [hhfun]; measurability
  have hgd_meas : Measurable gd := by
    rw [hgd]
    simp only [gammaConvDensity]
    have hsplit : (fun v : ℝ => ENNReal.ofReal
          (if 0 < v then Real.rpow v (nu / 2 - 1) * Real.exp (-(v / 2)) /
            (Real.rpow 2 (nu / 2) * Real.Gamma (nu / 2)) else 0))
        = fun v => if 0 < v then ENNReal.ofReal
          (Real.rpow v (nu / 2 - 1) * Real.exp (-(v / 2)) /
            (Real.rpow 2 (nu / 2) * Real.Gamma (nu / 2))) else 0 := by
      funext v
      by_cases hv : 0 < v <;> simp [hv]
    rw [hsplit]
    exact Measurable.ite measurableSet_Ioi (by measurability) measurable_const
  have hgd_lt : ∀ᵐ x ∂(volume : Measure ℝ), gd x < ⊤ := by rw [hgd]; simp
  set gd0 : ℝ → ENNReal :=
    fun z => ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(z ^ 2 / 2))) with hgd0
  have hgd0_meas : Measurable gd0 := by rw [hgd0]; measurability
  set rho : Measure ℝ := volume.withDensity fd with hrho
  set sgd : Measure (ℝ × ℝ) := (gaussianReal 0 1).prod (volume.withDensity gd) with hsgd
  have hgauss : (gaussianReal 0 1) = volume.withDensity gd0 := by
    rw [ProbabilityTheory.gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : NNReal) ≠ 0)]
    congr 1
    funext z
    have hval : ProbabilityTheory.gaussianPDFReal 0 1 z
        = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(z ^ 2 / 2)) := by
      simp only [ProbabilityTheory.gaussianPDFReal]
      ring_nf
      have hA : Real.pi * ((1 : NNReal) : ℝ) * 2 = Real.pi * 2 := by first | simp | norm_num
      have hB : z ^ 2 * (((1 : NNReal) : ℝ))⁻¹ * (-1 / 2) = z ^ 2 * (-1 / 2) := by
        first | simp | norm_num | ring
      rw [hA, hB]
    simp only [ProbabilityTheory.gaussianPDF, hval, hgd0]
  have hfd_meas : Measurable fd := by rw [hfd]; measurability
  have hind : ∀ (α : Type) [MeasurableSpace α] (μ : Measure α) (t : Set α), MeasurableSet t →
      ∫⁻ x, t.indicator (fun _ => (1 : ENNReal)) x ∂μ = μ t := by
    intro α _ μ t ht
    rw [MeasureTheory.lintegral_indicator ht]
    simp
  have hindm : ∀ (t : Set ℝ), MeasurableSet t →
      Measurable (t.indicator fun _ => (1 : ENNReal)) := by
    intro t ht
    exact Measurable.ite ht measurable_const measurable_const
  have hLaw_h : HasLaw hfun rho sgd := by
    refine ⟨hm.aemeasurable, ?_⟩
    have key : ∀ G : ℝ → ENNReal, Measurable G →
        ∫⁻ p : ℝ × ℝ, G (hfun p) ∂sgd = ∫⁻ t, G t ∂rho := by
      intro G hG
      have hstep1 : ∀ v : ℝ, ∫⁻ z, G (hfun (z, v)) ∂(gaussianReal 0 1)
          = ∫⁻ z, gd0 z * G (hfun (z, v)) ∂volume := by
        intro v
        rw [hgauss]
        exact MeasureTheory.lintegral_withDensity_eq_lintegral_mul volume hgd0_meas
          (by rw [hhfun]; measurability)
      have hstep2 : ∀ (H : ℝ → ENNReal),
          ∫⁻ v, H v ∂(volume.withDensity gd) = ∫⁻ v, gd v * H v ∂volume := by
        intro H
        exact MeasureTheory.lintegral_withDensity_eq_lintegral_mul_non_measurable₀ volume
          hgd_meas.aemeasurable hgd_lt H
      have hsgd' : sgd = (gaussianReal 0 1).prod (volume.withDensity gd) := hsgd
      have hrho' : rho = volume.withDensity fd := hrho
      rw [hsgd', hrho', MeasureTheory.lintegral_prod_symm (fun p : ℝ × ℝ => G (hfun p))
        (hG.comp_aemeasurable hm.aemeasurable)]
      simp only [hstep1]
      rw [hstep2]
      have hR : ∫⁻ t, G t ∂(volume.withDensity fd) = ∫⁻ t, fd t * G t ∂volume := by
        exact MeasureTheory.lintegral_withDensity_eq_lintegral_mul volume hfd_meas hG
      rw [hR]
      have hconv := statopia_math_node_1894322428_a8d5bf89 nu hnu G hG
      simpa only [hgd, hgd0, hfd, hhfun] using hconv
    ext s hs
    rw [MeasureTheory.Measure.map_apply_of_aemeasurable hm.aemeasurable hs]
    have h1 : sgd (hfun ⁻¹' s)
        = ∫⁻ p, (hfun ⁻¹' s).indicator (fun _ => (1 : ENNReal)) p ∂sgd :=
      (hind (α := ℝ × ℝ) sgd (hfun ⁻¹' s) (hm hs)).symm
    have e1 : ∫⁻ p, (hfun ⁻¹' s).indicator (fun _ => (1 : ENNReal)) p ∂sgd
        = ∫⁻ p, (s.indicator (fun _ => (1 : ENNReal))) (hfun p) ∂sgd := by
      apply MeasureTheory.lintegral_congr
      intro p
      by_cases hp : hfun p ∈ s
      · simp [hp]
      · simp [hp]
    rw [h1, e1, key (s.indicator fun _ => (1 : ENNReal)) (hindm s hs),
      hind (α := ℝ) rho s hs]
  exact (hLaw_h.comp hZV).congr (Filter.Eventually.of_forall fun ω => rfl)
  /- @proof-region region.target-node.session.b91ee561a120d575 end -/
