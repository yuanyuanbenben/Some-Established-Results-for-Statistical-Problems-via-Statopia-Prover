import Statlib.StatFoundation.BasicAnalysis.ENNRealBridge
import ProverJobs.job_paper_b0cf39bbf6c845c9a6b30a5db43f8efa.Vocabulary
import ProverJobs.job_paper_b0cf39bbf6c845c9a6b30a5db43f8efa.Base

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal MeasureTheory Topology BigOperators
open Statlib.Imported
open Statlib.Imported.DPMModel

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal MeasureTheory Topology BigOperators
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_2407238401_b71e9352 : ∀ {X : Type*} [MeasurableSpace X] (μ : Measure X) (p0 f : X → ℝ≥0∞)
    (hp0_meas : Measurable p0) (hf_meas : Measurable f)
    (hp0_int : ∫⁻ x, p0 x ∂μ = 1) (hf_int : ∫⁻ x, f x ∂μ ≤ 1)
    (hne : ∀ᵐ x ∂(μ.withDensity p0), f x ≠ 0)
    (hlt : ∀ᵐ x ∂(μ.withDensity p0), f x < ⊤)
    (hInt : MeasureTheory.Integrable
      (fun x => Real.log (f x).toReal - Real.log (p0 x).toReal) (μ.withDensity p0))
    (hdefect : -(InformationTheory.klDiv (μ.withDensity p0) (μ.withDensity f)).toReal ≤
      (∫ x, (Real.log (f x).toReal - Real.log (p0 x).toReal) ∂(μ.withDensity p0))
        + ((μ.withDensity p0).real Set.univ - (μ.withDensity f).real Set.univ)),
    (∫ x, (Real.log (f x).toReal - Real.log (p0 x).toReal) ∂(μ.withDensity p0) ≤ 0) ∧
    (1 - (μ.withDensity f).real Set.univ
      ≤ 2 * Real.sqrt ((InformationTheory.klDiv (μ.withDensity p0) (μ.withDensity f)).toReal)) := by
  /- @proof-region region.target-node.session.e3a804acb2cf2a73 begin -/
  intro X instX μ p0 f hp0_meas hf_meas hp0_int hf_int hne hlt hInt hdefect
  set P : Measure X := μ.withDensity p0 with hP_def
  set Q : Measure X := μ.withDensity f with hQ_def
  set K : ℝ≥0∞ := InformationTheory.klDiv P Q with hK_def
  let u : X → ℝ := fun x => (f x).toReal / (p0 x).toReal
  set q : ℝ := Q.real Set.univ with hq_def
  have hPabs : P ≪ μ := by
    rw [hP_def]
    exact MeasureTheory.withDensity_absolutelyContinuous μ p0
  have hp0_top_ae : ∀ᵐ x ∂μ, p0 x < ⊤ :=
    MeasureTheory.ae_lt_top hp0_meas (by rw [hp0_int]; exact ENNReal.one_ne_top)
  have hp0_top_P : ∀ᵐ x ∂P, p0 x < ⊤ := by
    have h := hp0_top_ae
    rw [MeasureTheory.ae_iff] at h
    rw [MeasureTheory.ae_iff]
    exact hPabs h
  have hP_univ : P Set.univ = 1 := by
    rw [hP_def, MeasureTheory.withDensity_apply p0 MeasurableSet.univ]
    simpa using hp0_int
  haveI hPfin : IsFiniteMeasure P := ⟨by rw [hP_univ]; simp⟩
  have hP_real : P.real Set.univ = 1 := by
    show (P Set.univ).toReal = 1
    rw [hP_univ, ENNReal.toReal_one]
  have hPf0 : P {x : X | f x = 0} = 0 := by
    have h := hne
    rw [MeasureTheory.ae_iff] at h
    simpa only [ne_eq, not_not] using h
  have hq_eq : q = (∫⁻ x, f x ∂μ).toReal := by
    have hQ_univ : Q Set.univ = ∫⁻ x, f x ∂μ := by
      rw [hQ_def, MeasureTheory.withDensity_apply f MeasurableSet.univ]
      simp
    show (Q Set.univ).toReal = (∫⁻ x, f x ∂μ).toReal
    rw [hQ_univ]
  have hq_le_one : q ≤ 1 := by
    rw [hq_eq]
    calc (∫⁻ x, f x ∂μ).toReal ≤ (1 : ℝ≥0∞).toReal :=
          ENNReal.toReal_mono ENNReal.one_ne_top hf_int
      _ = 1 := ENNReal.toReal_one
  have hq_pos : 0 < q := by
    have hSmeas : MeasurableSet {x : X | f x = 0} := by
      have h : MeasurableSet (f ⁻¹' ({0} : Set ℝ≥0∞)) := hf_meas (measurableSet_singleton 0)
      have hset : f ⁻¹' ({0} : Set ℝ≥0∞) = {x : X | f x = 0} := by
        ext x
        simp
      rwa [hset] at h
    have hPS : P {x : X | f x ≠ 0} = 1 := by
      have hset : {x : X | f x ≠ 0} = {x : X | f x = 0}ᶜ := by
        ext x
        simp
      have hfin : P {x : X | f x = 0} ≠ ⊤ :=
        ne_top_of_le_ne_top (by rw [hP_univ]; exact ENNReal.one_ne_top)
          (measure_mono (Set.subset_univ _))
      have hc : P {x : X | f x = 0}ᶜ = P Set.univ - P {x : X | f x = 0} :=
        MeasureTheory.measure_compl hSmeas hfin
      rw [hset, hc, hPf0, tsub_zero, hP_univ]
    have hmuS : μ {x : X | f x ≠ 0} ≠ 0 := by
      intro h0
      have hP0 : P {x : X | f x ≠ 0} = 0 := hPabs h0
      rw [hP0] at hPS
      exact one_ne_zero hPS.symm
    have hpos_int : 0 < ∫⁻ x, f x ∂μ := by
      have hz : ∫⁻ x, f x ∂μ ≠ 0 := by
        intro h0
        have hf0 : f =ᵐ[μ] (0 : X → ℝ≥0∞) :=
          (MeasureTheory.lintegral_eq_zero_iff hf_meas).mp h0
        apply hmuS
        have h : ∀ᵐ x ∂μ, f x = 0 := hf0
        rw [MeasureTheory.ae_iff] at h
        simpa only [ne_eq, not_not] using h
      exact lt_of_le_of_ne (zero_le _) (Ne.symm hz)
    rw [hq_eq]
    exact ENNReal.toReal_pos hpos_int.ne'
      (ne_top_of_le_ne_top ENNReal.one_ne_top hf_int)
  have hp0_ne_P : ∀ᵐ x ∂P, p0 x ≠ 0 := by
    have hs : MeasurableSet {x : X | p0 x = 0} := by
      have h : MeasurableSet (p0 ⁻¹' ({0} : Set ℝ≥0∞)) := hp0_meas (measurableSet_singleton 0)
      have hset : p0 ⁻¹' ({0} : Set ℝ≥0∞) = {x : X | p0 x = 0} := by
        ext x
        simp
      rwa [hset] at h
    have hzero : P {x : X | p0 x = 0} = 0 := by
      rw [hP_def, MeasureTheory.withDensity_apply p0 hs]
      have hcont : ∀ᵐ x ∂(μ.restrict {x : X | p0 x = 0}), p0 x = 0 := by
        filter_upwards [MeasureTheory.ae_restrict_mem hs] with x hx
        exact hx
      rw [MeasureTheory.lintegral_congr_ae hcont]
      simp
    rw [MeasureTheory.ae_iff]
    simpa only [ne_eq, not_not] using hzero
  have hu_meas : Measurable u :=
    hf_meas.ennreal_toReal.div hp0_meas.ennreal_toReal
  have hu_nonneg : 0 ≤ᵐ[P] u := by
    filter_upwards with x
    exact div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hu_pos_ae : ∀ᵐ x ∂P, 0 < u x := by
    filter_upwards [hp0_ne_P, hp0_top_P, hne, hlt] with x h1 h2 h3 h4
    exact div_pos (ENNReal.toReal_pos h3 (ne_of_lt h4))
      (ENNReal.toReal_pos h1 (ne_of_lt h2))
  have hpt_le : ∀ x, p0 x * ENNReal.ofReal (u x) ≤ f x := by
    intro x
    by_cases h0 : p0 x = 0
    · rw [h0, zero_mul]
      exact zero_le _
    · by_cases htop : p0 x = ⊤
      · have huz : u x = 0 := by
          show (f x).toReal / (p0 x).toReal = 0
          rw [htop, ENNReal.toReal_top]
          simp
        rw [huz, htop]
        simp
      · have hp0pos : 0 < (p0 x).toReal := ENNReal.toReal_pos h0 htop
        have hof : ENNReal.ofReal (u x) = ENNReal.ofReal ((f x).toReal) / p0 x := by
          show ENNReal.ofReal ((f x).toReal / (p0 x).toReal) =
            ENNReal.ofReal ((f x).toReal) / p0 x
          rw [ENNReal.ofReal_div_of_pos hp0pos, ENNReal.ofReal_toReal htop]
        rw [hof, ENNReal.div_eq_inv_mul, ENNReal.mul_inv_cancel_left h0 htop]
        exact ENNReal.ofReal_toReal_le
  have hcm : ∫⁻ x, ENNReal.ofReal (u x) ∂P = ∫⁻ x, p0 x * ENNReal.ofReal (u x) ∂μ := by
    rw [hP_def]
    exact MeasureTheory.lintegral_withDensity_eq_lintegral_mul_non_measurable μ hp0_meas hp0_top_ae _
  have hu_lintegral_le : ∫⁻ x, ENNReal.ofReal (u x) ∂P ≤ ∫⁻ x, f x ∂μ := by
    rw [hcm]
    exact MeasureTheory.lintegral_mono hpt_le
  have hu_ne_top : ∫⁻ x, ENNReal.ofReal (u x) ∂P ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (hu_lintegral_le.trans hf_int)
  have hu_int : MeasureTheory.Integrable u P :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hu_meas.aestronglyMeasurable
      hu_nonneg).mp hu_ne_top
  have hu_integral : ∫ x, u x ∂P = (∫⁻ x, ENNReal.ofReal (u x) ∂P).toReal :=
    Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.integral_eq_lintegral_toReal_of_nonneg
      hu_nonneg hu_int
  have hq'_le : ∫ x, u x ∂P ≤ q := by
    rw [hu_integral, hq_eq]
    exact ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top hf_int) hu_lintegral_le
  have hlogu_eq : ∀ᵐ x ∂P, Real.log (u x) = Real.log (f x).toReal - Real.log (p0 x).toReal := by
    filter_upwards [hp0_ne_P, hp0_top_P, hne, hlt] with x h1 h2 h3 h4
    have hpf : 0 < (p0 x).toReal := ENNReal.toReal_pos h1 (ne_of_lt h2)
    have hff : 0 < (f x).toReal := ENNReal.toReal_pos h3 (ne_of_lt h4)
    show Real.log ((f x).toReal / (p0 x).toReal) =
      Real.log (f x).toReal - Real.log (p0 x).toReal
    rw [Real.log_div hff.ne' hpf.ne']
  have hlogu_int : MeasureTheory.Integrable (fun x => Real.log (u x)) P :=
    hInt.congr (by
      filter_upwards [hlogu_eq] with x hx
      exact hx.symm)
  have htangent : ∀ᵐ x ∂P, Real.log (u x) ≤ Real.log q + u x / q - 1 := by
    filter_upwards [hu_pos_ae] with x hx
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < u x / q from div_pos hx hq_pos)
    rw [Real.log_div hx.ne' hq_pos.ne'] at h
    linarith
  have hRHS_int : MeasureTheory.Integrable (fun x => Real.log q + u x / q - 1) P := by
    have h1 : MeasureTheory.Integrable (fun x => u x / q) P := hu_int.div_const q
    have h2 : MeasureTheory.Integrable (fun _ : X => Real.log q) P :=
      MeasureTheory.integrable_const _
    have h3 : MeasureTheory.Integrable (fun x => Real.log q + u x / q) P := h2.add h1
    have h4 : MeasureTheory.Integrable (fun _ : X => (1:ℝ)) P :=
      MeasureTheory.integrable_const _
    exact h3.sub h4
  have hRHS_integral : ∫ x, (Real.log q + u x / q - 1) ∂P
      = Real.log q + (∫ x, u x ∂P) / q - 1 := by
    have h1 : MeasureTheory.Integrable (fun x => u x / q) P := hu_int.div_const q
    have h2 : MeasureTheory.Integrable (fun _ : X => Real.log q) P :=
      MeasureTheory.integrable_const _
    have h3 : MeasureTheory.Integrable (fun x => Real.log q + u x / q) P := h2.add h1
    have h4 : MeasureTheory.Integrable (fun _ : X => (1:ℝ)) P :=
      MeasureTheory.integrable_const _
    have hsub : ∫ x, (Real.log q + u x / q - (1:ℝ)) ∂P
        = ∫ x, (Real.log q + u x / q) ∂P - ∫ x, (1:ℝ) ∂P :=
      MeasureTheory.integral_sub h3 h4
    have hadd : ∫ x, (Real.log q + u x / q) ∂P
        = ∫ x, Real.log q ∂P + ∫ x, u x / q ∂P :=
      MeasureTheory.integral_add h2 h1
    have hdiv : ∫ x, u x / q ∂P = (∫ x, u x ∂P) / q := MeasureTheory.integral_div q u
    have hc : ∫ x, Real.log q ∂P = P.real Set.univ * Real.log q := by
      rw [MeasureTheory.integral_const]
      simp [smul_eq_mul]
    have hc1 : ∫ x, (1:ℝ) ∂P = P.real Set.univ := by
      rw [MeasureTheory.integral_const]
      simp [smul_eq_mul]
    rw [hsub, hadd, hdiv, hc, hc1, hP_real]
    ring
  have hA_le : ∫ x, (Real.log (f x).toReal - Real.log (p0 x).toReal) ∂P ≤ Real.log q := by
    have hA_eq : ∫ x, (Real.log (f x).toReal - Real.log (p0 x).toReal) ∂P
        = ∫ x, Real.log (u x) ∂P := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [hlogu_eq] with x hx
      exact hx.symm
    rw [hA_eq]
    calc ∫ x, Real.log (u x) ∂P ≤ ∫ x, (Real.log q + u x / q - 1) ∂P :=
          MeasureTheory.integral_mono_ae hlogu_int hRHS_int htangent
      _ = Real.log q + (∫ x, u x ∂P) / q - 1 := hRHS_integral
      _ ≤ Real.log q := by
          have hq1 : (∫ x, u x ∂P) / q ≤ 1 := by
            rw [div_le_one hq_pos]
            exact hq'_le
          linarith
  have hK_ge : -Real.log q + q - 1 ≤ K.toReal := by
    have h := hdefect
    rw [hP_real] at h
    linarith [hA_le, h]
  have hK_sq : (1 - Real.sqrt q) ^ 2 ≤ K.toReal := by
    have hlog : Real.log (Real.sqrt q) ≤ Real.sqrt q - 1 :=
      Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hq_pos)
    have hsq : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq_pos.le
    have hlogq : Real.log q = 2 * Real.log (Real.sqrt q) := by
      rw [← hsq, Real.log_pow]
      norm_num
    nlinarith [hK_ge, hlog, hlogq]
  have hsqrt_le : 1 - Real.sqrt q ≤ Real.sqrt K.toReal := by
    have hs1 : Real.sqrt q ≤ 1 := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt hq_le_one
    have h1 : (0:ℝ) ≤ 1 - Real.sqrt q := by linarith
    calc 1 - Real.sqrt q = Real.sqrt ((1 - Real.sqrt q) ^ 2) := (Real.sqrt_sq h1).symm
      _ ≤ Real.sqrt K.toReal := Real.sqrt_le_sqrt hK_sq
  constructor
  · exact hA_le.trans (Real.log_nonpos hq_pos.le hq_le_one)
  · have hsq : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq_pos.le
    have hs1 : Real.sqrt q ≤ 1 := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt hq_le_one
    have hprod : 1 - q = (1 - Real.sqrt q) * (1 + Real.sqrt q) := by nlinarith [hsq]
    have hstep1 : (1 - Real.sqrt q) * (1 + Real.sqrt q) ≤ (1 - Real.sqrt q) * 2 :=
      mul_le_mul_of_nonneg_left (by linarith : 1 + Real.sqrt q ≤ 2)
        (by linarith : (0:ℝ) ≤ 1 - Real.sqrt q)
    have hstep2 : (1 - Real.sqrt q) * 2 ≤ Real.sqrt K.toReal * 2 :=
      mul_le_mul_of_nonneg_right hsqrt_le (by norm_num : (0:ℝ) ≤ 2)
    linarith
  /- @proof-region region.target-node.session.e3a804acb2cf2a73 end -/

end Statlib.Imported
