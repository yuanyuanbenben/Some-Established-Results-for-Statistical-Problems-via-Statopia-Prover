import ProverJobs.job_paper_b0cf39bbf6c845c9a6b30a5db43f8efa.Vocabulary
import ProverJobs.job_paper_b0cf39bbf6c845c9a6b30a5db43f8efa.Base
import ProverJobs.job_paper_b0cf39bbf6c845c9a6b30a5db43f8efa.ProvedNodes.Node_2505690190_62e6c818_d650a686

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal MeasureTheory Topology BigOperators
open Statlib.Imported
open Statlib.Imported.DPMModel

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal MeasureTheory Topology BigOperators
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_3862551001_c5ec6ec7 : ∀ {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (p0 f : X → ℝ≥0∞)
    (hp0_meas : Measurable p0) (hf_meas : Measurable f)
    (hp0_int : ∫⁻ x, p0 x ∂μ = 1) (hf_int : ∫⁻ x, f x ∂μ ≤ 1)
    (hkl : InformationTheory.klDiv (μ.withDensity p0) (μ.withDensity f) ≠ ⊤),
    (∀ᵐ x ∂(μ.withDensity p0), f x ≠ 0) ∧
      (∀ᵐ x ∂(μ.withDensity p0), f x < ⊤) ∧
      MeasureTheory.Integrable
        (fun x => Real.log (f x).toReal - Real.log (p0 x).toReal) (μ.withDensity p0) ∧
      -(InformationTheory.klDiv (μ.withDensity p0) (μ.withDensity f)).toReal ≤
        (∫ x, (Real.log (f x).toReal - Real.log (p0 x).toReal) ∂(μ.withDensity p0))
          + ((μ.withDensity p0).real Set.univ - (μ.withDensity f).real Set.univ) ∧
      (∫⁻ x, ENNReal.ofReal
          (max (Real.log (f x).toReal - Real.log (p0 x).toReal) 0) ∂(μ.withDensity p0)) ≤ 1 ∧
      (∫⁻ x, ENNReal.ofReal
          (max (-(Real.log (f x).toReal - Real.log (p0 x).toReal)) 0) ∂(μ.withDensity p0)) ≤
        ENNReal.ofReal
          ((InformationTheory.klDiv (μ.withDensity p0) (μ.withDensity f)).toReal + 1) := by
  /- @proof-region region.target-node.session.ec847a910bfdd19e begin -/
  intro X _ μ p0 f hp0_meas hf_meas hp0_int hf_int hkl
  have hnull : ∀ (g : X → ℝ≥0∞), Measurable g → (μ.withDensity g) {x : X | g x = 0} = 0 := by
    intro g hg
    have hgsm : MeasurableSet {x : X | g x = 0} := hg (measurableSet_singleton (0 : ℝ≥0∞))
    have hz : ∫⁻ a in {x : X | g x = 0}, g a ∂μ = 0 := by
      rw [← MeasureTheory.lintegral_indicator hgsm]
      have hfun : (fun a => {x : X | g x = 0}.indicator g a) = (fun _ => (0 : ℝ≥0∞)) := by
        funext a
        by_cases ha : g a = 0
        · simp [Set.indicator_apply, ha]
        · simp [Set.indicator_apply, ha]
      rw [hfun]
      simp
    rw [← MeasureTheory.setLIntegral_one ({x : X | g x = 0})]
    rw [MeasureTheory.setLIntegral_withDensity_eq_setLIntegral_mul μ hg measurable_const hgsm]
    simpa using hz
  have hfinite : ∀ (g : X → ℝ≥0∞), Measurable g → ∫⁻ x, g x ∂μ ≠ ⊤ →
      ∀ᵐ x ∂(μ.withDensity p0), g x < ⊤ := by
    intro g hg hgfin
    have hzero : μ {x | g x = ⊤} = 0 :=
      MeasureTheory.measure_eq_top_of_lintegral_ne_top hg.aemeasurable hgfin
    have hae : ∀ᵐ x ∂μ, g x < ⊤ := by
      rw [MeasureTheory.ae_iff]
      have hset : {x | ¬ g x < ⊤} = {x | g x = ⊤} := by ext x; simp
      rw [hset]
      exact hzero
    exact (MeasureTheory.withDensity_absolutelyContinuous μ p0).ae_le hae
  have hftop : ∫⁻ x, f x ∂μ ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hf_int (by simp))
  have hp0top' : ∫⁻ x, p0 x ∂μ ≠ ⊤ := by rw [hp0_int]; simp
  have h2 : ∀ᵐ x ∂(μ.withDensity p0), f x < ⊤ := hfinite f hf_meas hftop
  have hp0lt : ∀ᵐ x ∂(μ.withDensity p0), p0 x < ⊤ := hfinite p0 hp0_meas hp0top'
  have hPQ : μ.withDensity p0 ≪ μ.withDensity f := by
    by_contra h
    exact hkl (by rw [InformationTheory.klDiv_def, if_neg (fun hc => h hc.1)])
  have hf0 : ∀ᵐ x ∂(μ.withDensity f), f x ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    have hset : {x : X | ¬ f x ≠ 0} = {x : X | f x = 0} := by ext x; simp
    rw [hset]
    exact hnull f hf_meas
  have h1 : ∀ᵐ x ∂(μ.withDensity p0), f x ≠ 0 := hPQ.ae_le hf0
  have hp00 : ∀ᵐ x ∂(μ.withDensity p0), p0 x ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    have hset : {x : X | ¬ p0 x ≠ 0} = {x : X | p0 x = 0} := by ext x; simp
    rw [hset]
    exact hnull p0 hp0_meas
  have h5 : ∫⁻ x, ENNReal.ofReal (max (Real.log (f x).toReal - Real.log (p0 x).toReal) 0)
      ∂(μ.withDensity p0) ≤ 1 := by
    have hbound : ∀ᵐ x ∂(μ.withDensity p0),
        ENNReal.ofReal (max (Real.log (f x).toReal - Real.log (p0 x).toReal) 0) ≤ f x / p0 x := by
      filter_upwards [h1, h2, hp0lt, hp00] with x hf0 hftop hp0top hp0ne
      have hfx : 0 < (f x).toReal :=
        lt_of_le_of_ne ENNReal.toReal_nonneg
          (Ne.symm (ENNReal.toReal_ne_zero.mpr ⟨hf0, ne_of_lt hftop⟩))
      have hpx : 0 < (p0 x).toReal :=
        lt_of_le_of_ne ENNReal.toReal_nonneg
          (Ne.symm (ENNReal.toReal_ne_zero.mpr ⟨hp0ne, ne_of_lt hp0top⟩))
      have hlog : Real.log (f x).toReal - Real.log (p0 x).toReal
          = Real.log ((f x / p0 x).toReal) := by
        rw [ENNReal.toReal_div, Real.log_div (ne_of_gt hfx) (ne_of_gt hpx)]
      rw [hlog]
      have hs : (0:ℝ) < (f x / p0 x).toReal := by
        rw [ENNReal.toReal_div]
        exact div_pos hfx hpx
      calc ENNReal.ofReal (max (Real.log ((f x / p0 x).toReal)) 0)
          ≤ ENNReal.ofReal ((f x / p0 x).toReal) :=
            ENNReal.ofReal_mono
              (max_le (le_trans (Real.log_le_sub_one_of_pos hs) (by linarith)) (le_of_lt hs))
        _ ≤ f x / p0 x := ENNReal.ofReal_toReal_le
    have hmuldiv : ∀ a b : ℝ≥0∞, a * (b / a) ≤ b := by
      intro a b
      rcases eq_or_ne a 0 with h0 | h0
      · rw [h0]; simp
      rcases eq_or_ne a ⊤ with htop | htop
      · rw [htop]
        have hb : b / ⊤ = 0 := by
          rw [div_eq_mul_inv, ENNReal.inv_eq_zero.mpr rfl, mul_zero]
        rw [hb, mul_zero]
        exact zero_le b
      · have heq : a * (b / a) = b := by
          rw [div_eq_mul_inv, mul_comm b a⁻¹, ENNReal.mul_inv_cancel_left h0 htop]
        exact le_of_eq heq
    calc ∫⁻ x, ENNReal.ofReal (max (Real.log (f x).toReal - Real.log (p0 x).toReal) 0)
            ∂(μ.withDensity p0)
        ≤ ∫⁻ x, f x / p0 x ∂(μ.withDensity p0) := MeasureTheory.lintegral_mono_ae hbound
      _ = ∫⁻ x, p0 x * (f x / p0 x) ∂μ :=
            MeasureTheory.lintegral_withDensity_eq_lintegral_mul₀ (f := p0) hp0_meas.aemeasurable
              (g := fun x => f x / p0 x) (hf_meas.div hp0_meas).aemeasurable
      _ ≤ ∫⁻ x, f x ∂μ := MeasureTheory.lintegral_mono (fun x => hmuldiv (p0 x) (f x))
      _ ≤ 1 := hf_int
  obtain ⟨h3, h4, h6⟩ :=
    statopia_math_node_2505690190_62e6c818 μ p0 f hp0_meas hf_meas hp0_int hf_int hkl h5
  exact ⟨h1, h2, h3, h4, h5, h6⟩
  /- @proof-region region.target-node.session.ec847a910bfdd19e end -/

end Statlib.Imported
