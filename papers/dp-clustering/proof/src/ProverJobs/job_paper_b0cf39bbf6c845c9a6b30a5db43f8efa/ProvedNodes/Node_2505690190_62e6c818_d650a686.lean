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
theorem statopia_math_node_2505690190_62e6c818 : ∀ {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (p0 f : X → ℝ≥0∞)
    (hp0_meas : Measurable p0) (hf_meas : Measurable f)
    (hp0_int : ∫⁻ x, p0 x ∂μ = 1) (hf_int : ∫⁻ x, f x ∂μ ≤ 1)
    (hkl : InformationTheory.klDiv (μ.withDensity p0) (μ.withDensity f) ≠ ⊤)
    (h5 : ∫⁻ x, ENNReal.ofReal
        (max (Real.log (f x).toReal - Real.log (p0 x).toReal) 0) ∂(μ.withDensity p0) ≤ 1),
    MeasureTheory.Integrable
        (fun x => Real.log (f x).toReal - Real.log (p0 x).toReal) (μ.withDensity p0) ∧
      -(InformationTheory.klDiv (μ.withDensity p0) (μ.withDensity f)).toReal ≤
        ∫ x, (Real.log (f x).toReal - Real.log (p0 x).toReal) ∂(μ.withDensity p0)
          + ((μ.withDensity p0).real Set.univ - (μ.withDensity f).real Set.univ) ∧
      ∫⁻ x, ENNReal.ofReal (max (-(Real.log (f x).toReal - Real.log (p0 x).toReal)) 0)
          ∂(μ.withDensity p0) ≤
        ENNReal.ofReal
          ((InformationTheory.klDiv (μ.withDensity p0) (μ.withDensity f)).toReal + 1) := by
  /- @proof-region region.target-node.session.fc5d945887d094e7 begin -/
  intro X _ μ p0 f hp0_meas hf_meas hp0_int hf_int hkl h5
  set P : Measure X := μ.withDensity p0 with hP
  set Q : Measure X := μ.withDensity f with hQ
  set G : X → ℝ := fun x => Real.log (f x).toReal - Real.log (p0 x).toReal with hG
  have hP_fin : IsFiniteMeasure P := by
    rw [hP]
    exact MeasureTheory.isFiniteMeasure_withDensity (by rw [hp0_int]; exact ENNReal.one_ne_top)
  have hQ_fin : IsFiniteMeasure Q := by
    rw [hQ]
    exact MeasureTheory.isFiniteMeasure_withDensity (ne_top_of_le_ne_top ENNReal.one_ne_top hf_int)
  haveI := hP_fin
  haveI := hQ_fin
  have hc : P ≪ Q ∧ MeasureTheory.Integrable (MeasureTheory.llr P Q) P := by
    by_contra h
    exact hkl (by rw [InformationTheory.klDiv_def, if_neg h])
  have hPQ : P ≪ Q := hc.1
  have hllr_int : MeasureTheory.Integrable (MeasureTheory.llr P Q) P := hc.2
  have hkl_eq : InformationTheory.klDiv P Q
      = ENNReal.ofReal (∫ x, MeasureTheory.llr P Q x ∂P + Q.real Set.univ
          - P.real Set.univ) := by
    rw [InformationTheory.klDiv_def, if_pos hc]
  have hP_set : ∀ (s : Set X), MeasurableSet s → P s = ∫⁻ x in s, p0 x ∂μ := by
    intro s hs
    have h := MeasureTheory.setLIntegral_withDensity_eq_lintegral_mul₀
      (μ := μ) (f := p0) (g := fun _ => (1 : ℝ≥0∞)) hp0_meas.aemeasurable
      aemeasurable_const hs
    rw [hP]
    simpa using h
  have hQ_set : ∀ (s : Set X), MeasurableSet s → Q s = ∫⁻ x in s, f x ∂μ := by
    intro s hs
    have h := MeasureTheory.setLIntegral_withDensity_eq_lintegral_mul₀
      (μ := μ) (f := f) (g := fun _ => (1 : ℝ≥0∞)) hf_meas.aemeasurable
      aemeasurable_const hs
    rw [hQ]
    simpa using h
  have hnull : ∀ (s : Set X), MeasurableSet s → μ s = 0 →
      ∀ (g : X → ℝ≥0∞), ∫⁻ x in s, g x ∂μ = 0 := by
    intro s hs hμs g
    rw [← MeasureTheory.lintegral_indicator hs]
    have hae : ∀ᵐ x ∂μ, x ∉ s := by
      rw [MeasureTheory.ae_iff]
      simpa using hμs
    have hzero : s.indicator g =ᶠ[ae μ] (0 : X → ℝ≥0∞) := by
      filter_upwards [hae] with x hx
      rw [Set.indicator_of_notMem (s := s) (f := g) hx]
      simp
    rw [MeasureTheory.lintegral_congr_ae hzero]
    simp
  have hset_zero : ∀ (g : X → ℝ≥0∞), Measurable g →
      ∫⁻ x in {x | g x = 0}, g x ∂μ = 0 := by
    intro g hg
    have hmeas : MeasurableSet {x | g x = 0} := hg (measurableSet_singleton 0)
    rw [← MeasureTheory.lintegral_indicator hmeas]
    have hzero : {x | g x = 0}.indicator g = (0 : X → ℝ≥0∞) := by
      funext x
      by_cases hx : x ∈ {x | g x = 0}
      · rw [Set.indicator_of_mem (s := {x | g x = 0}) (f := g) hx]
        exact hx
      · rw [Set.indicator_of_notMem (s := {x | g x = 0}) (f := g) hx]
        simp
    rw [hzero]
    simp
  have hf_zero_Q : Q {x | f x = 0} = 0 := by
    rw [hQ_set {x | f x = 0} (hf_meas (measurableSet_singleton 0))]
    exact hset_zero f hf_meas
  have hf_zero_P : P {x | f x = 0} = 0 := hPQ hf_zero_Q
  have hp0_zero_P : P {x | p0 x = 0} = 0 := by
    rw [hP_set {x | p0 x = 0} (hp0_meas (measurableSet_singleton 0))]
    exact hset_zero p0 hp0_meas
  have hf_ne_zero_P : ∀ᵐ x ∂P, f x ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simpa using hf_zero_P
  have hp0_ne_zero_P : ∀ᵐ x ∂P, p0 x ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simpa using hp0_zero_P
  have hf_top_null : μ {x | f x = ⊤} = 0 :=
    MeasureTheory.measure_eq_top_of_lintegral_ne_top hf_meas.aemeasurable
      (ne_top_of_le_ne_top ENNReal.one_ne_top hf_int)
  have hp0_top_null : μ {x | p0 x = ⊤} = 0 :=
    MeasureTheory.measure_eq_top_of_lintegral_ne_top hp0_meas.aemeasurable
      (by rw [hp0_int]; exact ENNReal.one_ne_top)
  have hf_ne_top_μ : ∀ᵐ x ∂μ, f x ≠ ⊤ := by
    rw [MeasureTheory.ae_iff]
    simpa using hf_top_null
  have hp0_ne_top_μ : ∀ᵐ x ∂μ, p0 x ≠ ⊤ := by
    rw [MeasureTheory.ae_iff]
    simpa using hp0_top_null
  have hf_top_P : P {x | f x = ⊤} = 0 := by
    rw [hP_set {x | f x = ⊤} (hf_meas (measurableSet_singleton ⊤))]
    exact hnull _ (hf_meas (measurableSet_singleton ⊤)) hf_top_null p0
  have hp0_top_P : P {x | p0 x = ⊤} = 0 := by
    rw [hP_set {x | p0 x = ⊤} (hp0_meas (measurableSet_singleton ⊤))]
    exact hnull _ (hp0_meas (measurableSet_singleton ⊤)) hp0_top_null p0
  have hf_ne_top_P : ∀ᵐ x ∂P, f x ≠ ⊤ := by
    rw [MeasureTheory.ae_iff]
    simpa using hf_top_P
  have hp0_ne_top_P : ∀ᵐ x ∂P, p0 x ≠ ⊤ := by
    rw [MeasureTheory.ae_iff]
    simpa using hp0_top_P
  have hp0_zero_imp : ∀ᵐ x ∂μ, f x = 0 → p0 x = 0 := by
    have hint : ∫⁻ x in {x | f x = 0}, p0 x ∂μ = 0 := by
      rw [← hP_set {x | f x = 0} (hf_meas (measurableSet_singleton 0))]
      exact hf_zero_P
    have hres : ∀ᵐ x ∂(μ.restrict {x | f x = 0}), p0 x = 0 :=
      (MeasureTheory.lintegral_eq_zero_iff' hp0_meas.aemeasurable).mp hint
    rw [MeasureTheory.ae_iff] at hres
    have hkey : (μ.restrict {x | f x = 0}) {x | p0 x ≠ 0}
        = μ ({x | p0 x ≠ 0} ∩ {x | f x = 0}) := by
      rw [Measure.restrict_apply]
      first
        | exact (hp0_meas (measurableSet_singleton 0)).compl
        | exact hf_meas (measurableSet_singleton 0)
    rw [MeasureTheory.ae_iff]
    have hset : {x | ¬ (f x = 0 → p0 x = 0)} = {x | p0 x ≠ 0} ∩ {x | f x = 0} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Classical.not_imp]
      exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
    rw [hset, ← hkey]
    exact hres
  have hmul : (fun x => f x * (p0 x / f x)) =ᶠ[ae μ] p0 := by
    filter_upwards [hf_ne_top_μ, hp0_zero_imp] with x hftop hz
    rw [ENNReal.div_eq_inv_mul]
    exact ENNReal.mul_inv_cancel_left' (fun h0 => hz h0)
      (fun htop => False.elim (absurd htop hftop))
  have hdens : Q.withDensity (p0 / f) = P := by
    have hmul₀ := MeasureTheory.withDensity_mul₀ (μ := μ) (f := f) (g := p0 / f)
      hf_meas.aemeasurable (hp0_meas.div hf_meas).aemeasurable
    rw [hQ, ← hmul₀, hP]
    exact MeasureTheory.withDensity_congr_ae hmul
  have hrn : (∂P/∂Q) =ᶠ[ae Q] (p0 / f) := by
    have h1 : Q.withDensity (∂P/∂Q) = Q.withDensity (p0 / f) := by
      rw [MeasureTheory.Measure.withDensity_rnDeriv_eq P Q hPQ, hdens]
    exact (MeasureTheory.withDensity_eq_iff_of_sigmaFinite
      (MeasureTheory.Measure.measurable_rnDeriv P Q).aemeasurable
      (hp0_meas.div hf_meas).aemeasurable).mp h1
  have hrnP : (∂P/∂Q) =ᶠ[ae P] (p0 / f) := Filter.Eventually.filter_mono hPQ.ae_le hrn
  have hllr : MeasureTheory.llr P Q =ᶠ[ae P] (fun x => -G x) := by
    filter_upwards [hrnP, hf_ne_top_P, hf_ne_zero_P, hp0_ne_top_P, hp0_ne_zero_P]
      with x hx hftop hf0 hptop hp00
    simp only [MeasureTheory.llr]
    have hpn : (p0 x).toReal ≠ 0 := (ENNReal.toReal_ne_zero).2 ⟨hp00, hptop⟩
    have hfn : (f x).toReal ≠ 0 := (ENNReal.toReal_ne_zero).2 ⟨hf0, hftop⟩
    rw [hx]
    have hval : (p0 / f) x = p0 x / f x := rfl
    rw [hval, ENNReal.toReal_div, Real.log_div hpn hfn]
    simp only [hG]
    ring
  have hllr_sum : ∫ x, MeasureTheory.llr P Q x ∂P = -∫ x, G x ∂P := by
    calc ∫ x, MeasureTheory.llr P Q x ∂P = ∫ x, -G x ∂P :=
          MeasureTheory.integral_congr_ae hllr
      _ = -∫ x, G x ∂P := MeasureTheory.integral_neg (f := G) (μ := P)
  have hIntG : MeasureTheory.Integrable G P := by
    have h1 : MeasureTheory.Integrable (fun x => -G x) P := hllr_int.congr hllr
    refine h1.neg.congr ?_
    filter_upwards with x
    simp
  have hP_univ : P Set.univ = 1 := by
    rw [hP_set Set.univ MeasurableSet.univ]
    simpa using hp0_int
  have hQ_univ : Q Set.univ = ∫⁻ x, f x ∂μ := by
    have h := hQ_set Set.univ MeasurableSet.univ
    simpa only [Measure.restrict_univ] using h
  have hPr : P.real Set.univ = 1 := by
    show (P Set.univ).toReal = 1
    rw [hP_univ]
    simp
  have hQ_real : Q.real Set.univ = (∫⁻ x, f x ∂μ).toReal := by
    show (Q Set.univ).toReal = (∫⁻ x, f x ∂μ).toReal
    rw [hQ_univ]
  have hK_eq : (InformationTheory.klDiv P Q).toReal
      = max (-(∫ x, G x ∂P) + Q.real Set.univ - P.real Set.univ) 0 := by
    rw [hkl_eq, ENNReal.toReal_ofReal', hllr_sum]
  have hK_le : -(∫ x, G x ∂P) + Q.real Set.univ - P.real Set.univ
      ≤ (InformationTheory.klDiv P Q).toReal := by
    rw [hK_eq]
    exact le_max_left _ _
  have hconj2 : -(InformationTheory.klDiv P Q).toReal
      ≤ ∫ x, G x ∂P + (P.real Set.univ - Q.real Set.univ) := by
    linarith
  have hInt_neg : MeasureTheory.Integrable (fun x => max (-(G x)) 0) P :=
    MeasureTheory.Integrable.neg_part hIntG
  have hInt_pos : MeasureTheory.Integrable (fun x => max (G x) 0) P :=
    MeasureTheory.Integrable.pos_part hIntG
  have hGfun : (fun x : X => G x) = fun x => max (G x) 0 - max (-(G x)) 0 := by
    funext x
    rcases le_total (G x) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith : (0:ℝ) ≤ -(G x))]
      ring
    · rw [max_eq_left h, max_eq_right (by linarith : -(G x) ≤ 0)]
      ring
  have hs : ∫ x, G x ∂P = (∫ x, max (G x) 0 ∂P) - ∫ x, max (-(G x)) 0 ∂P := by
    rw [hGfun, MeasureTheory.integral_sub hInt_pos hInt_neg]
  have hpt : ∀ᵐ x ∂μ, p0 x * ENNReal.ofReal (max (G x) 0) ≤ f x := by
    filter_upwards [hp0_ne_top_μ, hf_ne_top_μ, hp0_zero_imp] with x hp0top hftop hz
    by_cases hp0z : p0 x = 0
    · rw [hp0z, zero_mul]
      exact zero_le _
    by_cases hfz : f x = 0
    · exact False.elim (absurd (hz hfz) hp0z)
    have hp0ne : (p0 x).toReal ≠ 0 := (ENNReal.toReal_ne_zero).2 ⟨hp0z, hp0top⟩
    have hfne : (f x).toReal ≠ 0 := (ENNReal.toReal_ne_zero).2 ⟨hfz, hftop⟩
    have hp0pos : (0:ℝ) < (p0 x).toReal := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hp0ne)
    have hfpos : (0:ℝ) < (f x).toReal := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hfne)
    have hGx : G x = Real.log ((f x).toReal / (p0 x).toReal) := by
      simp only [hG]
      exact (Real.log_div (ne_of_gt hfpos) (ne_of_gt hp0pos)).symm
    have hpos : 0 < (f x).toReal / (p0 x).toReal := div_pos hfpos hp0pos
    have hmax : max (G x) 0 ≤ (f x).toReal / (p0 x).toReal := by
      rw [hGx]
      refine max_le ?_ (le_of_lt hpos)
      have hlog := Real.log_le_sub_one_of_pos hpos
      linarith
    have hEq1 : p0 x * ENNReal.ofReal (max (G x) 0)
        = ENNReal.ofReal ((p0 x).toReal * max (G x) 0) := by
      rw [ENNReal.ofReal_mul (le_of_lt hp0pos), ENNReal.ofReal_toReal hp0top]
    rw [hEq1, ← ENNReal.ofReal_toReal hftop]
    apply ENNReal.ofReal_le_ofReal
    calc (p0 x).toReal * max (G x) 0
        ≤ (p0 x).toReal * ((f x).toReal / (p0 x).toReal) :=
          mul_le_mul_of_nonneg_left hmax (le_of_lt hp0pos)
      _ = (f x).toReal := by field_simp
  have hf_ne_top_lintegral : ∫⁻ x, f x ∂μ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hf_int
  have hP_lt_top_μ : ∀ᵐ x ∂μ, p0 x < ⊤ := by
    filter_upwards [hp0_ne_top_μ] with x hx
    exact lt_top_iff_ne_top.2 hx
  have hle_lintegral : ∫⁻ x, ENNReal.ofReal (max (G x) 0) ∂P ≤ ∫⁻ x, f x ∂μ := by
    have heq : ∫⁻ x, ENNReal.ofReal (max (G x) 0) ∂P
        = ∫⁻ x, p0 x * ENNReal.ofReal (max (G x) 0) ∂μ := by
      rw [hP]
      exact MeasureTheory.lintegral_withDensity_eq_lintegral_mul_non_measurable μ hp0_meas
        hP_lt_top_μ (fun x => ENNReal.ofReal (max (G x) 0))
    rw [heq]
    exact MeasureTheory.lintegral_mono_ae hpt
  have hpQ : ∫ x, max (G x) 0 ∂P ≤ Q.real Set.univ := by
    have h1 : (∫⁻ x, ENNReal.ofReal (max (G x) 0) ∂P).toReal = ∫ x, max (G x) 0 ∂P :=
      Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.lintegral_toReal_eq_integral_of_nonneg
        (f := fun x => max (G x) 0)
        (Filter.Eventually.of_forall (fun x => le_max_right (G x) 0)) hInt_pos
    rw [← h1]
    calc (∫⁻ x, ENNReal.ofReal (max (G x) 0) ∂P).toReal
        ≤ (∫⁻ x, f x ∂μ).toReal := ENNReal.toReal_mono hf_ne_top_lintegral hle_lintegral
      _ = Q.real Set.univ := hQ_real.symm
  have hA_eq : (∫⁻ x, ENNReal.ofReal (max (-(G x)) 0) ∂P)
      = ENNReal.ofReal (∫ x, max (-(G x)) 0 ∂P) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt_neg
      (Filter.Eventually.of_forall (fun x => le_max_right (-(G x)) 0))).symm
  have hconj3 : (∫⁻ x, ENNReal.ofReal (max (-(G x)) 0) ∂P)
      ≤ ENNReal.ofReal ((InformationTheory.klDiv P Q).toReal + 1) := by
    rw [hA_eq]
    apply ENNReal.ofReal_le_ofReal
    linarith
  exact ⟨hIntG, hconj2, hconj3⟩
  /- @proof-region region.target-node.session.fc5d945887d094e7 end -/

end Statlib.Imported
