import Mathlib
import Mathlib
import Statlib.StatFoundation.BasicAnalysis.ENNRealBridge
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal MeasureTheory Topology BigOperators
noncomputable section
namespace OfflineDPEvidence
-- Generic KL-evidence proofs adapted from the verified sibling primitives.
-- No model Base, raw function-space prior, or new evidence premise is imported.
set_option autoImplicit false in
theorem statopia_math_node_2110233091_1dad31d5 : ∀ {X H : Type*} [MeasurableSpace X] [MeasurableSpace H]
    (P : Measure X) [IsProbabilityMeasure P]
    (nu : Measure H) [IsProbabilityMeasure nu]
    (g : H → X → ℝ) (hg : Measurable (Function.uncurry g))
    (h_neg_fin : ∀ᵐ x ∂P, ∫⁻ h, ENNReal.ofReal (max (-(g h x)) 0) ∂nu < ⊤)
    (h_pos_fin : ∀ᵐ x ∂P, ∫⁻ h, ENNReal.ofReal (max (g h x) 0) ∂nu < ⊤),
    ∀ᵐ x ∂(Measure.infinitePi (fun _ : ℕ => P)), ∀ n : ℕ,
      ENNReal.ofReal (Real.exp (∑ i ∈ Finset.range n, ∫ h, g h (x i) ∂nu))
        ≤ ∫⁻ h, ENNReal.ofReal (Real.exp (∑ i ∈ Finset.range n, g h (x i))) ∂nu := by
  /- @proof-region region.target-node.session.4caf69986dd6391c begin -/
  intro X H _ _ P _ ν _ g hg hNegFin hPosFin
  have hIntgAE : ∀ᵐ x ∂(Measure.infinitePi (fun _ : ℕ => P)), ∀ i : ℕ, Integrable (fun h => g h (x i)) ν := by
    have hsecMeas : ∀ y : X, Measurable (fun h => g h y) := fun y =>
      hg.comp (measurable_id.prod measurable_const : Measurable (fun h : H => (h, y)))
    have hPcombo : ∀ᵐ y ∂P,
        (∫⁻ h, ENNReal.ofReal (max (-(g h y)) 0) ∂ν < ⊤) ∧
        (∫⁻ h, ENNReal.ofReal (max (g h y) 0) ∂ν < ⊤) := hNegFin.and hPosFin
    have hcoordinate : ∀ i : ℕ, ∀ᵐ x ∂(Measure.infinitePi (fun _ : ℕ => P)),
        (∫⁻ h, ENNReal.ofReal (max (-(g h (x i))) 0) ∂ν < ⊤) ∧
        (∫⁻ h, ENNReal.ofReal (max (g h (x i)) 0) ∂ν < ⊤) := by
      intro i
      have h := (measurePreserving_eval_infinitePi (fun _ : ℕ => P) i).quasiMeasurePreserving.ae hPcombo
      simpa only [Function.eval] using h
    rw [MeasureTheory.ae_all_iff]
    intro i
    filter_upwards [hcoordinate i] with x hx
    obtain ⟨hneg, hpos⟩ := hx
    have hposMeas : AEStronglyMeasurable (fun h => max (g h (x i)) 0) ν :=
      ((hsecMeas (x i)).max (measurable_const : Measurable fun _ : H => (0 : ℝ))).aestronglyMeasurable
    have hnegMeas : AEStronglyMeasurable (fun h => max (-(g h (x i))) 0) ν :=
      (((hsecMeas (x i)).neg).max (measurable_const : Measurable fun _ : H => (0 : ℝ))).aestronglyMeasurable
    have hposInt : Integrable (fun h => max (g h (x i)) 0) ν :=
      (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hposMeas
        (Filter.Eventually.of_forall (fun h => le_max_right (g h (x i)) 0))).mp (ne_of_lt hpos)
    have hnegInt : Integrable (fun h => max (-(g h (x i))) 0) ν :=
      (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hnegMeas
        (Filter.Eventually.of_forall (fun h => le_max_right (-(g h (x i))) 0))).mp (ne_of_lt hneg)
    have hfun : (fun h => max (g h (x i)) 0 - max (-(g h (x i))) 0) = fun h => g h (x i) := by
      funext h
      by_cases hle : g h (x i) ≤ 0
      · rw [max_eq_right hle, max_eq_left (by linarith), zero_sub, neg_neg]
      · rw [max_eq_left (by linarith), max_eq_right (by linarith), sub_zero]
    rw [← hfun]
    exact hposInt.sub hnegInt
  filter_upwards [hIntgAE] with x hx
  intro n
  have hSecMeas : ∀ i : ℕ, Measurable (fun h => g h (x i)) := fun i =>
    hg.comp (measurable_id.prod measurable_const : Measurable (fun h : H => (h, x i)))
  have hSMeas : Measurable (fun h => ∑ i ∈ Finset.range n, g h (x i)) :=
    Finset.measurable_sum (Finset.range n) (fun i _ => hSecMeas i)
  have hIntgS : Integrable (fun h => ∑ i ∈ Finset.range n, g h (x i)) ν :=
    MeasureTheory.integrable_finset_sum (s := Finset.range n) (fun i _ => hx i)
  have hIntS : ∫ h, (∑ i ∈ Finset.range n, g h (x i)) ∂ν
      = ∑ i ∈ Finset.range n, ∫ h, g h (x i) ∂ν :=
    integral_finset_sum (Finset.range n) (fun i _ => hx i)
  by_cases hfin : ∫⁻ h, ENNReal.ofReal (Real.exp (∑ i ∈ Finset.range n, g h (x i))) ∂ν = ⊤
  · rw [hfin]
    exact le_top
  · have hpos : 0 ≤ᶠ[ae ν] (fun h => Real.exp (∑ i ∈ Finset.range n, g h (x i))) :=
      Filter.Eventually.of_forall (fun h => (Real.exp_pos _).le)
    have hExpAES : AEStronglyMeasurable (fun h => Real.exp (∑ i ∈ Finset.range n, g h (x i))) ν :=
      (Real.measurable_exp.comp hSMeas).aestronglyMeasurable
    have hexpIntg : Integrable (fun h => Real.exp (∑ i ∈ Finset.range n, g h (x i))) ν :=
      (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hExpAES hpos).mp hfin
    have hjensen : Real.exp (∫ h, (∑ i ∈ Finset.range n, g h (x i)) ∂ν)
        ≤ ∫ h, Real.exp (∑ i ∈ Finset.range n, g h (x i)) ∂ν :=
      ConvexOn.map_integral_le convexOn_exp Real.continuous_exp.continuousOn isClosed_univ
        (Filter.Eventually.of_forall (fun _ => Set.mem_univ _)) hIntgS hexpIntg
    rw [hIntS] at hjensen
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hexpIntg hpos]
    exact ENNReal.ofReal_le_ofReal hjensen

  /- @proof-region region.target-node.session.4caf69986dd6391c end -/


set_option autoImplicit false in
theorem statopia_math_node_2642199537_30588a87 : ∀ {X H : Type*} [MeasurableSpace X] [MeasurableSpace H]
    (P : Measure X) [IsProbabilityMeasure P] (ν : Measure H) [IsProbabilityMeasure ν]
    (g : H → X → ℝ) (hg : Measurable (Function.uncurry g)) (delta1 : ℝ)
    (h_int : ∀ᵐ h ∂ν, MeasureTheory.Integrable (g h) P)
    (h_lower : ∀ᵐ h ∂ν, -delta1 ≤ ∫ x, g h x ∂P)
    (h_pos_bound : ∀ᵐ h ∂ν, ∫⁻ x, ENNReal.ofReal (max (g h x) 0) ∂P ≤ (1 : ℝ≥0∞))
    (h_neg_bound : ∀ᵐ h ∂ν,
      ∫⁻ x, ENNReal.ofReal (max (-(g h x)) 0) ∂P ≤ ENNReal.ofReal (delta1 + 1)),
    Measurable (fun x => ∫ h, g h x ∂ν) ∧
      MeasureTheory.Integrable (fun x => ∫ h, g h x ∂ν) P ∧
      -delta1 ≤ ∫ x, (∫ h, g h x ∂ν) ∂P := by
  /- @proof-region region.target-node.session.cc7ebc352c403d91 begin -/
  intro X H _ _ P _ ν _ g hg delta1 h_int h_lower h_pos_bound h_neg_bound
  have hFm : Measurable (fun p : X × H => g p.2 p.1) := hg.comp measurable_swap
  have hbar_meas : Measurable (fun x => ∫ h, g h x ∂ν) :=
    (MeasureTheory.StronglyMeasurable.integral_prod_right' (ν := ν) hFm.stronglyMeasurable).measurable
  have hnice : ∀ h : H, Measurable (fun x => g h x) := fun h =>
    hg.comp (measurable_prodMk_left (x := h))
  have hkey : ∀ (h : H) (x : X),
      ‖g h x‖ₑ = ENNReal.ofReal (max (g h x) 0) + ENNReal.ofReal (max (-(g h x)) 0) := by
    intro h x
    classical
    rw [Real.enorm_eq_ofReal_abs,
      ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)]
    congr 1
    by_cases hx : (0 : ℝ) ≤ g h x
    · rw [abs_of_nonneg hx, max_eq_left hx, max_eq_right (by linarith : -(g h x) ≤ 0)]
      ring
    · rw [not_le] at hx
      rw [abs_of_neg hx, max_eq_right hx.le,
        max_eq_left (by linarith : (0 : ℝ) ≤ -(g h x))]
      ring
  have hkernel : ∀ h : H,
      ∫⁻ x, ‖g h x‖ₑ ∂P
        ≤ (∫⁻ x, ENNReal.ofReal (max (g h x) 0) ∂P)
          + ∫⁻ x, ENNReal.ofReal (max (-(g h x)) 0) ∂P := by
    intro h
    calc ∫⁻ x, ‖g h x‖ₑ ∂P
        = ∫⁻ x, (ENNReal.ofReal (max (g h x) 0)
            + ENNReal.ofReal (max (-(g h x)) 0)) ∂P := by
          simp only [hkey]
      _ ≤ (∫⁻ x, ENNReal.ofReal (max (g h x) 0) ∂P)
            + ∫⁻ x, ENNReal.ofReal (max (-(g h x)) 0) ∂P :=
          le_of_eq (MeasureTheory.lintegral_add_left
            (f := fun x => ENNReal.ofReal (max (g h x) 0))
            (g := fun x => ENNReal.ofReal (max (-(g h x)) 0))
            (by measurability))
  have h3 : ∀ᵐ h ∂ν, ∫⁻ x, ‖g h x‖ₑ ∂P ≤ 1 + ENNReal.ofReal (delta1 + 1) := by
    filter_upwards [h_pos_bound, h_neg_bound] with h hp hn
    exact le_trans (hkernel h) (add_le_add hp hn)
  have hIntF : MeasureTheory.Integrable (fun p : X × H => g p.2 p.1) (P.prod ν) := by
    have hgu : Measurable (fun z : H × X => g z.1 z.2) := hg
    have hKmf : Measurable (fun z : H × X => ‖g z.1 z.2‖ₑ) := by measurability
    have hb : ∫⁻ z : H × X, ‖g z.1 z.2‖ₑ ∂(ν.prod P)
        ≤ 1 + ENNReal.ofReal (delta1 + 1) := by
      rw [MeasureTheory.lintegral_prod (f := fun z : H × X => ‖g z.1 z.2‖ₑ)
        hKmf.aemeasurable]
      calc ∫⁻ h, ∫⁻ x, ‖g h x‖ₑ ∂P ∂ν
          ≤ ∫⁻ _h, (1 + ENNReal.ofReal (delta1 + 1)) ∂ν :=
            MeasureTheory.lintegral_mono_ae h3
        _ = 1 + ENNReal.ofReal (delta1 + 1) := by simp
    have hswap : ∫⁻ p : X × H, ‖g p.2 p.1‖ₑ ∂(P.prod ν)
        = ∫⁻ z : H × X, ‖g z.1 z.2‖ₑ ∂(ν.prod P) :=
      (MeasureTheory.lintegral_prod_swap (f := fun p : X × H => ‖g p.2 p.1‖ₑ)).symm
    have hC : (1 + ENNReal.ofReal (delta1 + 1)) < ⊤ := by simp
    have hFfi : MeasureTheory.HasFiniteIntegral (fun p : X × H => g p.2 p.1) (P.prod ν) := by
      show ∫⁻ p : X × H, ‖g p.2 p.1‖ₑ ∂(P.prod ν) < ⊤
      rw [hswap]
      exact lt_of_le_of_lt hb hC
    exact ⟨hFm.aestronglyMeasurable, hFfi⟩
  refine ⟨hbar_meas, ?_, ?_⟩
  · exact MeasureTheory.Integrable.integral_prod_left
      (f := fun p : X × H => g p.2 p.1) hIntF
  · have hintH : MeasureTheory.Integrable (fun h => ∫ x, g h x ∂P) ν :=
      MeasureTheory.Integrable.integral_prod_right
        (f := fun p : X × H => g p.2 p.1) hIntF
    have hswapint : ∫ x, (∫ h, g h x ∂ν) ∂P = ∫ h, (∫ x, g h x ∂P) ∂ν :=
      MeasureTheory.integral_integral_swap (f := fun x h => g h x) hIntF
    have hconst : MeasureTheory.Integrable (fun _ : H => -delta1) ν :=
      MeasureTheory.integrable_const (-delta1)
    have hmono : ∫ _h : H, -delta1 ∂ν ≤ ∫ h, (∫ x, g h x ∂P) ∂ν :=
      MeasureTheory.integral_mono_ae hconst hintH h_lower
    have hc : ∫ _h : H, -delta1 ∂ν = -delta1 := by simp
    calc -delta1 = ∫ _h : H, -delta1 ∂ν := hc.symm
      _ ≤ ∫ h, (∫ x, g h x ∂P) ∂ν := hmono
      _ = ∫ x, (∫ h, g h x ∂ν) ∂P := hswapint.symm
  /- @proof-region region.target-node.session.cc7ebc352c403d91 end -/


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


set_option autoImplicit false in
theorem statopia_math_node_3155168291_3ca337d1 : ∀ {X H : Type*} [MeasurableSpace X] [MeasurableSpace H]
    (μ : Measure X) [SigmaFinite μ]
    (p0 : X → ℝ≥0∞) (hp0 : Measurable p0)
    (hp0_int : ∫⁻ x, p0 x ∂μ = 1)
    (dens : H → X → ℝ≥0∞) (hdens : Measurable (Function.uncurry dens))
    (hdens_lt_top : ∀ h : H, ∀ᵐ x ∂μ, dens h x ≠ ⊤)
    (ε : ℝ),
    MeasurableSet {h : H |
      InformationTheory.klDiv (μ.withDensity p0) (μ.withDensity (dens h))
        < ENNReal.ofReal ε} := by
  /- @proof-region region.target-node.session.e583fcdf3097f3b5 begin -/
  intro X H _ _ μ _ p0 hp0 hp0_int dens hdens hdens_lt_top ε
  have hFmeas : Measurable (fun h : H =>
      InformationTheory.klDiv (μ.withDensity p0) (μ.withDensity (dens h))) := by
    have key : ∀ h : H, InformationTheory.klDiv (μ.withDensity p0) (μ.withDensity (dens h)) =
        if (∫⁻ x, p0 x * ({y | dens h y = 0}).indicator (fun _ => 1) x ∂μ = 0 ∧
            ∫⁻ x, ENNReal.ofReal ‖Real.log ((p0 x * (dens h x)⁻¹).toReal)‖
              ∂(μ.withDensity p0) ≠ ⊤)
          then ENNReal.ofReal ((∫⁻ x, ENNReal.ofReal (Real.log ((p0 x * (dens h x)⁻¹).toReal))
                ∂(μ.withDensity p0)).toReal
              - (∫⁻ x, ENNReal.ofReal (-(Real.log ((p0 x * (dens h x)⁻¹).toReal)))
                ∂(μ.withDensity p0)).toReal
              + (∫⁻ x, dens h x ∂μ).toReal - 1)
          else ⊤ := by
      intro h
      set f : X → ℝ≥0∞ := dens h with hf
      set P : Measure X := μ.withDensity p0 with hP
      set Q : Measure X := μ.withDensity f with hQ
      set g : X → ℝ := fun x => Real.log ((p0 x * (f x)⁻¹).toReal) with hg
      have hfmeas : Measurable f := by
        have hpair : Measurable (fun x : X => (h, x)) :=
          Measurable.prod (f := fun x : X => (h, x)) measurable_const measurable_id
        exact hdens.comp hpair
      have hgm : Measurable g := by
        have h1 : Measurable (fun x : X => (f x)⁻¹) := hfmeas.inv
        have h2 : Measurable (fun x : X => p0 x * (f x)⁻¹) := hp0.mul h1
        exact Real.measurable_log.comp (ENNReal.measurable_toReal.comp h2)
      have hPuniv : P Set.univ = 1 := by
        rw [← MeasureTheory.lintegral_one (μ := P), hP,
          MeasureTheory.lintegral_withDensity_eq_lintegral_mul₀ hp0.aemeasurable
            aemeasurable_const]
        simpa using hp0_int
      have hQuniv : Q Set.univ = ∫⁻ x, f x ∂μ := by
        rw [← MeasureTheory.lintegral_one (μ := Q), hQ,
          MeasureTheory.lintegral_withDensity_eq_lintegral_mul₀ hfmeas.aemeasurable
            aemeasurable_const]
        simp
      have hPreal : P.real Set.univ = 1 := by
        show (P Set.univ).toReal = 1
        rw [hPuniv]
        simp
      have hQreal : Q.real Set.univ = (∫⁻ x, f x ∂μ).toReal := by
        show (Q Set.univ).toReal = (∫⁻ x, f x ∂μ).toReal
        rw [hQuniv]
      have hac : P ≪ Q ↔ ∫⁻ x, p0 x * ({y | f y = 0}).indicator (fun _ => 1) x ∂μ = 0 := by
        set s : Set X := {y : X | f y = 0} with hsdef
        have hs : MeasurableSet s := by
          rw [hsdef]
          exact hfmeas (measurableSet_singleton 0)
        have hind : Measurable (s.indicator (fun _ => (1 : ℝ≥0∞))) :=
          Measurable.indicator measurable_const hs
        have hindp : Measurable (s.indicator (fun x => p0 x)) :=
          Measurable.indicator hp0 hs
        have hPs : P s = ∫⁻ x, p0 x * s.indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ := by
          have h1 : ∫⁻ x, s.indicator (fun _ => (1 : ℝ≥0∞)) x ∂P = P s :=
            MeasureTheory.lintegral_indicator_one₀ hs.nullMeasurableSet
          have h2 : ∫⁻ x, s.indicator (fun _ => (1 : ℝ≥0∞)) x ∂P
              = ∫⁻ x, p0 x * s.indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ := by
            rw [hP, MeasureTheory.lintegral_withDensity_eq_lintegral_mul₀ hp0.aemeasurable
              hind.aemeasurable]
            rfl
          rw [← h1, h2]
        have hQs : Q s = 0 := by
          have h1 : ∫⁻ x, s.indicator (fun _ => (1 : ℝ≥0∞)) x ∂Q = Q s :=
            MeasureTheory.lintegral_indicator_one₀ hs.nullMeasurableSet
          have h2 : ∫⁻ x, s.indicator (fun _ => (1 : ℝ≥0∞)) x ∂Q
              = ∫⁻ x, f x * s.indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ := by
            rw [hQ, MeasureTheory.lintegral_withDensity_eq_lintegral_mul₀ hfmeas.aemeasurable
              hind.aemeasurable]
            rfl
          have hpt0 : ∀ x : X, f x * s.indicator (fun _ => (1 : ℝ≥0∞)) x = 0 := by
            intro x
            by_cases hx : f x = 0
            · have hxs : x ∈ s := by rw [hsdef]; exact hx
              rw [Set.indicator_of_mem hxs, mul_one, hx]
            · have hxs : x ∉ s := by rw [hsdef]; simpa using hx
              rw [Set.indicator_of_notMem hxs, mul_zero]
          have h3 : (∫⁻ x, f x * s.indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ) = 0 := by
            rw [MeasureTheory.lintegral_congr hpt0]
            simp
          rw [← h1, h2, h3]
        constructor
        · intro hPQ
          rw [← hPs]
          have h1 : ∫⁻ x, s.indicator (fun _ => (1 : ℝ≥0∞)) x ∂Q = 0 :=
            (MeasureTheory.lintegral_indicator_one₀ hs.nullMeasurableSet).trans hQs
          have h2 : s.indicator (fun _ => (1 : ℝ≥0∞)) =ᵐ[Q] 0 :=
            (MeasureTheory.lintegral_eq_zero_iff hind).mp h1
          have h3 : s.indicator (fun _ => (1 : ℝ≥0∞)) =ᵐ[P] 0 :=
            MeasureTheory.Measure.AbsolutelyContinuous.ae_eq hPQ h2
          have h4 : ∫⁻ x, s.indicator (fun _ => (1 : ℝ≥0∞)) x ∂P = 0 := by
            rw [MeasureTheory.lintegral_congr_ae h3]
            simp
          exact (MeasureTheory.lintegral_indicator_one₀ hs.nullMeasurableSet).symm.trans h4
        · intro hA0
          have hzero : s.indicator (fun x => p0 x) =ᵐ[μ] 0 := by
            apply (MeasureTheory.lintegral_eq_zero_iff hindp).mp
            have hconv : ∫⁻ a, s.indicator (fun x => p0 x) a ∂μ
                = ∫⁻ x, p0 x * s.indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ :=
              MeasureTheory.lintegral_congr fun x => by
                by_cases hx : f x = 0
                · have hxs : x ∈ s := by rw [hsdef]; exact hx
                  rw [Set.indicator_of_mem hxs, Set.indicator_of_mem hxs, mul_one]
                · have hxs : x ∉ s := by rw [hsdef]; simpa using hx
                  rw [Set.indicator_of_notMem hxs, Set.indicator_of_notMem hxs, mul_zero]
            rw [hconv, hA0]
          have hpt : ∀ᵐ x ∂μ, f x = 0 → p0 x = 0 := by
            filter_upwards [hzero] with x hx hfx
            have hxs : x ∈ s := by rw [hsdef]; exact hfx
            have h2 : s.indicator (fun x => p0 x) x = p0 x :=
              Set.indicator_of_mem hxs (fun x => p0 x)
            rw [h2] at hx
            exact hx
          have hident : f * (fun x => p0 x * (f x)⁻¹) =ᵐ[μ] p0 := by
            filter_upwards [hdens_lt_top h, hpt] with x htop hx0
            by_cases hfx : f x = 0
            · rw [Pi.mul_apply, hfx, zero_mul, hx0 hfx]
            · rw [Pi.mul_apply, ← mul_assoc, mul_comm (f x) (p0 x), mul_assoc,
                ENNReal.mul_inv_cancel hfx htop, mul_one]
          have hquot : Measurable (fun x : X => p0 x * (f x)⁻¹) := hp0.mul hfmeas.inv
          have hPeq : P = Q.withDensity (fun x => p0 x * (f x)⁻¹) := by
            rw [hP, MeasureTheory.withDensity_congr_ae hident.symm,
              MeasureTheory.withDensity_mul μ hfmeas hquot, hQ]
          haveI hQfin : SigmaFinite Q :=
            MeasureTheory.SigmaFinite.withDensity_of_ne_top (hdens_lt_top h)
          have hrn : (fun x => Measure.rnDeriv (Q.withDensity (fun y => p0 y * (f y)⁻¹)) Q x)
              =ᵐ[Q] (fun x => p0 x * (f x)⁻¹) := Measure.rnDeriv_withDensity Q hquot
          have hac2 : Q.withDensity (fun x => p0 x * (f x)⁻¹) ≪ Q := by
            refine MeasureTheory.Measure.absolutelyContinuous_iff_withDensity_rnDeriv_eq.mpr ?_
            exact MeasureTheory.withDensity_congr_ae hrn
          rw [hPeq]
          exact hac2
      have hllr : (∫⁻ x, p0 x * ({y | f y = 0}).indicator (fun _ => 1) x ∂μ = 0) →
          llr P Q =ᵐ[P] g := by
        intro hA0
        have hf0 : MeasurableSet {y : X | f y = 0} := hfmeas (measurableSet_singleton 0)
        have hind : Measurable ({y : X | f y = 0}.indicator (fun _ => (1 : ℝ≥0∞))) :=
          Measurable.indicator measurable_const hf0
        have hPs0 : P {y : X | f y = 0} = 0 := by
          have h1 : ∫⁻ x, ({y : X | f y = 0}).indicator (fun _ => (1 : ℝ≥0∞)) x ∂P
              = P {y : X | f y = 0} :=
            MeasureTheory.lintegral_indicator_one₀ hf0.nullMeasurableSet
          rw [← h1, hP, MeasureTheory.lintegral_withDensity_eq_lintegral_mul₀ hp0.aemeasurable
            hind.aemeasurable]
          exact hA0
        have hPQ : P ≪ Q := hac.mpr hA0
        haveI hPfin : IsFiniteMeasure P := ⟨by rw [hPuniv]; exact ENNReal.one_lt_top⟩
        haveI hQsig : SigmaFinite Q :=
          MeasureTheory.SigmaFinite.withDensity_of_ne_top (hdens_lt_top h)
        have h1 : (fun x => Measure.rnDeriv P μ x) =ᵐ[μ] p0 := Measure.rnDeriv_withDensity μ hp0
        have h2 : (fun x => Measure.rnDeriv Q μ x) =ᵐ[μ] f := Measure.rnDeriv_withDensity μ hfmeas
        have hPmu : P ≪ μ := by
          refine MeasureTheory.Measure.absolutelyContinuous_iff_withDensity_rnDeriv_eq.mpr ?_
          rw [MeasureTheory.withDensity_congr_ae h1, hP]
        have hc : (fun x => Measure.rnDeriv P Q x * Measure.rnDeriv Q μ x)
            =ᵐ[μ] (fun x => Measure.rnDeriv P μ x) := Measure.rnDeriv_mul_rnDeriv hPQ
        have h4 : (fun x => Measure.rnDeriv P Q x * f x) =ᵐ[μ] p0 := by
          filter_upwards [hc, h2, h1] with x hx hx2 hx1
          rw [hx2, hx1] at hx
          exact hx
        have hind0 : ({y : X | f y = 0}).indicator (fun _ => (1 : ℝ≥0∞)) =ᵐ[P] 0 := by
          apply (MeasureTheory.lintegral_eq_zero_iff hind).mp
          exact (MeasureTheory.lintegral_indicator_one₀ hf0.nullMeasurableSet).trans hPs0
        have hPf0 : ∀ᵐ x ∂P, f x ≠ 0 := by
          filter_upwards [hind0] with x hx
          intro h
          have hmem : x ∈ {y : X | f y = 0} := h
          rw [Set.indicator_of_mem hmem] at hx
          simpa using hx
        have hPf_top : ∀ᵐ x ∂P, f x ≠ ⊤ := by
          have hind1 : (fun x : X => if f x = ⊤ then (0 : ℝ≥0∞) else 1) =ᵐ[μ]
              (fun _ => (1 : ℝ≥0∞)) := by
            filter_upwards [hdens_lt_top h] with x hx
            have hx' : f x ≠ ⊤ := hx
            simp [hx']
          have hind1P : (fun x : X => if f x = ⊤ then (0 : ℝ≥0∞) else 1) =ᵐ[P]
              (fun _ => (1 : ℝ≥0∞)) :=
            MeasureTheory.Measure.AbsolutelyContinuous.ae_eq hPmu hind1
          filter_upwards [hind1P] with x hx
          intro htop
          rw [htop] at hx
          simpa using hx
        have h5 : (fun x => Measure.rnDeriv P Q x * f x) =ᵐ[P] p0 :=
          MeasureTheory.Measure.AbsolutelyContinuous.ae_eq hPmu h4
        have h6 : (fun x => Measure.rnDeriv P Q x) =ᵐ[P] (fun x => p0 x * (f x)⁻¹) := by
          filter_upwards [h5, hPf0, hPf_top] with x hx hx0 hxtop
          have hmul : Measure.rnDeriv P Q x * f x = p0 x := hx
          rw [← hmul, mul_assoc, ENNReal.mul_inv_cancel hx0 hxtop, mul_one]
        rw [MeasureTheory.llr_def]
        filter_upwards [h6] with x hx
        rw [hx]
      have hInt : (∫⁻ x, p0 x * ({y | f y = 0}).indicator (fun _ => 1) x ∂μ = 0) →
          (Integrable (llr P Q) P ↔ ∫⁻ x, ENNReal.ofReal ‖g x‖ ∂P ≠ ⊤) := by
        intro hA0
        have hllr' : llr P Q =ᵐ[P] g := hllr hA0
        have h1 : Integrable (llr P Q) P ↔ Integrable g P :=
          ⟨fun hh => hh.congr hllr', fun hh => hh.congr hllr'.symm⟩
        rw [h1]
        have hbridge : (∫⁻ x, enorm (g x) ∂P) = ∫⁻ x, ENNReal.ofReal ‖g x‖ ∂P :=
          lintegral_congr fun x => Real.enorm_eq_ofReal_abs (g x)
        rw [← hbridge]
        constructor
        · intro hh
          exact ne_of_lt hh.2
        · intro hh
          exact ⟨hgm.aestronglyMeasurable, lt_top_iff_ne_top.mpr hh⟩
      rw [InformationTheory.klDiv_def]
      by_cases hA : ∫⁻ x, p0 x * ({y | f y = 0}).indicator (fun _ => 1) x ∂μ = 0
      · by_cases hB : ∫⁻ x, ENNReal.ofReal ‖g x‖ ∂P = ⊤
        · rw [if_neg (fun hh : P ≪ Q ∧ Integrable (llr P Q) P => (hInt hA).mp hh.2 hB),
            if_neg (fun hh : (∫⁻ x, p0 x * ({y | f y = 0}).indicator (fun _ => 1) x ∂μ = 0) ∧
              ∫⁻ x, ENNReal.ofReal ‖g x‖ ∂P ≠ ⊤ => hh.2 hB)]
        · have hI : Integrable (llr P Q) P := (hInt hA).mpr hB
          have hIg : Integrable g P := hI.congr (hllr hA)
          rw [if_pos ⟨hac.mpr hA, hI⟩,
            if_pos (show ((∫⁻ x, p0 x * ({y | f y = 0}).indicator (fun _ => 1) x ∂μ = 0) ∧
              ∫⁻ x, ENNReal.ofReal ‖g x‖ ∂P ≠ ⊤) from ⟨hA, hB⟩)]
          rw [MeasureTheory.integral_congr_ae (hllr hA),
            MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part hIg,
            hQreal, hPreal]
      · rw [if_neg (fun hh : P ≪ Q ∧ Integrable (llr P Q) P => hA (hac.mp hh.1)),
          if_neg (fun hh : (∫⁻ x, p0 x * ({y | f y = 0}).indicator (fun _ => 1) x ∂μ = 0) ∧
            ∫⁻ x, ENNReal.ofReal ‖g x‖ ∂P ≠ ⊤ => hA hh.1)]
    have hcond : MeasurableSet {h : H | (∫⁻ x, p0 x * ({y | dens h y = 0}).indicator (fun _ => 1) x ∂μ = 0 ∧
            ∫⁻ x, ENNReal.ofReal ‖Real.log ((p0 x * (dens h x)⁻¹).toReal)‖
              ∂(μ.withDensity p0) ≠ ⊤)} := by
      have hset : MeasurableSet {p : H × X | dens p.1 p.2 = 0} := hdens (measurableSet_singleton 0)
      have hid : ∀ p : H × X, ({y | dens p.1 y = 0}).indicator (fun _ => (1 : ℝ≥0∞)) p.2
          = {q : H × X | dens q.1 q.2 = 0}.indicator (fun _ => (1 : ℝ≥0∞)) p := by
        intro p
        by_cases hp : dens p.1 p.2 = 0
        · rw [Set.indicator_of_mem (show p ∈ {q : H × X | dens q.1 q.2 = 0} from hp),
              Set.indicator_of_mem (show p.2 ∈ {y | dens p.1 y = 0} from hp)]
        · have h1 : p ∉ {q : H × X | dens q.1 q.2 = 0} := hp
          have h2 : p.2 ∉ {y | dens p.1 y = 0} := hp
          rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
      have hA : Measurable (fun h : H =>
          ∫⁻ x, p0 x * ({y | dens h y = 0}).indicator (fun _ => 1) x ∂μ) := by
        have hjoint : Measurable (fun p : H × X =>
            p0 p.2 * ({y | dens p.1 y = 0}).indicator (fun _ => (1 : ℝ≥0∞)) p.2) := by
          have hbase : Measurable (fun p : H × X =>
              p0 p.2 * {q : H × X | dens q.1 q.2 = 0}.indicator (fun _ => (1 : ℝ≥0∞)) p) :=
            (hp0.comp measurable_snd).mul (Measurable.indicator measurable_const hset)
          have hfun : (fun p : H × X =>
                p0 p.2 * ({y | dens p.1 y = 0}).indicator (fun _ => (1 : ℝ≥0∞)) p.2)
              = fun p : H × X =>
                p0 p.2 * {q : H × X | dens q.1 q.2 = 0}.indicator (fun _ => (1 : ℝ≥0∞)) p := by
            funext p
            rw [hid p]
          rw [hfun]
          exact hbase
        exact Measurable.lintegral_prod_right hjoint
      have hB : Measurable (fun h : H =>
          ∫⁻ x, ENNReal.ofReal ‖Real.log ((p0 x * (dens h x)⁻¹).toReal)‖
            ∂(μ.withDensity p0)) := by
        have hd : Measurable (fun p : H × X => dens p.1 p.2) := hdens
        have hquot : Measurable (fun p : H × X => p0 p.2 * (dens p.1 p.2)⁻¹) :=
          (hp0.comp measurable_snd).mul hd.inv
        have hlog : Measurable (fun p : H × X =>
            Real.log ((p0 p.2 * (dens p.1 p.2)⁻¹).toReal)) :=
          Real.measurable_log.comp (ENNReal.measurable_toReal.comp hquot)
        exact Measurable.lintegral_prod_right (ENNReal.measurable_ofReal.comp hlog.norm)
      exact (hA (measurableSet_singleton 0)).inter (hB (measurableSet_singleton ⊤)).compl
    have hval : Measurable (fun h : H =>
        ENNReal.ofReal ((∫⁻ x, ENNReal.ofReal (Real.log ((p0 x * (dens h x)⁻¹).toReal))
              ∂(μ.withDensity p0)).toReal
            - (∫⁻ x, ENNReal.ofReal (-(Real.log ((p0 x * (dens h x)⁻¹).toReal)))
              ∂(μ.withDensity p0)).toReal
            + (∫⁻ x, dens h x ∂μ).toReal - 1)) := by
      have hd : Measurable (fun p : H × X => dens p.1 p.2) := hdens
      have hquot : Measurable (fun p : H × X => p0 p.2 * (dens p.1 p.2)⁻¹) :=
        (hp0.comp measurable_snd).mul hd.inv
      have hlog : Measurable (fun p : H × X =>
          Real.log ((p0 p.2 * (dens p.1 p.2)⁻¹).toReal)) :=
        Real.measurable_log.comp (ENNReal.measurable_toReal.comp hquot)
      have hL1 : Measurable (fun h : H =>
          ∫⁻ x, ENNReal.ofReal (Real.log ((p0 x * (dens h x)⁻¹).toReal))
            ∂(μ.withDensity p0)) :=
        Measurable.lintegral_prod_right (ENNReal.measurable_ofReal.comp hlog)
      have hL2 : Measurable (fun h : H =>
          ∫⁻ x, ENNReal.ofReal (-(Real.log ((p0 x * (dens h x)⁻¹).toReal)))
            ∂(μ.withDensity p0)) :=
        Measurable.lintegral_prod_right (ENNReal.measurable_ofReal.comp hlog.neg)
      have hL3 : Measurable (fun h : H => ∫⁻ x, dens h x ∂μ) :=
        Measurable.lintegral_prod_right hd
      have h1 : Measurable (fun h : H =>
          (∫⁻ x, ENNReal.ofReal (Real.log ((p0 x * (dens h x)⁻¹).toReal))
            ∂(μ.withDensity p0)).toReal) := ENNReal.measurable_toReal.comp hL1
      have h2 : Measurable (fun h : H =>
          (∫⁻ x, ENNReal.ofReal (-(Real.log ((p0 x * (dens h x)⁻¹).toReal)))
            ∂(μ.withDensity p0)).toReal) := ENNReal.measurable_toReal.comp hL2
      have h3 : Measurable (fun h : H => (∫⁻ x, dens h x ∂μ).toReal) :=
        ENNReal.measurable_toReal.comp hL3
      exact ENNReal.measurable_ofReal.comp (((h1.sub h2).add h3).sub measurable_const)
    have heq : (fun h : H => InformationTheory.klDiv (μ.withDensity p0) (μ.withDensity (dens h)))
        = fun h => if (∫⁻ x, p0 x * ({y | dens h y = 0}).indicator (fun _ => 1) x ∂μ = 0 ∧
            ∫⁻ x, ENNReal.ofReal ‖Real.log ((p0 x * (dens h x)⁻¹).toReal)‖
              ∂(μ.withDensity p0) ≠ ⊤)
          then ENNReal.ofReal ((∫⁻ x, ENNReal.ofReal (Real.log ((p0 x * (dens h x)⁻¹).toReal))
                ∂(μ.withDensity p0)).toReal
              - (∫⁻ x, ENNReal.ofReal (-(Real.log ((p0 x * (dens h x)⁻¹).toReal)))
                ∂(μ.withDensity p0)).toReal
              + (∫⁻ x, dens h x ∂μ).toReal - 1)
          else ⊤ := funext key
    rw [heq]
    exact Measurable.piecewise hcond hval measurable_const
  exact hFmeas measurableSet_Iio
  /- @proof-region region.target-node.session.e583fcdf3097f3b5 end -/


set_option autoImplicit false in
theorem statopia_math_node_341907188_a9df01ea : ∀ {X H : Type*} [MeasurableSpace X] [MeasurableSpace H]
    (P : Measure X) [IsProbabilityMeasure P]
    (nu : Measure H) [IsProbabilityMeasure nu]
    (g : H → X → ℝ) (hg : Measurable (Function.uncurry g))
    (delta1 eps : ℝ) (heps : 0 < eps)
    (h_int : ∀ᵐ h ∂nu, MeasureTheory.Integrable (g h) P)
    (h_le_zero : ∀ᵐ h ∂nu, ∫ x, g h x ∂P ≤ 0)
    (h_lower : ∀ᵐ h ∂nu, -delta1 ≤ ∫ x, g h x ∂P)
    (h_pos_bound : ∀ᵐ h ∂nu, ∫⁻ x, ENNReal.ofReal (max (g h x) 0) ∂P ≤ (1 : ℝ≥0∞))
    (h_neg_bound : ∀ᵐ h ∂nu,
      ∫⁻ x, ENNReal.ofReal (max (-(g h x)) 0) ∂P ≤ ENNReal.ofReal (delta1 + 1))
    (h_neg_fin : ∀ᵐ x ∂P, ∫⁻ h, ENNReal.ofReal (max (-(g h x)) 0) ∂nu < ⊤)
    (h_pos_fin : ∀ᵐ x ∂P, ∫⁻ h, ENNReal.ofReal (max (g h x) 0) ∂nu < ⊤),
    ∀ᵐ x ∂(Measure.infinitePi (fun _ : ℕ => P)), ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ENNReal.ofReal (Real.exp (-(n : ℝ) * (delta1 + eps))) ≤
        ∫⁻ h, ENNReal.ofReal (Real.exp (∑ i ∈ Finset.range n, g h (x i))) ∂nu := by
  /- @proof-region region.target-node.session.01e719a297e1c154 begin -/
  intro X H _ _ P _ ν _ g hg δ1 ε hε hInt hUpper hLower hPos hNeg hNegFin hPosFin
  classical
  set gbar : X → ℝ := fun x => ∫ h, g h x ∂ν with hgbar
  have hSLLN_aux (hMeas : Measurable gbar) (hInt_bar : Integrable gbar P) :
      ∀ᵐ x ∂(Measure.infinitePi (fun _ : ℕ => P)),
        Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, gbar (x i)) / (n : ℝ)) atTop
          (nhds (∫ x, gbar x ∂P)) := by
    have hmap0 : Measure.map (fun x : ℕ → X => x 0) (Measure.infinitePi (fun _ : ℕ => P)) = P :=
      Measure.infinitePi_map_eval (fun _ : ℕ => P) 0
    have hInt0 : Integrable (fun x : ℕ → X => gbar (x 0)) (Measure.infinitePi (fun _ : ℕ => P)) := by
      have hI : Integrable gbar
          (Measure.map (fun x : ℕ → X => x 0) (Measure.infinitePi (fun _ : ℕ => P))) := by
        rw [hmap0]
        exact hInt_bar
      have h2 := hI.comp_measurable (f := fun x : ℕ → X => x 0) (measurable_pi_apply 0)
      simpa [Function.comp] using h2
    have hfam : iIndepFun (fun i (ω : ℕ → X) => gbar (ω i))
        (Measure.infinitePi (fun _ : ℕ => P)) :=
      iIndepFun_infinitePi (fun _ => hMeas)
    have hindep : Pairwise (Function.onFun
        (fun x1 x2 => x1 ⟂ᵢ[Measure.infinitePi (fun _ : ℕ => P)] x2)
        (fun i (x : ℕ → X) => gbar (x i))) := by
      intro i j hij
      exact hfam.indepFun hij
    have hident : ∀ i : ℕ, IdentDistrib (fun x : ℕ → X => gbar (x i))
        (fun x : ℕ → X => gbar (x 0)) (Measure.infinitePi (fun _ : ℕ => P))
        (Measure.infinitePi (fun _ : ℕ => P)) := by
      intro i
      have hi : Measure.map (fun x : ℕ → X => gbar (x i))
          (Measure.infinitePi (fun _ : ℕ => P)) = Measure.map gbar P := by
        have h := Measure.map_map (μ := Measure.infinitePi (fun _ : ℕ => P))
          (f := fun x : ℕ → X => x i) hMeas (measurable_pi_apply i)
        rw [Measure.infinitePi_map_eval (fun _ : ℕ => P) i] at h
        exact h.symm
      have h0 : Measure.map (fun x : ℕ → X => gbar (x 0))
          (Measure.infinitePi (fun _ : ℕ => P)) = Measure.map gbar P := by
        have h := Measure.map_map (μ := Measure.infinitePi (fun _ : ℕ => P))
          (f := fun x : ℕ → X => x 0) hMeas (measurable_pi_apply 0)
        rw [Measure.infinitePi_map_eval (fun _ : ℕ => P) 0] at h
        exact h.symm
      refine ⟨?_, ?_, ?_⟩
      all_goals
        first
          | exact (hMeas.comp (measurable_pi_apply i)).aemeasurable
          | exact (hMeas.comp (measurable_pi_apply 0)).aemeasurable
          | exact hi.trans h0.symm
    have hsw : ∫ x : ℕ → X, gbar (x 0) ∂(Measure.infinitePi (fun _ : ℕ => P)) = ∫ x, gbar x ∂P := by
      have key : ∫ x : ℕ → X, gbar (x 0) ∂(Measure.infinitePi (fun _ : ℕ => P))
          = ∫ x, gbar x ∂(Measure.map (fun x : ℕ → X => x 0)
              (Measure.infinitePi (fun _ : ℕ => P))) :=
        (MeasureTheory.integral_map (measurable_pi_apply 0).aemeasurable hMeas.aestronglyMeasurable).symm
      rw [key, hmap0]
    have hmain := ProbabilityTheory.strong_law_ae_real (fun i (x : ℕ → X) => gbar (x i))
      hInt0 hindep hident
    rwa [hsw] at hmain
  obtain ⟨hMeas0, hInt0bar, hL0⟩ :=
    statopia_math_node_2642199537_30588a87 P ν g hg δ1 hInt hLower hPos hNeg
  have hSLLN : ∀ᵐ x ∂(Measure.infinitePi (fun _ : ℕ => P)),
      Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, gbar (x i)) / (n : ℝ)) atTop
        (nhds (∫ x, gbar x ∂P)) :=
    hSLLN_aux (by simpa [hgbar] using hMeas0) (by simpa [hgbar] using hInt0bar)
  have hL : -δ1 ≤ ∫ x, gbar x ∂P := by
    simpa [hgbar] using hL0
  have hbig : ∀ᵐ x ∂(Measure.infinitePi (fun _ : ℕ => P)),
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → -((n : ℝ) * (δ1 + ε)) ≤ ∑ i ∈ Finset.range n, gbar (x i) := by
    filter_upwards [hSLLN] with x hx
    have hev : ∀ᶠ n : ℕ in atTop, -(δ1 + ε) < (∑ i ∈ Finset.range n, gbar (x i)) / (n : ℝ) :=
      hx.eventually (by
        filter_upwards [isOpen_Ioi.mem_nhds (show -(δ1 + ε) < ∫ y, gbar y ∂P by linarith)] with y hy
        exact hy)
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    refine ⟨max N 1, fun n hn => ?_⟩
    have hn1 : 1 ≤ n := le_trans (le_max_right N 1) hn
    have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hlt := hN n (le_trans (le_max_left N 1) hn)
    have hmul : -(δ1 + ε) * (n : ℝ) <
        (∑ i ∈ Finset.range n, gbar (x i)) / (n : ℝ) * (n : ℝ) :=
      mul_lt_mul_of_pos_right hlt hpos
    have hsimp : (∑ i ∈ Finset.range n, gbar (x i)) / (n : ℝ) * (n : ℝ)
        = ∑ i ∈ Finset.range n, gbar (x i) := by
      field_simp
    rw [hsimp] at hmul
    nlinarith
  have hJensen : ∀ᵐ x ∂(Measure.infinitePi (fun _ : ℕ => P)),
      ∀ n : ℕ, ENNReal.ofReal (Real.exp (∑ i ∈ Finset.range n, gbar (x i))) ≤
        ∫⁻ h, ENNReal.ofReal (Real.exp (∑ i ∈ Finset.range n, g h (x i))) ∂ν := by
    have h := statopia_math_node_2110233091_1dad31d5 P ν g hg hNegFin hPosFin
    simpa [hgbar] using h
  filter_upwards [hbig, hJensen] with x hx1 hx2
  obtain ⟨N, hN⟩ := hx1
  refine ⟨N, fun n hn => le_trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)) (hx2 n)⟩
  nlinarith [hN n hn]
  /- @proof-region region.target-node.session.01e719a297e1c154 end -/


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


set_option autoImplicit false in
theorem generic_KL_evidence : ∀ {X H : Type*} [MeasurableSpace X] [MeasurableSpace H]
    (μ : Measure X) [SigmaFinite μ]
    (p0 : X → ℝ≥0∞) (hp0 : Measurable p0) (hp0_int : ∫⁻ x, p0 x ∂μ = 1)
    (PiPrior : Measure H) [IsProbabilityMeasure PiPrior]
    (dens : H → X → ℝ≥0∞) (hdens : Measurable (Function.uncurry dens))
    (hdens_lt_top : ∀ h : H, ∀ᵐ x ∂μ, dens h x ≠ ⊤)
    (hdens_norm : ∀ᵐ h ∂PiPrior, ∫⁻ x, dens h x ∂μ ≤ 1)
    (hKL_pos : ∀ delta : ℝ, 0 < delta →
      0 < PiPrior {h : H |
        InformationTheory.klDiv (μ.withDensity p0) (μ.withDensity (dens h))
          < ENNReal.ofReal delta}),
    ∀ delta : ℝ, 0 < delta →
      ∀ᵐ x ∂(Measure.infinitePi (fun _ : ℕ => μ.withDensity p0)),
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          ENNReal.ofReal (Real.exp (-(n : ℝ) * delta)) ≤
            ∫⁻ h, ∏ i ∈ Finset.range n, (dens h (x i) * (p0 (x i))⁻¹) ∂PiPrior := by
  /- @proof-region region.target-node.session.2d97536fa28e7d13 begin -/
  intro X H _ _ μ _ p0 hp0_meas hp0_int PiPrior _ dens hdens_meas hdens_lt_top hdens_norm hKL δ hδ
  haveI hPprob : IsProbabilityMeasure (μ.withDensity p0) :=
    ⟨by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hp0_int]⟩
  have hP_ne_zero : ∀ᵐ x ∂(μ.withDensity p0), p0 x ≠ 0 := by
    have hmeas : MeasurableSet {x : X | p0 x = 0} := hp0_meas (measurableSet_singleton 0)
    have hzero : (μ.withDensity p0) {x : X | p0 x = 0} = 0 := by
      rw [withDensity_apply _ hmeas]
      have hzero_ae : p0 =ᵐ[μ.restrict {x : X | p0 x = 0}] 0 := by
        filter_upwards [ae_restrict_mem hmeas] with x hx
        simpa using hx
      rw [lintegral_congr_ae hzero_ae]
      simp
    rw [ae_iff]
    simpa using hzero
  have hP_lt_top : ∀ᵐ x ∂(μ.withDensity p0), p0 x < ⊤ := by
    have hfin : ∀ᵐ x ∂μ, p0 x < ⊤ :=
      ae_lt_top hp0_meas (by rw [hp0_int]; exact ENNReal.one_ne_top)
    exact hfin.filter_mono
      (Measure.AbsolutelyContinuous.ae_le (withDensity_absolutelyContinuous μ p0))

  set δ₁ : ℝ := δ / 2 with hδ₁def
  have hδ₁pos : 0 < δ₁ := by
    rw [hδ₁def]; linarith
  have hδ₁lt : δ₁ < δ := by
    rw [hδ₁def]; linarith
  have hPuniv : (μ.withDensity p0).real Set.univ = 1 := by
    rw [Measure.real_def]
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hp0_int]
    simp
  set δ₀ : ℝ := min (δ₁ ^ 2 / 64) (δ₁ / 4) with hδ₀def
  have hδ₀pos : 0 < δ₀ := by
    rw [hδ₀def]
    exact lt_min (div_pos (pow_pos hδ₁pos 2) (by norm_num)) (by linarith)
  have hδ₀_le : δ₀ ≤ δ₁ ^ 2 / 64 := by
    rw [hδ₀def]
    exact min_le_left _ _
  have hδ₀_le' : δ₀ ≤ δ₁ / 4 := by
    rw [hδ₀def]
    exact min_le_right _ _
  have hsqrt₀ : Real.sqrt δ₀ ≤ δ₁ / 8 := by
    have h8 : (0 : ℝ) ≤ δ₁ / 8 := by linarith
    have hsq : δ₀ ≤ (δ₁ / 8) ^ 2 := by
      have hEq : (δ₁ / 8) ^ 2 = δ₁ ^ 2 / 64 := by ring
      rw [hEq]
      exact hδ₀_le
    calc Real.sqrt δ₀ ≤ Real.sqrt ((δ₁ / 8) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = δ₁ / 8 := Real.sqrt_sq h8
  have hδ₀bound : δ₀ + 2 * Real.sqrt δ₀ ≤ δ₁ := by
    nlinarith [hδ₀_le', hsqrt₀, Real.sqrt_nonneg δ₀]
  set Kset : Set H :=
    {h : H | InformationTheory.klDiv (μ.withDensity p0) (μ.withDensity (dens h))
      < ENNReal.ofReal δ₀} with hKdef
  have hKpos : 0 < PiPrior Kset := by
    rw [hKdef]
    exact hKL δ₀ hδ₀pos
  set b : ℝ≥0∞ := PiPrior Kset with hbdef
  have hb_ne_zero : b ≠ 0 := by
    rw [hbdef]; exact ne_of_gt hKpos
  have hb_le_one : b ≤ 1 := by
    rw [hbdef]
    calc PiPrior Kset ≤ PiPrior Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hb_ne_top : b ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hb_le_one ENNReal.one_lt_top)
  set ν : Measure H := b⁻¹ • PiPrior.restrict Kset with hνdef
  haveI hνprob : IsProbabilityMeasure ν := by
    constructor
    rw [hνdef, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
      Set.univ_inter, ← hbdef]
    exact ENNReal.inv_mul_cancel hb_ne_zero hb_ne_top
  have hν_ac : ν ≪ PiPrior := by
    rw [hνdef]
    have h1 : PiPrior.restrict Kset ≪ PiPrior :=
      Measure.absolutelyContinuous_of_le (Measure.restrict_le_self (μ := PiPrior) (s := Kset))
    have h2 : b⁻¹ • PiPrior ≪ PiPrior :=
      Measure.absolutelyContinuous_of_le_smul (le_refl (b⁻¹ • PiPrior))
    exact (h1.smul b⁻¹).trans h2
  have hK_meas : MeasurableSet Kset := by
    rw [hKdef]
    exact statopia_math_node_3155168291_3ca337d1 μ p0 hp0_meas hp0_int dens hdens_meas
      hdens_lt_top δ₀
  have hν_K : ∀ᵐ h ∂ν, h ∈ Kset := by
    rw [ae_iff]
    change ν Ksetᶜ = 0
    rw [hνdef, Measure.smul_apply, Measure.restrict_apply hK_meas.compl]
    have hempty : Ksetᶜ ∩ Kset = ∅ := by
      ext h; simp
    rw [hempty, measure_empty, smul_zero]
  have hν_norm : ∀ᵐ h ∂ν, ∫⁻ x, dens h x ∂μ ≤ 1 :=
    hdens_norm.filter_mono (Measure.AbsolutelyContinuous.ae_le hν_ac)
  set g : H → X → ℝ :=
    fun h x => Real.log (dens h x).toReal - Real.log (p0 x).toReal with hgdef
  have hpair_meas : ∀ h : H, Measurable fun x : X => (h, x) := fun h =>
    measurable_prodMk_left
  have hdens_h_meas : ∀ h : H, Measurable (dens h) := fun h =>
    hdens_meas.comp (hpair_meas h)
  have hg_meas : Measurable (Function.uncurry g) := by
    rw [hgdef]
    have h1 : Measurable fun p : H × X => Real.log (dens p.1 p.2).toReal :=
      hdens_meas.ennreal_toReal.log
    have h2 : Measurable fun p : H × X => Real.log (p0 p.2).toReal :=
      (hp0_meas.ennreal_toReal.log).comp measurable_snd
    exact h1.sub h2
  have hpert : ∀ h : H, h ∈ Kset → (∫⁻ x, dens h x ∂μ ≤ 1) →
      MeasureTheory.Integrable (g h) (μ.withDensity p0) ∧
      (-δ₁ ≤ ∫ x, g h x ∂(μ.withDensity p0)) ∧
      (∫ x, g h x ∂(μ.withDensity p0) ≤ 0) ∧
      (∫⁻ x, ENNReal.ofReal (max (g h x) 0) ∂(μ.withDensity p0) ≤ 1) ∧
      (∫⁻ x, ENNReal.ofReal (max (-(g h x)) 0) ∂(μ.withDensity p0)
        ≤ ENNReal.ofReal (δ₁ + 1)) := by
    intro h hK hnorm
    have hK' : InformationTheory.klDiv (μ.withDensity p0) (μ.withDensity (dens h))
        < ENNReal.ofReal δ₀ := by
      have h' := hK
      rw [hKdef] at h'
      exact h'
    have hkl_ne : InformationTheory.klDiv (μ.withDensity p0) (μ.withDensity (dens h)) ≠ ⊤ :=
      ne_of_lt (lt_of_lt_of_le hK' le_top)
    obtain ⟨hne, hlt, hInt, hlow, hpos, hneg⟩ :=
      statopia_math_node_3862551001_c5ec6ec7 μ p0 (dens h) hp0_meas
        (hdens_h_meas h) hp0_int hnorm hkl_ne
    have hKlt : (InformationTheory.klDiv (μ.withDensity p0) (μ.withDensity (dens h))).toReal
        < δ₀ := by
      have h2 := (ENNReal.toReal_lt_toReal hkl_ne ENNReal.ofReal_ne_top).mpr hK'
      rwa [ENNReal.toReal_ofReal (le_of_lt hδ₀pos)] at h2
    have hInt' : MeasureTheory.Integrable
        (fun x => Real.log (dens h x).toReal - Real.log (p0 x).toReal) (μ.withDensity p0) := hInt
    obtain ⟨hupper, hdef⟩ :=
      statopia_math_node_2407238401_b71e9352 μ p0 (dens h) hp0_meas
        (hdens_h_meas h) hp0_int hnorm hne hlt hInt' hlow
    have hlowg : -(InformationTheory.klDiv (μ.withDensity p0)
          (μ.withDensity (dens h))).toReal
        ≤ (∫ x, g h x ∂(μ.withDensity p0))
          + (1 - (μ.withDensity (dens h)).real Set.univ) := by
      rw [hPuniv] at hlow
      rw [hgdef]
      exact hlow
    refine ⟨hInt, ?_, ?_, ?_, ?_⟩
    · linarith [hlowg, hdef, hKlt, Real.sqrt_le_sqrt (le_of_lt hKlt), hδ₀bound,
        Real.sqrt_nonneg δ₀]
    · rw [hgdef]; exact hupper
    · rw [hgdef]; exact hpos
    · refine le_trans ?_ (ENNReal.ofReal_le_ofReal (by linarith :
        (InformationTheory.klDiv (μ.withDensity p0) (μ.withDensity (dens h))).toReal + 1
          ≤ δ₁ + 1))
      rw [hgdef]
      exact hneg
  have hInt_ae : ∀ᵐ h ∂ν, MeasureTheory.Integrable (g h) (μ.withDensity p0) := by
    filter_upwards [hν_K, hν_norm] with h hK hnorm
    exact (hpert h hK hnorm).1
  have hLower_ae : ∀ᵐ h ∂ν, -δ₁ ≤ ∫ x, g h x ∂(μ.withDensity p0) := by
    filter_upwards [hν_K, hν_norm] with h hK hnorm
    exact (hpert h hK hnorm).2.1
  have hUpper_ae : ∀ᵐ h ∂ν, ∫ x, g h x ∂(μ.withDensity p0) ≤ 0 := by
    filter_upwards [hν_K, hν_norm] with h hK hnorm
    exact (hpert h hK hnorm).2.2.1
  have hPos_ae : ∀ᵐ h ∂ν,
      ∫⁻ x, ENNReal.ofReal (max (g h x) 0) ∂(μ.withDensity p0) ≤ 1 := by
    filter_upwards [hν_K, hν_norm] with h hK hnorm
    exact (hpert h hK hnorm).2.2.2.1
  have hNeg_ae : ∀ᵐ h ∂ν,
      ∫⁻ x, ENNReal.ofReal (max (-(g h x)) 0) ∂(μ.withDensity p0)
        ≤ ENNReal.ofReal (δ₁ + 1) := by
    filter_upwards [hν_K, hν_norm] with h hK hnorm
    exact (hpert h hK hnorm).2.2.2.2
  have hFneg_meas :
      Measurable fun p : H × X => ENNReal.ofReal (max (-(Function.uncurry g p)) 0) :=
    (hg_meas.neg.max measurable_const).ennreal_ofReal
  have hFpos_meas :
      Measurable fun p : H × X => ENNReal.ofReal (max (Function.uncurry g p) 0) :=
    (hg_meas.max measurable_const).ennreal_ofReal
  have hNegFin : ∀ᵐ x ∂(μ.withDensity p0),
      ∫⁻ h, ENNReal.ofReal (max (-(g h x)) 0) ∂ν < ⊤ := by
    have hmeas : AEMeasurable
        (fun x : X => ∫⁻ h, ENNReal.ofReal (max (-(g h x)) 0) ∂ν) (μ.withDensity p0) :=
      AEMeasurable.lintegral_prod_left
        (f := fun h x => ENNReal.ofReal (max (-(g h x)) 0)) hFneg_meas.aemeasurable
    refine ae_lt_top' hmeas ?_
    have h1 : ∫⁻ x, (∫⁻ h, ENNReal.ofReal (max (-(g h x)) 0) ∂ν) ∂(μ.withDensity p0)
        = ∫⁻ p : H × X, ENNReal.ofReal (max (-(Function.uncurry g p)) 0)
            ∂(ν.prod (μ.withDensity p0)) :=
      (MeasureTheory.lintegral_prod_symm (μ := ν) (ν := μ.withDensity p0)
        (fun p : H × X => ENNReal.ofReal (max (-(Function.uncurry g p)) 0))
        hFneg_meas.aemeasurable).symm
    have h2 : ∫⁻ p : H × X, ENNReal.ofReal (max (-(Function.uncurry g p)) 0)
          ∂(ν.prod (μ.withDensity p0))
        = ∫⁻ h, (∫⁻ x, ENNReal.ofReal (max (-(g h x)) 0) ∂(μ.withDensity p0)) ∂ν :=
      MeasureTheory.lintegral_prod (μ := ν) (ν := μ.withDensity p0)
        (fun p : H × X => ENNReal.ofReal (max (-(Function.uncurry g p)) 0))
        hFneg_meas.aemeasurable
    rw [h1.trans h2]
    refine ne_of_lt (lt_of_le_of_lt ?_ (ENNReal.ofReal_lt_top (r := δ₁ + 1)))
    calc ∫⁻ h, (∫⁻ x, ENNReal.ofReal (max (-(g h x)) 0) ∂(μ.withDensity p0)) ∂ν
        ≤ ∫⁻ _, ENNReal.ofReal (δ₁ + 1) ∂ν := lintegral_mono_ae hNeg_ae
      _ = ENNReal.ofReal (δ₁ + 1) * ν Set.univ := lintegral_const _
      _ = ENNReal.ofReal (δ₁ + 1) := by rw [measure_univ, mul_one]
  have hPosFin : ∀ᵐ x ∂(μ.withDensity p0),
      ∫⁻ h, ENNReal.ofReal (max (g h x) 0) ∂ν < ⊤ := by
    have hmeas : AEMeasurable
        (fun x : X => ∫⁻ h, ENNReal.ofReal (max (g h x) 0) ∂ν) (μ.withDensity p0) :=
      AEMeasurable.lintegral_prod_left
        (f := fun h x => ENNReal.ofReal (max (g h x) 0)) hFpos_meas.aemeasurable
    refine ae_lt_top' hmeas ?_
    have h1 : ∫⁻ x, (∫⁻ h, ENNReal.ofReal (max (g h x) 0) ∂ν) ∂(μ.withDensity p0)
        = ∫⁻ p : H × X, ENNReal.ofReal (max (Function.uncurry g p) 0)
            ∂(ν.prod (μ.withDensity p0)) :=
      (MeasureTheory.lintegral_prod_symm (μ := ν) (ν := μ.withDensity p0)
        (fun p : H × X => ENNReal.ofReal (max (Function.uncurry g p) 0))
        hFpos_meas.aemeasurable).symm
    have h2 : ∫⁻ p : H × X, ENNReal.ofReal (max (Function.uncurry g p) 0)
          ∂(ν.prod (μ.withDensity p0))
        = ∫⁻ h, (∫⁻ x, ENNReal.ofReal (max (g h x) 0) ∂(μ.withDensity p0)) ∂ν :=
      MeasureTheory.lintegral_prod (μ := ν) (ν := μ.withDensity p0)
        (fun p : H × X => ENNReal.ofReal (max (Function.uncurry g p) 0))
        hFpos_meas.aemeasurable
    rw [h1.trans h2]
    refine ne_of_lt (lt_of_le_of_lt ?_ ENNReal.one_lt_top)
    calc ∫⁻ h, (∫⁻ x, ENNReal.ofReal (max (g h x) 0) ∂(μ.withDensity p0)) ∂ν
        ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂ν := lintegral_mono_ae hPos_ae
      _ = 1 * ν Set.univ := lintegral_const _
      _ = 1 := by rw [measure_univ, mul_one]
  set eps : ℝ := (δ - δ₁) / 2 with hepsdef
  have hepspos : 0 < eps := by
    rw [hepsdef]; linarith
  have hepslt : δ₁ + eps < δ := by
    rw [hepsdef, hδ₁def]; linarith
  have hcore := statopia_math_node_341907188_a9df01ea (μ.withDensity p0) ν g hg_meas
    δ₁ eps hepspos hInt_ae hUpper_ae hLower_ae hPos_ae hNeg_ae hNegFin hPosFin
  have hbν : b • ν = PiPrior.restrict Kset := by
    rw [hνdef, smul_smul, mul_comm, ENNReal.inv_mul_cancel hb_ne_zero hb_ne_top, one_smul]
  have hsmulInt : ∀ G : H → ℝ≥0∞, ∫⁻ h, G h ∂(b • ν) = b • ∫⁻ h, G h ∂ν := by
    intro G
    rw [MeasureTheory.lintegral_smul_measure]
  have hident : ∀ᵐ x ∂(Measure.infinitePi (fun _ : ℕ => μ.withDensity p0)), ∀ᵐ h ∂ν,
      ∀ n : ℕ, ∏ i ∈ Finset.range n, (dens h (x i) * (p0 (x i))⁻¹)
        = ENNReal.ofReal (Real.exp (∑ i ∈ Finset.range n, g h (x i))) := by
    have hcyl : ∀ (i : ℕ) (A : Set X), MeasurableSet A →
        (Measure.infinitePi (fun _ : ℕ => μ.withDensity p0)) {x : ℕ → X | x i ∈ A}
          = (μ.withDensity p0) A := by
      intro i A hA
      have h := Measure.infinitePi_pi (fun _ : ℕ => (μ.withDensity p0))
        (s := {i}) (t := fun _ : ℕ => A) (by intro j hj; exact hA)
      have hset : Set.pi (↑({i} : Finset ℕ)) (fun _ : ℕ => A) = {x : ℕ → X | x i ∈ A} := by
        ext x
        simp [Set.mem_pi, Finset.mem_singleton]
      rw [hset, Finset.prod_singleton] at h
      exact h
    have hsingle : ∀ (a c : ℝ≥0∞), a ≠ 0 → a ≠ ⊤ → c ≠ 0 → c ≠ ⊤ →
        a * c⁻¹ = ENNReal.ofReal (Real.exp (Real.log a.toReal - Real.log c.toReal)) := by
      intro a c ha0 hat hc0 hct
      have hctop : c⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hc0
      have hprod : a * c⁻¹ ≠ ⊤ := ENNReal.mul_ne_top hat hctop
      rw [← ENNReal.ofReal_toReal hprod]
      congr 1
      rw [ENNReal.toReal_mul, ENNReal.toReal_inv, Real.exp_sub,
        Real.exp_log (ENNReal.toReal_pos ha0 hat), Real.exp_log (ENNReal.toReal_pos hc0 hct),
        div_eq_mul_inv]
    have hdens_good_ae : ∀ᵐ h ∂ν, ∀ᵐ x ∂(μ.withDensity p0),
        dens h x ≠ 0 ∧ dens h x < ⊤ := by
      filter_upwards [hν_K, hν_norm] with h hK hnorm
      have hK' : InformationTheory.klDiv (μ.withDensity p0) (μ.withDensity (dens h))
          < ENNReal.ofReal δ₀ := by
        have h' := hK
        rw [hKdef] at h'
        exact h'
      have hkl_ne : InformationTheory.klDiv (μ.withDensity p0) (μ.withDensity (dens h)) ≠ ⊤ :=
        ne_of_lt (lt_of_lt_of_le hK' le_top)
      obtain ⟨hne, hlt, -⟩ :=
        statopia_math_node_3862551001_c5ec6ec7 μ p0 (dens h) hp0_meas
          (hdens_h_meas h) hp0_int hnorm hkl_ne
      filter_upwards [hne, hlt] with x h1 h2 using ⟨h1, h2⟩
    have hp0_good : ∀ᵐ x ∂(μ.withDensity p0), p0 x ≠ 0 ∧ p0 x < ⊤ := by
      filter_upwards [hP_ne_zero, hP_lt_top] with x h1 h2 using ⟨h1, h2⟩
    have hcoord : ∀ᵐ h ∂ν, ∀ᵐ x ∂(Measure.infinitePi (fun _ : ℕ => μ.withDensity p0)),
        ∀ i : ℕ, dens h (x i) ≠ 0 ∧ dens h (x i) < ⊤ ∧ p0 (x i) ≠ 0 ∧ p0 (x i) < ⊤ := by
      filter_upwards [hdens_good_ae] with h hgood
      have hcomb : ∀ᵐ x ∂(μ.withDensity p0),
          dens h x ≠ 0 ∧ dens h x < ⊤ ∧ p0 x ≠ 0 ∧ p0 x < ⊤ := by
        filter_upwards [hgood, hp0_good] with x h1 h2
        exact ⟨h1.1, h1.2, h2.1, h2.2⟩
      set Bad : Set X := {y : X | dens h y = 0} ∪ {y : X | dens h y = ⊤}
        ∪ {y : X | p0 y = 0} ∪ {y : X | p0 y = ⊤} with hBaddef
      have hBad_meas : MeasurableSet Bad := by
        rw [hBaddef]
        exact (((hdens_h_meas h (measurableSet_singleton 0)).union
          (hdens_h_meas h (measurableSet_singleton ⊤))).union
          (hp0_meas (measurableSet_singleton 0))).union (hp0_meas (measurableSet_singleton ⊤))
      have hBad0 : (μ.withDensity p0) Bad = 0 := by
        have hsets : {y : X | ¬ (dens h y ≠ 0 ∧ dens h y < ⊤ ∧ p0 y ≠ 0 ∧ p0 y < ⊤)} = Bad := by
          rw [hBaddef]
          ext y
          simp only [Set.mem_setOf_eq, Set.mem_union, lt_top_iff_ne_top]
          constructor
          · intro hn
            by_cases h0 : dens h y = 0
            · exact Or.inl (Or.inl (Or.inl h0))
            · by_cases h1 : dens h y = ⊤
              · exact Or.inl (Or.inl (Or.inr h1))
              · by_cases h2 : p0 y = 0
                · exact Or.inl (Or.inr h2)
                · exact Or.inr (by_contra fun h3 => hn ⟨h0, h1, h2, h3⟩)
          · intro hd hconj
            exact hd.elim
              (fun hl => hl.elim
                (fun hAB => hAB.elim (fun h0 => hconj.1 h0) (fun h1 => hconj.2.1 h1))
                (fun h2 => hconj.2.2.1 h2))
              (fun h3 => hconj.2.2.2 h3)
        rw [← hsets]
        exact MeasureTheory.ae_iff.mp hcomb
      have hcyl0 : ∀ i : ℕ, (Measure.infinitePi (fun _ : ℕ => μ.withDensity p0))
          {x : ℕ → X | x i ∈ Bad} = 0 := by
        intro i
        rw [hcyl i Bad hBad_meas, hBad0]
      have hmain : ∀ᵐ x ∂(Measure.infinitePi (fun _ : ℕ => μ.withDensity p0)),
          ∀ i : ℕ, x i ∉ Bad := by
        rw [ae_iff]
        have hsets : {x : ℕ → X | ¬ ∀ i : ℕ, x i ∉ Bad}
            = ⋃ i : ℕ, {x : ℕ → X | x i ∈ Bad} := by
          ext x
          simp only [Set.mem_setOf_eq, Set.mem_iUnion]
          simp only [not_forall, not_not]
        rw [hsets]
        exact measure_iUnion_null hcyl0
      filter_upwards [hmain] with x hx
      intro i
      have hx' := hx i
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro hzero; exact hx' (by simp [hBaddef, hzero])
      · rw [lt_top_iff_ne_top]; intro htop; exact hx' (by simp [hBaddef, htop])
      · intro hzero; exact hx' (by simp [hBaddef, hzero])
      · rw [lt_top_iff_ne_top]; intro htop; exact hx' (by simp [hBaddef, htop])
    have hident_pt : ∀ (h : H) (y : ℕ → X),
        (∀ i : ℕ, dens h (y i) ≠ 0 ∧ dens h (y i) < ⊤ ∧ p0 (y i) ≠ 0 ∧ p0 (y i) < ⊤) →
        ∀ n : ℕ, ∏ i ∈ Finset.range n, (dens h (y i) * (p0 (y i))⁻¹)
          = ENNReal.ofReal (Real.exp (∑ i ∈ Finset.range n, g h (y i))) := by
      have hofReal_prod : ∀ (s : Finset ℕ) (F : ℕ → ℝ),
          (∏ i ∈ s, ENNReal.ofReal (Real.exp (F i)))
            = ENNReal.ofReal (∏ i ∈ s, Real.exp (F i)) := by
        intro s F
        induction s using Finset.induction with
        | empty => simp
        | insert a s ha ih =>
            rw [Finset.prod_insert ha, Finset.prod_insert ha, ih,
              ← ENNReal.ofReal_mul (le_of_lt (Real.exp_pos (F a)))]
      intro h y hy n
      have hstep1 : (∏ i ∈ Finset.range n, (dens h (y i) * (p0 (y i))⁻¹))
          = ∏ i ∈ Finset.range n, ENNReal.ofReal
              (Real.exp (Real.log (dens h (y i)).toReal - Real.log (p0 (y i)).toReal)) := by
        refine Finset.prod_congr rfl ?_
        intro i hi
        exact hsingle (dens h (y i)) (p0 (y i)) (hy i).1
          (ne_of_lt (hy i).2.1) (hy i).2.2.1 (ne_of_lt (hy i).2.2.2)
      rw [hstep1, hofReal_prod (Finset.range n)
        (fun i => Real.log (dens h (y i)).toReal - Real.log (p0 (y i)).toReal)]
      congr 1
      rw [Real.exp_sum]
    set A : Set (H × (ℕ → X)) := ⋃ i : ℕ,
      ({z : H × (ℕ → X) | dens z.1 (z.2 i) = 0} ∪ {z : H × (ℕ → X) | dens z.1 (z.2 i) = ⊤}
        ∪ {z : H × (ℕ → X) | p0 (z.2 i) = 0} ∪ {z : H × (ℕ → X) | p0 (z.2 i) = ⊤}) with hAdef
    have hA_meas : MeasurableSet A := by
      rw [hAdef]
      apply MeasurableSet.iUnion
      intro i
      have hd : Measurable fun z : H × (ℕ → X) => dens z.1 (z.2 i) :=
        hdens_meas.comp (Measurable.prodMk measurable_fst ((measurable_pi_apply i).comp measurable_snd))
      have hp : Measurable fun z : H × (ℕ → X) => p0 (z.2 i) :=
        hp0_meas.comp ((measurable_pi_apply i).comp measurable_snd)
      exact (((hd (measurableSet_singleton 0)).union (hd (measurableSet_singleton ⊤))).union
        (hp (measurableSet_singleton 0))).union (hp (measurableSet_singleton ⊤))
    have hmemA : ∀ (h : H) (x : ℕ → X),
        ((h, x) ∈ A ↔ ∃ i : ℕ,
          ((dens h (x i) = 0 ∨ dens h (x i) = ⊤) ∨ p0 (x i) = 0) ∨ p0 (x i) = ⊤) := by
      intro h x
      rw [hAdef]
      simp only [Set.mem_iUnion, Set.mem_union, Set.mem_setOf_eq]
    have hnotA : ∀ (h : H) (x : ℕ → X),
        (∀ i : ℕ, dens h (x i) ≠ 0 ∧ dens h (x i) < ⊤ ∧ p0 (x i) ≠ 0 ∧ p0 (x i) < ⊤) →
        (h, x) ∉ A := by
      intro h x hg hmem
      obtain ⟨i, hi⟩ := (hmemA h x).1 hmem
      have h1 : dens h (x i) ≠ 0 := (hg i).1
      have h2 : dens h (x i) ≠ ⊤ := ne_of_lt (hg i).2.1
      have h3 : p0 (x i) ≠ 0 := (hg i).2.2.1
      have h4 : p0 (x i) ≠ ⊤ := ne_of_lt (hg i).2.2.2
      have hni : ¬ (((dens h (x i) = 0 ∨ dens h (x i) = ⊤) ∨ p0 (x i) = 0) ∨ p0 (x i) = ⊤) :=
        fun hb =>
          Or.elim hb
            (fun hl => Or.elim hl
              (fun hAB => Or.elim hAB (fun h0 => h1 h0) (fun ht => h2 ht))
              (fun hz => h3 hz))
            (fun hz2 => h4 hz2)
      exact hni hi
    have hgood_of_notA : ∀ (h : H) (x : ℕ → X), (h, x) ∉ A →
        ∀ i : ℕ, dens h (x i) ≠ 0 ∧ dens h (x i) < ⊤ ∧ p0 (x i) ≠ 0 ∧ p0 (x i) < ⊤ := by
      intro h x hnot i
      have hni : ¬ (((dens h (x i) = 0 ∨ dens h (x i) = ⊤) ∨ p0 (x i) = 0) ∨ p0 (x i) = ⊤) := by
        intro hb
        exact hnot ((hmemA h x).2 ⟨i, hb⟩)
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro h0; exact hni (Or.inl (Or.inl (Or.inl h0)))
      · rw [lt_top_iff_ne_top]; intro ht; exact hni (Or.inl (Or.inl (Or.inr ht)))
      · intro h0; exact hni (Or.inl (Or.inr h0))
      · rw [lt_top_iff_ne_top]; intro ht; exact hni (Or.inr ht)
    have hF_meas : Measurable (A.indicator (fun _ => (1 : ℝ≥0∞))) :=
      measurable_const.indicator hA_meas
    have hmeasure_ind : ∫⁻ z, A.indicator (fun _ => (1 : ℝ≥0∞)) z
        ∂(ν.prod (Measure.infinitePi (fun _ : ℕ => μ.withDensity p0)))
        = (ν.prod (Measure.infinitePi (fun _ : ℕ => μ.withDensity p0))) A := by
      rw [lintegral_indicator hA_meas]
      rw [show ∫⁻ z in A, (1 : ℝ≥0∞)
            ∂(ν.prod (Measure.infinitePi (fun _ : ℕ => μ.withDensity p0)))
          = ∫⁻ z, (1 : ℝ≥0∞)
              ∂((ν.prod (Measure.infinitePi (fun _ : ℕ => μ.withDensity p0))).restrict A) from rfl]
      rw [lintegral_const, one_mul, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    have hA_null : (ν.prod (Measure.infinitePi (fun _ : ℕ => μ.withDensity p0))) A = 0 := by
      have hgood_prod :
          ∀ᵐ z ∂(ν.prod (Measure.infinitePi (fun _ : ℕ => μ.withDensity p0))), z ∉ A := by
        rw [MeasureTheory.Measure.ae_prod_iff_ae_ae (p := fun z : H × (ℕ → X) => z ∉ A)
          hA_meas.compl]
        exact hcoord.mono (fun h hh => hh.mono (fun x hx => hnotA h x hx))
      have := MeasureTheory.ae_iff.mp hgood_prod
      simpa using this
    have hzeroint : ∫⁻ x, (∫⁻ h, A.indicator (fun _ => (1 : ℝ≥0∞)) (h, x) ∂ν)
        ∂(Measure.infinitePi (fun _ : ℕ => μ.withDensity p0)) = 0 := by
      rw [← MeasureTheory.lintegral_prod_symm (μ := ν)
        (ν := Measure.infinitePi (fun _ : ℕ => μ.withDensity p0))
        (f := fun z : H × (ℕ → X) => A.indicator (fun _ => (1 : ℝ≥0∞)) z) hF_meas.aemeasurable]
      rw [hmeasure_ind, hA_null]
    have hae : ∀ᵐ x ∂(Measure.infinitePi (fun _ : ℕ => μ.withDensity p0)),
        ∀ᵐ h ∂ν, ∀ i : ℕ, dens h (x i) ≠ 0 ∧ dens h (x i) < ⊤ ∧ p0 (x i) ≠ 0 ∧ p0 (x i) < ⊤ := by
      have hmeas_int : AEMeasurable
          (fun x : ℕ → X => ∫⁻ h, A.indicator (fun _ => (1 : ℝ≥0∞)) (h, x) ∂ν)
          (Measure.infinitePi (fun _ : ℕ => μ.withDensity p0)) :=
        AEMeasurable.lintegral_prod_left
          (f := fun h x => A.indicator (fun _ => (1 : ℝ≥0∞)) (h, x)) hF_meas.aemeasurable
      have hzero_ae : ∀ᵐ x ∂(Measure.infinitePi (fun _ : ℕ => μ.withDensity p0)),
          ∫⁻ h, A.indicator (fun _ => (1 : ℝ≥0∞)) (h, x) ∂ν = 0 :=
        (MeasureTheory.lintegral_eq_zero_iff' hmeas_int).mp hzeroint
      filter_upwards [hzero_ae] with x hx
      have hsecA : MeasurableSet {h : H | (h, x) ∈ A} :=
        hA_meas.preimage (Measurable.prodMk measurable_id measurable_const)
      have hsec_int : ν {h : H | (h, x) ∈ A}
          = ∫⁻ h, ({h' : H | (h', x) ∈ A}).indicator (fun _ => (1 : ℝ≥0∞)) h ∂ν := by
        rw [lintegral_indicator hsecA]
        rw [show ∫⁻ h in {h' : H | (h', x) ∈ A}, (1 : ℝ≥0∞) ∂ν
            = ∫⁻ h, (1 : ℝ≥0∞) ∂(ν.restrict {h' : H | (h', x) ∈ A}) from rfl]
        rw [lintegral_const, one_mul, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
      have hsec_zero : ν {h : H | (h, x) ∈ A} = 0 := by
        rw [hsec_int]
        have hxs : ∫⁻ h, ({h' : H | (h', x) ∈ A}).indicator (fun _ => (1 : ℝ≥0∞)) h ∂ν
            = ∫⁻ h, A.indicator (fun _ => (1 : ℝ≥0∞)) (h, x) ∂ν := rfl
        rw [hxs, hx]
      have hnotmem : ∀ᵐ h ∂ν, (h, x) ∉ A := by
        rw [ae_iff]
        simpa using hsec_zero
      filter_upwards [hnotmem] with h hh
      exact hgood_of_notA h x hh
    exact hae.mono (fun x hx => hx.mono (fun h hh => hident_pt h x hh))
  set η : ℝ := δ - (δ₁ + eps) with hηdef
  have hηpos : 0 < η := by
    rw [hηdef]; linarith
  have hb_toReal_pos : 0 < b.toReal := ENNReal.toReal_pos hb_ne_zero hb_ne_top
  have hev : ∀ᶠ n : ℕ in atTop, Real.exp (-(n : ℝ) * η) ≤ b.toReal := by
    obtain ⟨N₀, hN₀⟩ := exists_nat_ge (-(Real.log b.toReal) / η)
    refine eventually_atTop.2 ⟨N₀, fun n hn => ?_⟩
    have hn' : (-(Real.log b.toReal) / η) ≤ (n : ℝ) := le_trans hN₀ (by exact_mod_cast hn)
    have h1 : -(Real.log b.toReal) ≤ (n : ℝ) * η := by
      have h2 := mul_le_mul_of_nonneg_right hn' (le_of_lt hηpos)
      rwa [div_mul_cancel₀ _ (ne_of_gt hηpos)] at h2
    have h3 : Real.exp (-(n : ℝ) * η) ≤ Real.exp (Real.log b.toReal) := by
      apply Real.exp_le_exp.2
      have hrs : -(n : ℝ) * η = -((n : ℝ) * η) := by ring
      rw [hrs]
      linarith
    rwa [Real.exp_log hb_toReal_pos] at h3
  filter_upwards [hcore, hident] with x hxcore hxident
  obtain ⟨N₁, hN₁⟩ := hxcore
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 hev
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have hn₁ : N₁ ≤ n := le_trans (le_max_left N₁ N₂) hn
  have hn₂ : N₂ ≤ n := le_trans (le_max_right N₁ N₂) hn
  have hstep : ENNReal.ofReal (Real.exp (-(n : ℝ) * δ))
      ≤ b * ENNReal.ofReal (Real.exp (-(n : ℝ) * (δ₁ + eps))) := by
    rw [← ENNReal.ofReal_toReal hb_ne_top, ← ENNReal.ofReal_mul (le_of_lt hb_toReal_pos)]
    apply ENNReal.ofReal_le_ofReal
    have hsplit : -(n : ℝ) * δ = -(n : ℝ) * (δ₁ + eps) + -(n : ℝ) * η := by
      rw [hηdef]; ring
    calc Real.exp (-(n : ℝ) * δ)
        = Real.exp (-(n : ℝ) * (δ₁ + eps)) * Real.exp (-(n : ℝ) * η) := by
          rw [hsplit, Real.exp_add]
      _ ≤ Real.exp (-(n : ℝ) * (δ₁ + eps)) * b.toReal :=
          mul_le_mul_of_nonneg_left (hN₂ n hn₂) (le_of_lt (Real.exp_pos _))
      _ = b.toReal * Real.exp (-(n : ℝ) * (δ₁ + eps)) := mul_comm _ _
  have hcongr : (∫⁻ h, ENNReal.ofReal (Real.exp (∑ i ∈ Finset.range n, g h (x i))) ∂ν)
      = ∫⁻ h, ∏ i ∈ Finset.range n, (dens h (x i) * (p0 (x i))⁻¹) ∂ν :=
    lintegral_congr_ae (hxident.mono fun h hh => (hh n).symm)
  calc ENNReal.ofReal (Real.exp (-(n : ℝ) * δ))
      ≤ b * ENNReal.ofReal (Real.exp (-(n : ℝ) * (δ₁ + eps))) := hstep
    _ ≤ b * (∫⁻ h, ENNReal.ofReal (Real.exp (∑ i ∈ Finset.range n, g h (x i))) ∂ν) :=
        mul_le_mul_left' (hN₁ n hn₁) b
    _ = b * (∫⁻ h, ∏ i ∈ Finset.range n, (dens h (x i) * (p0 (x i))⁻¹) ∂ν) := by
        rw [hcongr]
    _ = ∫⁻ h, ∏ i ∈ Finset.range n, (dens h (x i) * (p0 (x i))⁻¹) ∂(b • ν) :=
        (hsmulInt _).symm
    _ = ∫⁻ h, ∏ i ∈ Finset.range n, (dens h (x i) * (p0 (x i))⁻¹) ∂(PiPrior.restrict Kset) := by
        rw [hbν]
    _ = ∫⁻ h in Kset, ∏ i ∈ Finset.range n, (dens h (x i) * (p0 (x i))⁻¹) ∂PiPrior := rfl
    _ ≤ ∫⁻ h, ∏ i ∈ Finset.range n, (dens h (x i) * (p0 (x i))⁻¹) ∂PiPrior := by
        rw [← lintegral_indicator hK_meas]
        exact lintegral_mono (fun h => Set.indicator_le_self Kset _ h)
  /- @proof-region region.target-node.session.2d97536fa28e7d13 end -/



#print axioms generic_KL_evidence

/-- Exact finite-cylinder law, independent of model representations. -/
theorem finite_prefix_law {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (n : ℕ) :
    Measure.pi (fun _ : Fin n => P) =
      Measure.map (fun x : ℕ → X => fun i : Fin n => x (i : ℕ))
        (Measure.infinitePi (fun _ : ℕ => P)) := by
refine Measure.pi_eq (fun s hs => ?_)
have hT : Measurable (fun x : ℕ → X => fun i : Fin n => x (i : ℕ)) := by
  rw [measurable_pi_iff]
  exact fun i => measurable_pi_apply (i : ℕ)
have hS : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
rw [Measure.map_apply hT hS]
have hset : (fun x : ℕ → X => fun i : Fin n => x (i : ℕ)) ⁻¹' (Set.univ.pi s)
    = Set.pi (((Finset.range n : Finset ℕ)) : Set ℕ)
        (fun k => if h : k < n then s ⟨k, h⟩ else Set.univ) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Finset.mem_range]
  constructor
  · intro hx k hk
    rw [dif_pos hk]
    exact hx ⟨k, hk⟩ (Set.mem_univ _)
  · intro hx i _
    have h := hx (i : ℕ) i.isLt
    rw [dif_pos i.isLt] at h
    exact h
rw [hset]
rw [Measure.infinitePi_pi]
· refine Finset.prod_bij
    (fun (k : ℕ) (hk : k ∈ Finset.range n) => (⟨k, Finset.mem_range.mp hk⟩ : Fin n))
    ?_ ?_ ?_ ?_
  · intro a _
    exact Finset.mem_univ _
  · intro a₁ _ a₂ _ h
    simpa using h
  · intro b _
    exact ⟨(b : ℕ), Finset.mem_range.mpr b.isLt, rfl⟩
  · intro a ha
    simp only [dif_pos (Finset.mem_range.mp ha)]
· intro k _
  by_cases h : k < n
  · rw [dif_pos h]
    exact hs ⟨k, h⟩
  · rw [dif_neg h]
    exact MeasurableSet.univ

/-- Generic proper-parameter KL support makes normalized evidence bad events vanish. -/
theorem generic_KL_bad_probability {X H : Type*} [MeasurableSpace X] [MeasurableSpace H]
    (μ : Measure X) [SigmaFinite μ]
    (p0 : X → ℝ≥0∞) (hp0 : Measurable p0) (hp0_int : ∫⁻ x, p0 x ∂μ = 1)
    (PiPrior : Measure H) [IsProbabilityMeasure PiPrior]
    (dens : H → X → ℝ≥0∞) (hdens : Measurable (Function.uncurry dens))
    (hdens_lt_top : ∀ h : H, ∀ᵐ x ∂μ, dens h x ≠ ⊤)
    (hdens_norm : ∀ᵐ h ∂PiPrior, ∫⁻ x, dens h x ∂μ ≤ 1)
    (hKL_pos : ∀ delta : ℝ, 0 < delta →
      0 < PiPrior {h : H |
        InformationTheory.klDiv (μ.withDensity p0) (μ.withDensity (dens h))
          < ENNReal.ofReal delta}) (delta : ℝ) (hdelta : 0 < delta) :
    Tendsto (fun n : ℕ => (Measure.pi (fun _ : Fin n => μ.withDensity p0))
      {xs : Fin n → X | (∫⁻ h, ∏ i : Fin n,
        (dens h (xs i) * (p0 (xs i))⁻¹) ∂PiPrior) <
          ENNReal.ofReal (Real.exp (-(n : ℝ) * delta))}) atTop (𝓝 0) := by
  classical
  let P := μ.withDensity p0
  haveI : IsProbabilityMeasure P := ⟨by
    dsimp only [P]
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hp0_int]⟩
  let W : (n : ℕ) → (Fin n → X) → ℝ≥0∞ := fun n xs =>
    ∫⁻ h, ∏ i : Fin n, (dens h (xs i) * (p0 (xs i))⁻¹) ∂PiPrior
  have hW : ∀ n, Measurable (W n) := by
    intro n
    have hjoint : Measurable (Function.uncurry (fun h : H => fun xs : Fin n → X =>
        ∏ i : Fin n, (dens h (xs i) * (p0 (xs i))⁻¹))) := by
      apply Finset.measurable_prod
      intro i hi
      exact (hdens.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))).mul
        ((hp0.comp ((measurable_pi_apply i).comp measurable_snd)).inv)
    exact hjoint.lintegral_prod_left
  let E : ℕ → Set (ℕ → X) := fun n =>
    {x | W n (fun i => x (i : ℕ)) < ENNReal.ofReal (Real.exp (-(n : ℝ) * delta))}
  have hE : ∀ n, MeasurableSet (E n) := by
    intro n
    exact measurableSet_lt ((hW n).comp (measurable_pi_lambda _
      (fun i => measurable_pi_apply (i : ℕ)))) measurable_const
  have hevent := generic_KL_evidence μ p0 hp0 hp0_int PiPrior dens hdens
    hdens_lt_top hdens_norm hKL_pos delta hdelta
  have hrepr : ∀ n (x : ℕ → X), W n (fun i => x (i : ℕ)) =
      ∫⁻ h, ∏ i ∈ Finset.range n, (dens h (x i) * (p0 (x i))⁻¹) ∂PiPrior := by
    intro n x
    apply lintegral_congr
    intro h
    exact Fin.prod_univ_eq_prod_range (fun i => dens h (x i) * (p0 (x i))⁻¹) n
  have hAE : ∀ᵐ x ∂(Measure.infinitePi (fun _ : ℕ => P)),
      ∀ᶠ n in atTop, x ∈ E n ↔ x ∈ (∅ : Set (ℕ → X)) := by
    filter_upwards [hevent] with x hx
    obtain ⟨N, hN⟩ := hx
    filter_upwards [eventually_ge_atTop N] with n hn
    simp only [E, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    rw [hrepr]
    exact hN n hn
  have hlim := tendsto_measure_of_ae_tendsto_indicator atTop MeasurableSet.empty hE
    MeasurableSet.univ (measure_ne_top _ Set.univ)
    (Filter.Eventually.of_forall (fun n => Set.subset_univ (E n))) hAE
  simp only [measure_empty] at hlim
  have hproj : ∀ n, (Measure.infinitePi (fun _ : ℕ => P)) (E n) =
      (Measure.pi (fun _ : Fin n => P))
        {xs | W n xs < ENNReal.ofReal (Real.exp (-(n : ℝ) * delta))} := by
    intro n
    rw [finite_prefix_law P n]
    have hprefix : Measurable (fun x : ℕ → X => fun i : Fin n => x (i : ℕ)) :=
      measurable_pi_lambda _ (fun i => measurable_pi_apply (i : ℕ))
    have hS : MeasurableSet {xs : Fin n → X |
        W n xs < ENNReal.ofReal (Real.exp (-(n : ℝ) * delta))} :=
      measurableSet_lt (hW n) measurable_const
    exact (Measure.map_apply hprefix hS).symm
  simpa only [hproj, W, P] using hlim

#print axioms generic_KL_bad_probability

end OfflineDPEvidence
