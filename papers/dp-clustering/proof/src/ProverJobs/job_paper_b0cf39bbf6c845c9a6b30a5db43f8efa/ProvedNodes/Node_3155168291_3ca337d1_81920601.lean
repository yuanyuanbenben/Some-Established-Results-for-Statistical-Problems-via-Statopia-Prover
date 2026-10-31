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

end Statlib.Imported
