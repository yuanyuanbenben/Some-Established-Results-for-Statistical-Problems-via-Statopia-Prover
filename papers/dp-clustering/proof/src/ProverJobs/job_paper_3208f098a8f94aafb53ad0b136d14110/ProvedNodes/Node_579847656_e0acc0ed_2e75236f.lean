import Statlib.StatFoundation.BasicAnalysis.ENNRealBridge
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.Vocabulary
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.Base
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.ProvedNodes.Node_1445702134_3c8d3810_8f7a15fe
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.ProvedNodes.Node_2166343247_005d03d5_e190fc11


open MeasureTheory
open Statlib.Imported

noncomputable section
open MeasureTheory
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_579847656_e0acc0ed : ∀ (t : ℝ) (ht : 1 ≤ t)
    (s : ℝ) (hs : 1 ≤ s)
    (eps : ℝ) (heps : 0 < eps)
    (n : ℕ) (hn : 1 ≤ n)
    (pi : ℝ → ℝ) (hpi_meas : Measurable pi)
    (hpi_nonneg : ∀ alpha ∈ Set.Ioi (0 : ℝ), 0 ≤ pi alpha)
    (hint : Integrable (fun alpha : ℝ => alpha ^ (t + s - 1) * pi alpha)
      (volume.restrict (Set.Ioi (0 : ℝ)))),
    (∫ alpha in Set.Ioi eps, alpha ^ (t - 1) * pi alpha) *
        (∫ alpha in Set.Ioi eps, alpha ^ (t + s) / risingFac alpha n * pi alpha)
      ≤ (∫ alpha in Set.Ioi eps, alpha ^ (t + s - 1) * pi alpha) *
          (∫ alpha in Set.Ioi eps, alpha ^ t / risingFac alpha n * pi alpha) := by
  /- @proof-region region.target-node.session.8d2106c2f46bba35 begin -/
  intro t ht s hs eps heps n hn pi hpi_meas hpi_nonneg hint
  obtain ⟨hfac_pos, hfac_pow, hfac_fact, hfac_monoα, hfac_quot⟩ :=
    statopia_math_node_1445702134_3c8d3810
  have hR_pos : ∀ α : ℝ, 0 < α → 0 < risingFac α n := fun α hα => hfac_pos α n hα
  have hquot_anti : ∀ α β : ℝ, 0 < α → α ≤ β → β / risingFac β n ≤ α / risingFac α n := by
    intro α β hα hαβ
    exact (hfac_quot.2.2 n hn).2.1 hα (lt_of_lt_of_le hα hαβ) hαβ
  have hR_meas : Measurable fun α : ℝ => risingFac α n := by
    have h := Finset.measurable_prod (s := Finset.range n)
      (f := fun k : ℕ => fun α : ℝ => α + (k : ℝ)) (fun k _ => measurable_id.add_const (k : ℝ))
    simpa only [risingFac] using h
  set d : ℝ → ENNReal := fun α => ENNReal.ofReal (α ^ (t - 1) * pi α) with hd
  set ν : Measure ℝ := volume.restrict (Set.Ioi eps) with hν
  set μ : Measure ℝ := ν.withDensity d with hμ
  set f : ℝ → ℝ := fun α => max (α ^ s) 0 with hf
  set g : ℝ → ℝ := fun α => max (α / risingFac α n) 0 with hg
  have hf_meas : Measurable f := by
    rw [hf]
    measurability
  have hg_meas : Measurable g := by
    rw [hg]
    measurability
  have hf_nonneg : ∀ x, 0 ≤ f x := fun x => le_max_right _ _
  have hg_nonneg : ∀ x, 0 ≤ g x := fun x => le_max_right _ _
  have hp_meas : Measurable fun α : ℝ => α ^ (t - 1) := by
    have hc : Continuous fun α : ℝ => α ^ (t - 1) :=
      continuous_id.rpow_const fun x => Or.inr (by linarith)
    exact hc.measurable
  have hbase_meas : Measurable fun α : ℝ => α ^ (t - 1) * pi α := hp_meas.mul hpi_meas
  have hd_meas : Measurable d := by
    show Measurable fun α : ℝ => ENNReal.ofReal (α ^ (t - 1) * pi α)
    exact hbase_meas.ennreal_ofReal
  have hd_lt : ∀ᵐ x ∂ν, d x < ⊤ := Filter.Eventually.of_forall (fun x => by
    rw [hd]
    simp)

  have hae_mem : ∀ᵐ x ∂ν, x ∈ Set.Ioi eps := by
    rw [hν]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioi
  have hsub : Set.Ioi eps ∩ Set.Ioi (0 : ℝ) = Set.Ioi eps := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioi]
    exact ⟨fun h => h.1, fun h => ⟨h, lt_trans heps h⟩⟩
  have hν_le : ν ≤ volume.restrict (Set.Ioi (0 : ℝ)) := by
    have heq : ν = (volume.restrict (Set.Ioi (0 : ℝ))).restrict (Set.Ioi eps) := by
      rw [hν, MeasureTheory.Measure.restrict_restrict measurableSet_Ioi, hsub]
    rw [heq]
    exact MeasureTheory.Measure.restrict_le_self
  have hint_eps : Integrable (fun α : ℝ => α ^ (t + s - 1) * pi α) ν :=
    hint.mono_measure hν_le
  have hbase_int : Integrable (fun α : ℝ => α ^ (t - 1) * pi α) ν := by
    refine MeasureTheory.Integrable.mono' (hint_eps.const_mul (eps ^ (-s)))
      hbase_meas.aestronglyMeasurable ?_
    filter_upwards [hae_mem] with x hx
    have hx0 : 0 < x := lt_trans heps hx
    have hpix : 0 ≤ pi x := hpi_nonneg x hx0
    have hxn : 0 ≤ x ^ (t - 1) := Real.rpow_nonneg (le_of_lt hx0) _
    have hnn : 0 ≤ x ^ (t - 1) * pi x := mul_nonneg hxn hpix
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    have hxle : x ^ (-s) ≤ eps ^ (-s) :=
      Real.rpow_le_rpow_of_nonpos heps (le_of_lt hx) (by linarith)
    have hsplit : x ^ (t - 1) = x ^ (t + s - 1) * x ^ (-s) := by
      rw [← Real.rpow_add hx0]
      congr 1
      ring
    have h1 : 0 ≤ x ^ (t + s - 1) := Real.rpow_nonneg (le_of_lt hx0) _
    rw [hsplit]
    calc x ^ (t + s - 1) * x ^ (-s) * pi x
        = x ^ (t + s - 1) * pi x * x ^ (-s) := by ring
      _ ≤ x ^ (t + s - 1) * pi x * eps ^ (-s) :=
          mul_le_mul_of_nonneg_left hxle (mul_nonneg h1 hpix)
      _ = eps ^ (-s) * (x ^ (t + s - 1) * pi x) := by ring
  haveI hμ_fin : IsFiniteMeasure μ := by
    rw [hμ]
    exact MeasureTheory.isFiniteMeasure_withDensity_ofReal hbase_int.2
  have hq_le_one : ∀ x : ℝ, 0 < x → x / risingFac x n ≤ 1 := by
    intro x hx
    rw [(hfac_quot.2.2 n hn).2.2 x hx]
    have hP1 : (1 : ℝ) ≤ ∏ j ∈ Finset.range (n - 1), (x + ((j : ℝ) + 1)) := by
      have hpt : ∀ j ∈ Finset.range (n - 1), (1 : ℝ) ≤ x + ((j : ℝ) + 1) := by
        intro j hj
        have hj0 : (0 : ℝ) ≤ (j : ℝ) := by positivity
        linarith
      have hprod : (∏ j ∈ Finset.range (n - 1), (1 : ℝ))
          ≤ ∏ j ∈ Finset.range (n - 1), (x + ((j : ℝ) + 1)) :=
        Finset.prod_le_prod (fun i _ => zero_le_one) hpt
      simpa only [Finset.prod_const_one] using hprod
    have hle := one_div_le_one_div_of_le (a := (1 : ℝ))
      (b := ∏ j ∈ Finset.range (n - 1), (x + ((j : ℝ) + 1))) zero_lt_one hP1
    simpa using hle
  have hbase_le : ∀ x ∈ Set.Ioi eps, x ^ (t - 1) ≤ eps ^ (-s) * x ^ (t + s - 1) := by
    intro x hx
    have hx0 : 0 < x := lt_trans heps hx
    have hxle : x ^ (-s) ≤ eps ^ (-s) :=
      Real.rpow_le_rpow_of_nonpos heps (le_of_lt hx) (by linarith)
    have hsplit : x ^ (t - 1) = x ^ (t + s - 1) * x ^ (-s) := by
      rw [← Real.rpow_add hx0]
      congr 1
      ring
    rw [hsplit]
    calc x ^ (t + s - 1) * x ^ (-s)
        = x ^ (-s) * x ^ (t + s - 1) := by ring
      _ ≤ eps ^ (-s) * x ^ (t + s - 1) :=
          mul_le_mul_of_nonneg_right hxle (Real.rpow_nonneg (le_of_lt hx0) _)
  have hf_int : Integrable f μ := by
    rw [hμ, MeasureTheory.integrable_withDensity_iff hd_meas hd_lt]
    have hfun : Integrable (fun x : ℝ => f x * (x ^ (t - 1) * pi x)) ν := by
      refine MeasureTheory.Integrable.mono' (g := fun x : ℝ => x ^ (t + s - 1) * pi x) hint_eps
        (hf_meas.mul hbase_meas).aestronglyMeasurable ?_
      filter_upwards [hae_mem] with x hx
      have hx0 : 0 < x := lt_trans heps hx
      have hpix : 0 ≤ pi x := hpi_nonneg x hx0
      have hxpow : 0 ≤ x ^ (t - 1) := Real.rpow_nonneg (le_of_lt hx0) _
      have hfx : f x = x ^ s := by
        rw [hf]
        exact max_eq_left (Real.rpow_nonneg (le_of_lt hx0) s)
      rw [hfx]
      have hnn : 0 ≤ x ^ s * (x ^ (t - 1) * pi x) :=
        mul_nonneg (Real.rpow_nonneg (le_of_lt hx0) _) (mul_nonneg hxpow hpix)
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      have hmul : x ^ s * x ^ (t - 1) = x ^ (t + s - 1) := by
        rw [← Real.rpow_add hx0]
        congr 1
        ring
      rw [← hmul]
      exact le_of_eq (by ring)
    refine hfun.congr ?_
    filter_upwards [hae_mem] with x hx
    have hx0 : 0 < x := lt_trans heps hx
    have hpix : 0 ≤ pi x := hpi_nonneg x hx0
    have hdx : (d x).toReal = x ^ (t - 1) * pi x := by
      rw [hd]
      exact ENNReal.toReal_ofReal (mul_nonneg (Real.rpow_nonneg (le_of_lt hx0) _) hpix)
    rw [hdx]
  have hg_int : Integrable g μ := by
    rw [hμ, MeasureTheory.integrable_withDensity_iff hd_meas hd_lt]
    have hfun : Integrable (fun x : ℝ => g x * (x ^ (t - 1) * pi x)) ν := by
      refine MeasureTheory.Integrable.mono'
        (g := fun x : ℝ => eps ^ (-s) * (x ^ (t + s - 1) * pi x))
        (hint_eps.const_mul (eps ^ (-s))) (hg_meas.mul hbase_meas).aestronglyMeasurable ?_
      filter_upwards [hae_mem] with x hx
      have hx0 : 0 < x := lt_trans heps hx
      have hpix : 0 ≤ pi x := hpi_nonneg x hx0
      have hxpow : 0 ≤ x ^ (t - 1) := Real.rpow_nonneg (le_of_lt hx0) _
      have hqpos : 0 < x / risingFac x n := (hfac_quot.2.2 n hn).1 x hx0
      have hqle : x / risingFac x n ≤ 1 := hq_le_one x hx0
      have hgx : g x = x / risingFac x n := by
        rw [hg]
        exact max_eq_left (le_of_lt hqpos)
      rw [hgx]
      have hnn : 0 ≤ x / risingFac x n * (x ^ (t - 1) * pi x) :=
        mul_nonneg (le_of_lt hqpos) (mul_nonneg hxpow hpix)
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      have hbase_nn : 0 ≤ x ^ (t - 1) * pi x := mul_nonneg hxpow hpix
      calc x / risingFac x n * (x ^ (t - 1) * pi x)
          = (x ^ (t - 1) * pi x) * (x / risingFac x n) := by ring
        _ ≤ (x ^ (t - 1) * pi x) * 1 := mul_le_mul_of_nonneg_left hqle hbase_nn
        _ = x ^ (t - 1) * pi x := by ring
        _ ≤ (eps ^ (-s) * x ^ (t + s - 1)) * pi x :=
            mul_le_mul_of_nonneg_right (hbase_le x hx) hpix
        _ = eps ^ (-s) * (x ^ (t + s - 1) * pi x) := by ring
    refine hfun.congr ?_
    filter_upwards [hae_mem] with x hx
    have hx0 : 0 < x := lt_trans heps hx
    have hpix : 0 ≤ pi x := hpi_nonneg x hx0
    have hdx : (d x).toReal = x ^ (t - 1) * pi x := by
      rw [hd]
      exact ENNReal.toReal_ofReal (mul_nonneg (Real.rpow_nonneg (le_of_lt hx0) _) hpix)
    rw [hdx]
  have hfg_int : Integrable (fun x => f x * g x) μ := by
    rw [hμ, MeasureTheory.integrable_withDensity_iff hd_meas hd_lt]
    have hfun : Integrable (fun x : ℝ => f x * g x * (x ^ (t - 1) * pi x)) ν := by
      refine MeasureTheory.Integrable.mono' (g := fun x : ℝ => x ^ (t + s - 1) * pi x) hint_eps
        ((hf_meas.mul hg_meas).mul hbase_meas).aestronglyMeasurable ?_
      filter_upwards [hae_mem] with x hx
      have hx0 : 0 < x := lt_trans heps hx
      have hpix : 0 ≤ pi x := hpi_nonneg x hx0
      have hxpow : 0 ≤ x ^ (t - 1) := Real.rpow_nonneg (le_of_lt hx0) _
      have hqpos : 0 < x / risingFac x n := (hfac_quot.2.2 n hn).1 x hx0
      have hqle : x / risingFac x n ≤ 1 := hq_le_one x hx0
      have hfx : f x = x ^ s := by
        rw [hf]
        exact max_eq_left (Real.rpow_nonneg (le_of_lt hx0) s)
      have hgx : g x = x / risingFac x n := by
        rw [hg]
        exact max_eq_left (le_of_lt hqpos)
      rw [hfx, hgx]
      have hnn : 0 ≤ x ^ s * (x / risingFac x n) * (x ^ (t - 1) * pi x) :=
        mul_nonneg (mul_nonneg (Real.rpow_nonneg (le_of_lt hx0) _) (le_of_lt hqpos))
          (mul_nonneg hxpow hpix)
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      have hmul : x ^ s * x ^ (t - 1) = x ^ (t + s - 1) := by
        rw [← Real.rpow_add hx0]
        congr 1
        ring
      have hA : 0 ≤ x ^ (t + s - 1) := Real.rpow_nonneg (le_of_lt hx0) _
      calc x ^ s * (x / risingFac x n) * (x ^ (t - 1) * pi x)
          = x ^ (t + s - 1) * (x / risingFac x n) * pi x := by
            rw [← hmul]
            ring
        _ ≤ x ^ (t + s - 1) * 1 * pi x := by
            apply mul_le_mul_of_nonneg_right _ hpix
            exact mul_le_mul_of_nonneg_left hqle hA
        _ = x ^ (t + s - 1) * pi x := by ring
    refine hfun.congr ?_
    filter_upwards [hae_mem] with x hx
    have hx0 : 0 < x := lt_trans heps hx
    have hpix : 0 ≤ pi x := hpi_nonneg x hx0
    have hdx : (d x).toReal = x ^ (t - 1) * pi x := by
      rw [hd]
      exact ENNReal.toReal_ofReal (mul_nonneg (Real.rpow_nonneg (le_of_lt hx0) _) hpix)
    rw [hdx]
  have hanti : ∀ᵐ p ∂(μ.prod μ), (f p.1 - f p.2) * (g p.1 - g p.2) ≤ 0 := by
    have hμ_supp : ∀ᵐ x ∂μ, x ∈ Set.Ioi eps := by
      rw [hμ]
      exact (MeasureTheory.ae_withDensity_iff hd_meas).mpr (hae_mem.mono (fun x hx _ => hx))
    have hmeas : MeasurableSet {z : ℝ × ℝ | z.1 ∈ Set.Ioi eps ∧ z.2 ∈ Set.Ioi eps} :=
      (measurable_fst measurableSet_Ioi).inter (measurable_snd measurableSet_Ioi)
    have hboth : ∀ᵐ p ∂(μ.prod μ), p.1 ∈ Set.Ioi eps ∧ p.2 ∈ Set.Ioi eps := by
      refine (MeasureTheory.Measure.ae_prod_iff_ae_ae hmeas).mpr ?_
      filter_upwards [hμ_supp] with x hx
      filter_upwards [hμ_supp] with y hy
      exact ⟨hx, hy⟩
    filter_upwards [hboth] with p hp
    have hx0 : 0 < p.1 := lt_trans heps hp.1
    have hy0 : 0 < p.2 := lt_trans heps hp.2
    have hfx : f p.1 = p.1 ^ s := by
      rw [hf]
      exact max_eq_left (Real.rpow_nonneg (le_of_lt hx0) s)
    have hfy : f p.2 = p.2 ^ s := by
      rw [hf]
      exact max_eq_left (Real.rpow_nonneg (le_of_lt hy0) s)
    have hgx : g p.1 = p.1 / risingFac p.1 n := by
      rw [hg]
      exact max_eq_left (le_of_lt ((hfac_quot.2.2 n hn).1 p.1 hx0))
    have hgy : g p.2 = p.2 / risingFac p.2 n := by
      rw [hg]
      exact max_eq_left (le_of_lt ((hfac_quot.2.2 n hn).1 p.2 hy0))
    rw [hfx, hfy, hgx, hgy]
    rcases le_total p.1 p.2 with hle | hle
    · have h1 : p.1 ^ s ≤ p.2 ^ s := Real.rpow_le_rpow (le_of_lt hx0) hle (by linarith)
      have h2 : p.2 / risingFac p.2 n ≤ p.1 / risingFac p.1 n := hquot_anti p.1 p.2 hx0 hle
      nlinarith
    · have h1 : p.2 ^ s ≤ p.1 ^ s := Real.rpow_le_rpow (le_of_lt hy0) hle (by linarith)
      have h2 : p.1 / risingFac p.1 n ≤ p.2 / risingFac p.2 n := hquot_anti p.2 p.1 hy0 hle
      nlinarith
  have hnn_base : 0 ≤ᶠ[ae ν] fun x : ℝ => x ^ (t - 1) * pi x := by
    filter_upwards [hae_mem] with x hx
    exact mul_nonneg (Real.rpow_nonneg (le_of_lt (lt_trans heps hx)) _)
      (hpi_nonneg x (lt_trans heps hx))
  have hI0 : (μ Set.univ).toReal = ∫ α in Set.Ioi eps, α ^ (t - 1) * pi α := by
    have hstep : (∫⁻ x, d x ∂ν).toReal = ∫ α in Set.Ioi eps, α ^ (t - 1) * pi α := by
      rw [hd]
      exact Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.lintegral_toReal_eq_integral_of_nonneg
        hnn_base hbase_int
    have huniv : (μ Set.univ).toReal = (∫⁻ x, d x ∂ν).toReal := by
      rw [hμ, MeasureTheory.withDensity_apply' d Set.univ]
      simp
    rw [huniv, hstep]
  have hgen : ∀ h : ℝ → ℝ, ∫ x, h x ∂μ = ∫ x, h x * (x ^ (t - 1) * pi x) ∂ν := by
    intro h
    rw [hμ, integral_withDensity_eq_integral_toReal_smul hd_meas hd_lt h]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hae_mem] with x hx
    have hx0 : 0 < x := lt_trans heps hx
    have hpix : 0 ≤ pi x := hpi_nonneg x hx0
    have hdx : (d x).toReal = x ^ (t - 1) * pi x := by
      rw [hd]
      exact ENNReal.toReal_ofReal (mul_nonneg (Real.rpow_nonneg (le_of_lt hx0) _) hpix)
    rw [hdx, smul_eq_mul, mul_comm]
  have hI1 : (∫ x, f x ∂μ) = ∫ α in Set.Ioi eps, α ^ (t + s - 1) * pi α := by
    rw [hgen f]
    refine MeasureTheory.setIntegral_congr_ae measurableSet_Ioi (Filter.Eventually.of_forall ?_)
    intro x hx
    have hx0 : 0 < x := lt_trans heps hx
    have hfx : f x = x ^ s := by
      rw [hf]
      exact max_eq_left (Real.rpow_nonneg (le_of_lt hx0) s)
    rw [hfx]
    have hmul : x ^ s * x ^ (t - 1) = x ^ (t + s - 1) := by
      rw [← Real.rpow_add hx0]
      congr 1
      ring
    rw [← hmul]
    ring
  have hI2 : (∫ x, g x ∂μ) = ∫ α in Set.Ioi eps, α ^ t / risingFac α n * pi α := by
    rw [hgen g]
    refine MeasureTheory.setIntegral_congr_ae measurableSet_Ioi (Filter.Eventually.of_forall ?_)
    intro x hx
    have hx0 : 0 < x := lt_trans heps hx
    have hqpos : 0 < x / risingFac x n := (hfac_quot.2.2 n hn).1 x hx0
    have hgx : g x = x / risingFac x n := by
      rw [hg]
      exact max_eq_left (le_of_lt hqpos)
    rw [hgx]
    have hone : x ^ (t - 1) * x = x ^ t := by
      rw [← Real.rpow_add_one (ne_of_gt hx0)]
      congr 1
      ring
    rw [← hone]
    ring
  have hI3 : (∫ x, f x * g x ∂μ) = ∫ α in Set.Ioi eps, α ^ (t + s) / risingFac α n * pi α := by
    rw [hgen (fun x => f x * g x)]
    refine MeasureTheory.setIntegral_congr_ae measurableSet_Ioi (Filter.Eventually.of_forall ?_)
    intro x hx
    have hx0 : 0 < x := lt_trans heps hx
    have hqpos : 0 < x / risingFac x n := (hfac_quot.2.2 n hn).1 x hx0
    have hfx : f x = x ^ s := by
      rw [hf]
      exact max_eq_left (Real.rpow_nonneg (le_of_lt hx0) s)
    have hgx : g x = x / risingFac x n := by
      rw [hg]
      exact max_eq_left (le_of_lt hqpos)
    rw [hfx, hgx]
    have hmul : x ^ s * x ^ (t - 1) = x ^ (t + s - 1) := by
      rw [← Real.rpow_add hx0]
      congr 1
      ring
    have hone : x ^ (t + s - 1) * x = x ^ (t + s) := by
      rw [← Real.rpow_add_one (ne_of_gt hx0)]
      congr 1
      ring
    rw [← hone, ← hmul]
    ring
  have hcheb := statopia_math_node_2166343247_005d03d5 μ f g hf_nonneg hg_nonneg hf_meas hg_meas
    hf_int hg_int hfg_int hanti
  rw [hI0, hI1, hI2, hI3] at hcheb
  exact hcheb
  /- @proof-region region.target-node.session.8d2106c2f46bba35 end -/

end Statlib.Imported
end
