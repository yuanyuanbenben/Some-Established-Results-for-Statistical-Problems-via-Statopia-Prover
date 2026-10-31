import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q09.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q09.Base

open MeasureTheory ProbabilityTheory
open Msc62GroundTruth

open MeasureTheory ProbabilityTheory
namespace Msc62GroundTruth

set_option autoImplicit false in
theorem statopia_math_node_2073386701_8222945a : ∀ (d : ℕ) (alpha : ℝ) (halpha : 0 < alpha)
    (n : ℕ) (hn : 1 ≤ n)
    (h : ℝ) (hh : h = Real.rpow (n : ℝ) (-1 / (2 * alpha + (d : ℝ))))
    (f0 : Cube d → ℝ) (K : ℝ → Cube d → Cube d → ℝ)
    (muU : Measure (Cube d)) [IsProbabilityMeasure muU]
    (hmuU : muU {x | InUnitCube x} = 1)
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (g : Cube d → Omega → ℝ)
    (L0 MK MAlpha : ℝ) (hL0 : 0 ≤ L0) (hMK : 0 ≤ MK)
    (h_pos : 0 < h)
    (f0_bounded : ∃ M : ℝ, 0 < M ∧ ∀ x, InUnitCube x → |f0 x| ≤ M)
    (holder : ∀ x y, InUnitCube x → InUnitCube y →
      |f0 x - f0 y| ≤ L0 * ‖x - y‖ ^ alpha)
    (product_kernel : ∃ k : ℝ → ℝ, Measurable k ∧ (∀ u, |k u| ≤ MK) ∧
      ∀ x z, InUnitCube x → InUnitCube z →
        K h x z = (1 / h ^ d) * ∏ j : Fin d, k ((x j - z j) / h))
    (kernel_measurable : ∀ x, InUnitCube x → Measurable (K h x))
    (kernel_normalization : ∀ x, InInteriorBand h x → ∫ z, K h x z ∂muU = 1)
    (kernel_alpha_moment : ∀ x, InInteriorBand h x →
      ∫ z, |K h x z| * ‖x - z‖ ^ alpha ∂muU ≤ MAlpha * Real.rpow h alpha)
      (population_smoother_identity : ∀ x, InInteriorBand h x →
        (∫ omega, g x omega ∂P) = ∫ z, K h x z * f0 z ∂muU)
      (x : Cube d) (hx : InInteriorBand h x),
      |(∫ omega, g x omega ∂P) - f0 x| ≤ L0 * MAlpha * Real.rpow h alpha := by
  /- @proof-region region.target-node.session.ba7895cd760e76e9 begin -/
  intro d alpha halpha n hn h hh f0 K muU inst_muU hmuU Omega Omega_meas P P_prob g L0 MK MAlpha hL0 hMK h_pos f0_bounded holder product_kernel kernel_measurable kernel_normalization kernel_alpha_moment population_smoother_identity x hx
  have hx_cube : InUnitCube x := by
    intro j
    exact ⟨le_trans h_pos.le (hx j).1, le_trans (hx j).2 (by linarith)⟩
  rw [population_smoother_identity x hx]
  have hS_meas : MeasurableSet {z : Cube d | InUnitCube z} := by
    have hset : {z : Cube d | InUnitCube z} = ⋂ j : Fin d, {z | z j ∈ Set.Icc (0 : ℝ) 1} := by
      ext z
      simp only [Set.mem_setOf_eq, InUnitCube, Set.mem_iInter]
    rw [hset]
    exact MeasurableSet.iInter (fun j => measurableSet_Icc.preimage (measurable_pi_apply j))
  have haeU : ∀ᵐ z ∂muU, InUnitCube z := by
    rw [ae_iff]
    have hcomp : {z : Cube d | ¬ InUnitCube z} = {z : Cube d | InUnitCube z}ᶜ := by
      ext z; simp
    rw [hcomp, measure_compl hS_meas (measure_ne_top muU _), measure_univ, hmuU]
    simp
  have hIntK : Integrable (fun z => K h x z) muU := by
    obtain ⟨k, hk_meas, hk_bound, hk_prod⟩ := product_kernel
    refine Integrable.of_bound (kernel_measurable x hx_cube).aestronglyMeasurable (|1 / h ^ d| * MK ^ d) ?_
    filter_upwards [haeU] with z hz
    rw [hk_prod x z hx_cube hz, Real.norm_eq_abs, abs_mul, Finset.abs_prod]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    calc ∏ j : Fin d, |k ((x j - z j) / h)| ≤ ∏ _ : Fin d, MK := by
          apply Finset.prod_le_prod
          · intro j _; exact abs_nonneg _
          · intro j _; exact hk_bound _
      _ = MK ^ d := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hf0_cont : ContinuousOn f0 {z : Cube d | InUnitCube z} := by
    rw [Metric.continuousOn_iff]
    intro b hb eps heps
    refine ⟨(eps / (L0 + 1)) ^ (1 / alpha), ?_, ?_⟩
    · apply Real.rpow_pos_of_pos
      positivity
    · intro a ha hd
      have hδpow : ((eps / (L0 + 1)) ^ (1 / alpha)) ^ alpha = eps / (L0 + 1) := by
        rw [← Real.rpow_mul (show (0:ℝ) ≤ eps / (L0 + 1) by positivity), one_div,
          inv_mul_cancel₀ halpha.ne', Real.rpow_one]
      have hd' : dist b a < (eps / (L0 + 1)) ^ (1 / alpha) := by
        simpa only [dist_comm] using hd
      have hpowlt : (dist b a) ^ alpha < eps / (L0 + 1) := by
        have hlt := Real.rpow_lt_rpow (dist_nonneg : (0:ℝ) ≤ dist b a) hd' halpha
        rwa [hδpow] at hlt
      have key : dist (f0 b) (f0 a) < eps := by
        calc dist (f0 b) (f0 a) = |f0 b - f0 a| := by rw [dist_eq_norm, Real.norm_eq_abs]
          _ ≤ L0 * (dist b a) ^ alpha := by
              simpa only [dist_eq_norm] using holder b a hb ha
          _ ≤ L0 * (eps / (L0 + 1)) :=
              mul_le_mul_of_nonneg_left (le_of_lt hpowlt) hL0
          _ < eps := by
              have hpos : (0:ℝ) < L0 + 1 := by linarith
              rw [← mul_div_assoc, div_lt_iff₀ hpos]
              nlinarith [heps]
      simpa only [dist_comm] using key
  have hf0_ae : AEStronglyMeasurable f0 muU := by
    have hAS : AEStronglyMeasurable f0 (muU.restrict {z : Cube d | InUnitCube z}) :=
      hf0_cont.aestronglyMeasurable hS_meas
    have hind : AEStronglyMeasurable ({z : Cube d | InUnitCube z}.indicator f0) muU :=
      (aestronglyMeasurable_indicator_iff hS_meas).mpr hAS
    have heq : ({z : Cube d | InUnitCube z}.indicator f0) =ᵐ[muU] f0 := by
      filter_upwards [haeU] with z hz
      exact Set.indicator_of_mem (s := {z : Cube d | InUnitCube z}) (f := f0) hz
    exact hind.congr heq
  have hIntKf0 : Integrable (fun z => K h x z * f0 z) muU := by
    obtain ⟨k, hk_meas, hk_bound, hk_prod⟩ := product_kernel
    obtain ⟨M, hMpos, hM⟩ := f0_bounded
    refine Integrable.of_bound ((kernel_measurable x hx_cube).aestronglyMeasurable.mul hf0_ae) ((|1 / h ^ d| * MK ^ d) * M) ?_
    filter_upwards [haeU] with z hz
    rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_mul ?_ (hM z hz) (abs_nonneg _) (mul_nonneg (abs_nonneg _) (pow_nonneg hMK d))
    rw [hk_prod x z hx_cube hz, abs_mul, Finset.abs_prod]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    calc ∏ j : Fin d, |k ((x j - z j) / h)| ≤ ∏ _ : Fin d, MK := by
          apply Finset.prod_le_prod
          · intro j _; exact abs_nonneg _
          · intro j _; exact hk_bound _
      _ = MK ^ d := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hIntKf0x : Integrable (fun z => K h x z * f0 x) muU := hIntK.mul_const (f0 x)
  have hkey : ∫ z, K h x z * f0 z ∂muU - f0 x = ∫ z, K h x z * (f0 z - f0 x) ∂muU := by
    have hc : ∫ z, K h x z * f0 x ∂muU = f0 x := by
      rw [integral_mul_const, kernel_normalization x hx, one_mul]
    rw [show (fun z => K h x z * (f0 z - f0 x))
          = (fun z => K h x z * f0 z - K h x z * f0 x) from by funext z; ring]
    rw [integral_sub hIntKf0 hIntKf0x, hc]
  rw [hkey]
  have hdom : ∫ z, ‖K h x z * (f0 z - f0 x)‖ ∂muU
      ≤ ∫ z, |K h x z| * (L0 * ‖x - z‖ ^ alpha) ∂muU := by
    have hF_int : Integrable (fun z => ‖K h x z * (f0 z - f0 x)‖) muU := by
      have hd : Integrable (fun z => K h x z * f0 z - K h x z * f0 x) muU :=
        hIntKf0.sub hIntKf0x
      have hd2 : Integrable (fun z => K h x z * (f0 z - f0 x)) muU := by
        simpa only [mul_sub] using hd
      exact hd2.norm
    have hG_int : Integrable (fun z => |K h x z| * (L0 * ‖x - z‖ ^ alpha)) muU := by
      obtain ⟨k, hk_meas, hk_bound, hk_prod⟩ := product_kernel
      have hKabs : Measurable (fun z => |K h x z|) := (kernel_measurable x hx_cube).abs
      have hcont : Continuous (fun z : Cube d => ‖x - z‖ ^ alpha) :=
        (Real.continuous_rpow_const halpha.le).comp
          (continuous_norm.comp (continuous_const.sub continuous_id))
      have hmeas : AEStronglyMeasurable
          (fun z => |K h x z| * (L0 * ‖x - z‖ ^ alpha)) muU :=
        (hKabs.mul (hcont.measurable.const_mul L0)).aestronglyMeasurable
      refine Integrable.of_bound hmeas ((|1 / h ^ d| * MK ^ d) * L0) ?_
      filter_upwards [haeU] with z hz
      have hKbd : |K h x z| ≤ |1 / h ^ d| * MK ^ d := by
        rw [hk_prod x z hx_cube hz, abs_mul, Finset.abs_prod]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        calc ∏ j : Fin d, |k ((x j - z j) / h)| ≤ ∏ _ : Fin d, MK := by
              apply Finset.prod_le_prod
              · intro j _; exact abs_nonneg _
              · intro j _; exact hk_bound _
          _ = MK ^ d := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      have hnormle : ‖x - z‖ ≤ 1 := by
        rw [← dist_eq_norm, dist_pi_le_iff (by norm_num : (0:ℝ) ≤ 1)]
        intro j
        rw [Real.dist_eq]
        exact abs_le.mpr
          ⟨by linarith [(hx_cube j).1, (hz j).2], by linarith [(hz j).1, (hx_cube j).2]⟩
      have hpbd : ‖x - z‖ ^ alpha ≤ 1 := by
        calc ‖x - z‖ ^ alpha ≤ 1 ^ alpha :=
              Real.rpow_le_rpow (norm_nonneg _) hnormle halpha.le
          _ = 1 := Real.one_rpow alpha
      have hLbd : L0 * ‖x - z‖ ^ alpha ≤ L0 := by
        have h' := mul_le_mul_of_nonneg_left hpbd hL0
        rwa [mul_one] at h'
      have hnonneg : (0:ℝ) ≤ L0 * ‖x - z‖ ^ alpha :=
        mul_nonneg hL0 (Real.rpow_nonneg (norm_nonneg _) alpha)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) hnonneg)]
      exact mul_le_mul hKbd hLbd hnonneg (mul_nonneg (abs_nonneg _) (pow_nonneg hMK d))
    have hF_le_G : ∀ᵐ z ∂muU,
        ‖K h x z * (f0 z - f0 x)‖ ≤ |K h x z| * (L0 * ‖x - z‖ ^ alpha) := by
      filter_upwards [haeU] with z hz
      have hz_holder : |f0 z - f0 x| ≤ L0 * ‖x - z‖ ^ alpha := by
        have h' := holder x z hx_cube hz
        rwa [abs_sub_comm] at h'
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left hz_holder (abs_nonneg _)
    exact integral_mono_ae hF_int hG_int hF_le_G
  calc |∫ z, K h x z * (f0 z - f0 x) ∂muU|
      ≤ ∫ z, ‖K h x z * (f0 z - f0 x)‖ ∂muU := by
        simpa using norm_integral_le_integral_norm (fun z => K h x z * (f0 z - f0 x))
    _ ≤ ∫ z, |K h x z| * (L0 * ‖x - z‖ ^ alpha) ∂muU := hdom
    _ = L0 * ∫ z, |K h x z| * ‖x - z‖ ^ alpha ∂muU := by
        rw [show (fun z => |K h x z| * (L0 * ‖x - z‖ ^ alpha))
              = (fun z => L0 * (|K h x z| * ‖x - z‖ ^ alpha)) from by
          funext z; ring]
        exact integral_const_mul L0 (fun z => |K h x z| * ‖x - z‖ ^ alpha)
    _ ≤ L0 * (MAlpha * Real.rpow h alpha) :=
        mul_le_mul_of_nonneg_left (kernel_alpha_moment x hx) hL0
    _ = L0 * MAlpha * Real.rpow h alpha := by ring
  /- @proof-region region.target-node.session.ba7895cd760e76e9 end -/

end Msc62GroundTruth
