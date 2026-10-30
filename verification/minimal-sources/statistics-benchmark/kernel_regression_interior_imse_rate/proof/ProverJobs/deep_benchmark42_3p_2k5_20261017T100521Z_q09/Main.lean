import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q09.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q09.ProvedNodes
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q09.Base

open MeasureTheory ProbabilityTheory
namespace Msc62GroundTruth

theorem kernel_regression_interior_imse_rate
    (d : ℕ) (hd : 1 ≤ d)
    (alpha : ℝ) (halpha : 0 < alpha)
    (nu b : ℝ) (hnu : 0 < nu) (hb : 0 < b)
    (L0 MK LK gamma MAlpha Cv : ℝ)
    (hL0 : 0 ≤ L0) (hMK : 0 ≤ MK) (hLK : 0 ≤ LK)
    (hgamma : 0 < gamma) (hMAlpha : 0 ≤ MAlpha) (hCv : 0 ≤ Cv) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f0 : Cube d → ℝ)
        (K : ℝ → Cube d → Cube d → ℝ)
        (muU : Measure (Cube d)) [IsProbabilityMeasure muU]
        (h_uniform : IsUniformOnUnitCube muU)
        {Omega : Type*} [MeasurableSpace Omega]
        (P : Measure Omega) [IsProbabilityMeasure P]
        (n : ℕ) (hn : 1 ≤ n)
        (X : Fin n → Omega → Cube d)
        (Y xi : Fin n → Omega → ℝ)
        (muI : Measure (Cube d)) [IsFiniteMeasure muI]
        (hX_meas : ∀ i, Measurable (X i))
        (hX_cube : ∀ i omega, InUnitCube (X i omega))
        (hX_law : ∀ i, Measure.map (X i) P = muU)
        (hY_meas : ∀ i, Measurable (Y i))
        (hxi_meas : ∀ i, Measurable (xi i))
        (hxi_integrable : ∀ i, Integrable (xi i) P)
        (h_regression_model : ∀ i omega,
          Y i omega = f0 (X i omega) + xi i omega)
        (hxi_centered : ∀ i, ∫ omega, xi i omega ∂P = 0)
        (hxi_exp_integrable : ∀ (i : Fin n) (t : ℝ), |t| < 1 / b →
          Integrable (fun omega => Real.exp (t * xi i omega)) P)
        (hxi_subexponential : ∀ (i : Fin n) (t : ℝ), |t| < 1 / b →
          ∫ omega, Real.exp (t * xi i omega) ∂P ≤
            Real.exp (nu ^ 2 * t ^ 2 / (2 * (1 - b * |t|))))
        (h_package : KernelRiskPackage P d n alpha
          (Real.rpow (n : ℝ) (-1 / (2 * alpha + (d : ℝ))))
          f0 K muU muI
          (fun x omega =>
            (1 / (n : ℝ)) * ∑ i : Fin n,
              K (Real.rpow (n : ℝ) (-1 / (2 * alpha + (d : ℝ))))
                x (X i omega) * Y i omega)
          L0 MK LK gamma MAlpha Cv),
        let h : ℝ := Real.rpow (n : ℝ) (-1 / (2 * alpha + (d : ℝ)))
        let I_h : Set (Cube d) := {x | InInteriorBand h x}
        let estimator (x : Cube d) (omega : Omega) : ℝ :=
          (1 / (n : ℝ)) * ∑ i : Fin n, K h x (X i omega) * Y i omega
        (∫ x in I_h,
          ∫ omega, (estimator x omega - f0 x) ^ 2 ∂P ∂muI) ≤
          C * Real.rpow (n : ℝ)
            (-2 * alpha / (2 * alpha + (d : ℝ)))
:= by
  /- @proof-region region.root.d6108a46516c begin -/
  refine ⟨1 + (L0 * MAlpha) ^ 2 + Cv, by nlinarith [sq_nonneg (L0 * MAlpha)], ?_⟩
  intro f0 K muU hmuU h_uniform Omega hOmega P hP n hn X Y xi muI hmuI
    hX_meas hX_cube hX_law hY_meas hxi_meas hxi_integrable h_regression_model
    hxi_centered hxi_exp_integrable hxi_subexponential h_package
  haveI := hmuU
  haveI := hP
  haveI := hmuI
  dsimp only
  set h : ℝ := Real.rpow (n : ℝ) (-1 / (2 * alpha + (d : ℝ))) with hh
  
  have hn0 : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hd0 : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hd
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
  have hh_pos : 0 < h := h_package.h_pos
  have hden_pos : 0 < 2 * alpha + (d : ℝ) := by linarith
  let g : Cube d → Omega → ℝ :=
    fun x omega => (1 / (n : ℝ)) * ∑ i : Fin n, K h x (X i omega) * Y i omega
  have hband_cube : ∀ x : Cube d, InInteriorBand h x → InUnitCube x := by
    intro x hx j
    exact ⟨le_trans (le_of_lt hh_pos) (hx j).1, by linarith [(hx j).2, hh_pos]⟩
  have hpow_d : h ^ d = Real.rpow h (d : ℝ) := (Real.rpow_natCast h d).symm
  have hexp1 : (-1 / (2 * alpha + (d : ℝ))) * (d : ℝ)
      = -(d : ℝ) / (2 * alpha + (d : ℝ)) := by ring
  have h_hd_eq : h ^ d =
      Real.rpow (n : ℝ) ((-1 / (2 * alpha + (d : ℝ))) * (d : ℝ)) := by
    rw [hpow_d, hh]
    change ((n : ℝ) ^ (-1 / (2 * alpha + (d : ℝ)))) ^ (d : ℝ)
      = (n : ℝ) ^ ((-1 / (2 * alpha + (d : ℝ))) * (d : ℝ))
    rw [← Real.rpow_mul (le_of_lt hn_pos)]
  have h_n_mul : (n : ℝ) * h ^ d =
      Real.rpow (n : ℝ) ((2 * alpha) / (2 * alpha + (d : ℝ))) := by
    have hd_eq : h ^ d =
        Real.rpow (n : ℝ) (-(d : ℝ) / (2 * alpha + (d : ℝ))) := by
      rw [h_hd_eq, hexp1]
    rw [hd_eq]
    change (n : ℝ) * (n : ℝ) ^ (-(d : ℝ) / (2 * alpha + (d : ℝ)))
      = (n : ℝ) ^ ((2 * alpha) / (2 * alpha + (d : ℝ)))
    have hexp2 : (1 : ℝ) + (-(d : ℝ) / (2 * alpha + (d : ℝ)))
        = (2 * alpha) / (2 * alpha + (d : ℝ)) := by
      have hX : (2 * alpha + (d : ℝ)) ≠ 0 := ne_of_gt hden_pos
      have hX' : (↑d + alpha * 2) ≠ 0 := by
        rw [show (↑d + alpha * 2 : ℝ) = 2 * alpha + (d : ℝ) from by ring]
        exact ne_of_gt hden_pos
      field_simp
      ring
    have hkey : (n : ℝ) ^ (1 : ℝ) *
          (n : ℝ) ^ (-(d : ℝ) / (2 * alpha + (d : ℝ)))
        = (n : ℝ) ^ ((2 * alpha) / (2 * alpha + (d : ℝ))) := by
      rw [← Real.rpow_add hn_pos, hexp2]
    rw [← hkey]
    rw [Real.rpow_one]
  have h_bw : 1 / ((n : ℝ) * h ^ d) = Real.rpow h (2 * alpha) := by
    rw [h_n_mul]
    change 1 / (n : ℝ) ^ ((2 * alpha) / (2 * alpha + (d : ℝ)))
      = h ^ (2 * alpha)
    rw [one_div]
    change ((n : ℝ) ^ ((2 * alpha) / (2 * alpha + (d : ℝ))))⁻¹ = h ^ (2 * alpha)
    rw [← Real.rpow_neg (le_of_lt hn_pos)]
    change (n : ℝ) ^ (-((2 * alpha) / (2 * alpha + (d : ℝ)))) = h ^ (2 * alpha)
    rw [hh]
    change (n : ℝ) ^ (-((2 * alpha) / (2 * alpha + (d : ℝ))))
      = ((n : ℝ) ^ (-1 / (2 * alpha + (d : ℝ)))) ^ (2 * alpha)
    rw [← Real.rpow_mul (le_of_lt hn_pos)]
    congr 1
    ring
  have hbw2 : Real.rpow h (2 * alpha) =
      Real.rpow (n : ℝ) (-2 * alpha / (2 * alpha + (d : ℝ))) := by
    rw [hh]
    change ((n : ℝ) ^ (-1 / (2 * alpha + (d : ℝ)))) ^ (2 * alpha)
      = (n : ℝ) ^ (-2 * alpha / (2 * alpha + (d : ℝ)))
    rw [← Real.rpow_mul (le_of_lt hn_pos)]
    congr 1
    ring
  have hcube_meas : MeasurableSet {x : Cube d | InUnitCube x} := by
    have hset : {x : Cube d | InUnitCube x}
        = ⋂ j : Fin d, ({x : Cube d | (0 : ℝ) ≤ x j} ∩ {x : Cube d | x j ≤ 1}) := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff, InUnitCube,
        Set.mem_Icc]
    rw [hset]
    exact MeasurableSet.iInter fun j =>
      (measurableSet_le measurable_const (measurable_pi_apply j)).inter
        (measurableSet_le (measurable_pi_apply j) measurable_const)
  have hband_meas : MeasurableSet {x : Cube d | InInteriorBand h x} := by
    have hset : {x : Cube d | InInteriorBand h x}
        = ⋂ j : Fin d, ({x : Cube d | h ≤ x j} ∩ {x : Cube d | x j ≤ 1 - h}) := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff, InInteriorBand]
    rw [hset]
    exact MeasurableSet.iInter fun j =>
      (measurableSet_le measurable_const (measurable_pi_apply j)).inter
        (measurableSet_le (measurable_pi_apply j) measurable_const)
  have hcube_ae : ∀ᵐ z ∂muU, InUnitCube z := by
    rw [MeasureTheory.ae_iff]
    have hc : {z : Cube d | ¬ InUnitCube z} = {z : Cube d | InUnitCube z}ᶜ := by
      ext z
      simp
    rw [hc, MeasureTheory.measure_compl hcube_meas (measure_ne_top muU _), h_uniform.1,
      measure_univ]
    simp
  have h_bias : ∀ x, InInteriorBand h x →
      |(∫ ω, g x ω ∂P) - f0 x| ≤ L0 * MAlpha * Real.rpow h alpha := by
    have hf0_cont : ContinuousOn f0 {y : Cube d | InUnitCube y} := by
      intro y hy
      rw [Metric.continuousWithinAt_iff]
      intro eps heps
      have hpos : 0 < eps / (2 * (L0 + 1)) := div_pos heps (by linarith)
      refine ⟨(eps / (2 * (L0 + 1))) ^ (1 / alpha),
        Real.rpow_pos_of_pos hpos _, ?_⟩
      intro z hz hdist
      have hδalpha : ((eps / (2 * (L0 + 1))) ^ (1 / alpha)) ^ alpha
          = eps / (2 * (L0 + 1)) := by
        rw [← Real.rpow_mul (le_of_lt hpos)]
        have hexp : 1 / alpha * alpha = 1 := by
          field_simp
        rw [hexp, Real.rpow_one]
      have hstep : ‖z - y‖ ^ alpha
          ≤ ((eps / (2 * (L0 + 1))) ^ (1 / alpha)) ^ alpha :=
        Real.rpow_le_rpow (norm_nonneg _) (le_of_lt hdist) (le_of_lt halpha)
      rw [hδalpha] at hstep
      have hb : |f0 z - f0 y| ≤ L0 * ‖z - y‖ ^ alpha := h_package.holder z y hz hy
      have hstep2 : L0 * (eps / (2 * (L0 + 1))) ≤ eps / 2 := by
        have hX : (0:ℝ) < 2 * (L0 + 1) := by linarith
        have hXne : (2 * (L0 + 1)) ≠ 0 := ne_of_gt hX
        have hEq : eps / 2 - L0 * (eps / (2 * (L0 + 1))) = eps / (2 * (L0 + 1)) := by
          field_simp
          ring
        have hpos2 : 0 < eps / (2 * (L0 + 1)) := div_pos heps hX
        linarith
      have hfin : |f0 z - f0 y| ≤ eps / 2 := by
        calc |f0 z - f0 y| ≤ L0 * ‖z - y‖ ^ alpha := hb
          _ ≤ L0 * (eps / (2 * (L0 + 1))) := mul_le_mul_of_nonneg_left hstep hL0
          _ ≤ eps / 2 := hstep2
      rw [Real.dist_eq]
      linarith
    intro x hx
    have hx_cube : InUnitCube x := hband_cube x hx
    obtain ⟨Mf, hMf_pos, hMf⟩ := h_package.f0_bounded
    obtain ⟨k, hk_meas, hk_abs, hk_lip, hK_eq⟩ := h_package.product_kernel
    have hf0_aesm : AEStronglyMeasurable f0 muU := by
      have hcont : AEStronglyMeasurable f0
          (muU.restrict {y : Cube d | InUnitCube y}) :=
        hf0_cont.aestronglyMeasurable hcube_meas
      have hind : AEStronglyMeasurable
          ({y : Cube d | InUnitCube y}.indicator f0) muU :=
        (aestronglyMeasurable_indicator_iff hcube_meas).mpr hcont
      refine hind.congr ?_
      filter_upwards [hcube_ae] with z hz
      rw [Set.indicator_of_mem hz]
    have hKbd : ∀ᵐ z ∂muU, ‖K h x z‖ ≤ (1 / h ^ d) * MK ^ d := by
      filter_upwards [hcube_ae] with z hz
      have h1 : ‖K h x z‖ =
          (1 / h ^ d) * |∏ j : Fin d, k ((x j - z j) / h)| := by
        rw [hK_eq x z hx_cube hz, Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / h ^ d)]
      rw [h1]
      apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ 1 / h ^ d)
      calc |∏ j : Fin d, k ((x j - z j) / h)|
          = ∏ j : Fin d, |k ((x j - z j) / h)| := Finset.abs_prod _ _
        _ ≤ ∏ _j : Fin d, MK :=
            Finset.prod_le_prod (fun j _ => abs_nonneg _) (fun j _ => hk_abs _)
        _ = MK ^ d := by simp
    have hK_aesm : AEStronglyMeasurable (K h x) muU :=
      (h_package.kernel_measurable x hx_cube).aestronglyMeasurable
    have hK_int : Integrable (K h x) muU :=
      MeasureTheory.Integrable.of_bound hK_aesm _ hKbd
    have hf0bd : ∀ᵐ z ∂muU, ‖f0 z‖ ≤ Mf := by
      filter_upwards [hcube_ae] with z hz
      rw [Real.norm_eq_abs]
      exact hMf z hz
    have hKf0bd : ∀ᵐ z ∂muU, ‖K h x z * f0 z‖ ≤ ((1 / h ^ d) * MK ^ d) * Mf := by
      filter_upwards [hKbd, hf0bd] with z h1 h2
      rw [Real.norm_eq_abs] at h1
      rw [Real.norm_eq_abs] at h2
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    have hKf0_int : Integrable (fun z => K h x z * f0 z) muU :=
      MeasureTheory.Integrable.of_bound (hK_aesm.mul hf0_aesm) _ hKf0bd
    have hident : (∫ ω, g x ω ∂P) - f0 x
        = ∫ z, K h x z * (f0 z - f0 x) ∂muU := by
      rw [h_package.population_smoother_identity x hx]
      have h1 : ∫ z, K h x z * (f0 z - f0 x) ∂muU
          = ∫ z, K h x z * f0 z ∂muU - f0 x := by
        calc ∫ z, K h x z * (f0 z - f0 x) ∂muU
            = ∫ z, (K h x z * f0 z - (f0 x) * K h x z) ∂muU := by
                congr 1 with z
                ring
          _ = ∫ z, K h x z * f0 z ∂muU - ∫ z, (f0 x) * K h x z ∂muU :=
                MeasureTheory.integral_sub hKf0_int (hK_int.const_mul (f0 x))
          _ = ∫ z, K h x z * f0 z ∂muU - f0 x * ∫ z, K h x z ∂muU := by
                rw [MeasureTheory.integral_const_mul]
          _ = ∫ z, K h x z * f0 z ∂muU - f0 x * 1 := by
                rw [h_package.kernel_normalization x hx]
          _ = ∫ z, K h x z * f0 z ∂muU - f0 x := by ring
      exact h1.symm
    have hprod_int : Integrable (fun z => K h x z * (f0 z - f0 x)) muU := by
      have h := hKf0_int.sub (hK_int.const_mul (f0 x))
      refine h.congr ?_
      filter_upwards with z
      simp only [Pi.sub_apply]
      ring
    have hmaj_bound : ∀ᵐ z ∂muU,
        ‖K h x z * (f0 z - f0 x)‖ ≤ L0 * (|K h x z| * ‖x - z‖ ^ alpha) := by
      filter_upwards [hcube_ae] with z hz
      have h1 : |f0 z - f0 x| ≤ L0 * ‖z - x‖ ^ alpha :=
        h_package.holder z x hz hx_cube
      rw [Real.norm_eq_abs, abs_mul, norm_sub_rev x z]
      calc |K h x z| * |f0 z - f0 x| ≤ |K h x z| * (L0 * ‖z - x‖ ^ alpha) :=
            mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        _ = L0 * (|K h x z| * ‖z - x‖ ^ alpha) := by ring
    have hnorm2 : ∀ᵐ z ∂muU, ‖x - z‖ ≤ 2 := by
      filter_upwards [hcube_ae] with z hz
      refine (pi_norm_le_iff_of_nonneg (x := x - z) (r := 2)
        (by norm_num : (0:ℝ) ≤ 2)).mpr ?_
      intro j
      rw [Real.norm_eq_abs, Pi.sub_apply, abs_le]
      constructor
      · linarith [(hx_cube j).1, (hz j).2]
      · linarith [(hx_cube j).2, (hz j).1]
    have hmaj_int : Integrable (fun z => L0 * (|K h x z| * ‖x - z‖ ^ alpha)) muU := by
      have hmeas : Measurable
          (fun z : Cube d => L0 * (|K h x z| * ‖x - z‖ ^ alpha)) := by
        have hsub : Continuous fun z : Cube d => x - z :=
          continuous_const.sub continuous_id
        have hphi : Continuous fun z : Cube d => ‖x - z‖ ^ alpha :=
          (Real.continuous_rpow_const (le_of_lt halpha)).comp hsub.norm
        exact measurable_const.mul
          (((h_package.kernel_measurable x hx_cube).abs).mul hphi.measurable)
      have hbd : ∀ᵐ z ∂muU,
          ‖L0 * (|K h x z| * ‖x - z‖ ^ alpha)‖
            ≤ L0 * (((1 / h ^ d) * MK ^ d) * (2:ℝ) ^ alpha) := by
        filter_upwards [hKbd, hnorm2] with z h1 h2
        have h1' : |K h x z| ≤ (1 / h ^ d) * MK ^ d := by
          rw [Real.norm_eq_abs] at h1
          exact h1
        have hpow : ‖x - z‖ ^ alpha ≤ (2:ℝ) ^ alpha :=
          Real.rpow_le_rpow (norm_nonneg _) h2 (le_of_lt halpha)
        have hle : |K h x z| * ‖x - z‖ ^ alpha
            ≤ ((1 / h ^ d) * MK ^ d) * (2:ℝ) ^ alpha :=
          mul_le_mul h1' hpow (by positivity) (by positivity)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hL0,
          abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left hle hL0
      exact MeasureTheory.Integrable.of_bound hmeas.aestronglyMeasurable _ hbd
    have hbound : |∫ z, K h x z * (f0 z - f0 x) ∂muU|
        ≤ L0 * MAlpha * Real.rpow h alpha := by
      have h1 : |∫ z, K h x z * (f0 z - f0 x) ∂muU|
          ≤ ∫ z, ‖K h x z * (f0 z - f0 x)‖ ∂muU := by
        simpa [Real.norm_eq_abs] using
          MeasureTheory.norm_integral_le_integral_norm
            (fun z => K h x z * (f0 z - f0 x))
      have h2 : ∫ z, ‖K h x z * (f0 z - f0 x)‖ ∂muU
          ≤ ∫ z, L0 * (|K h x z| * ‖x - z‖ ^ alpha) ∂muU :=
        MeasureTheory.integral_mono_ae hprod_int.norm hmaj_int hmaj_bound
      have h3 : ∫ z, L0 * (|K h x z| * ‖x - z‖ ^ alpha) ∂muU
          = L0 * ∫ z, |K h x z| * ‖x - z‖ ^ alpha ∂muU :=
        MeasureTheory.integral_const_mul L0 _
      have h4 : ∫ z, |K h x z| * ‖x - z‖ ^ alpha ∂muU ≤ MAlpha * h ^ alpha :=
        h_package.kernel_alpha_moment x hx
      calc |∫ z, K h x z * (f0 z - f0 x) ∂muU|
          ≤ ∫ z, ‖K h x z * (f0 z - f0 x)‖ ∂muU := h1
        _ ≤ ∫ z, L0 * (|K h x z| * ‖x - z‖ ^ alpha) ∂muU := h2
        _ = L0 * ∫ z, |K h x z| * ‖x - z‖ ^ alpha ∂muU := h3
        _ ≤ L0 * (MAlpha * h ^ alpha) := mul_le_mul_of_nonneg_left h4 hL0
        _ = L0 * MAlpha * h ^ alpha := by ring
    rw [hident]
    exact hbound
  have hpt : ∀ x, InInteriorBand h x →
      ∫ ω, (g x ω - f0 x) ^ 2 ∂P ≤
        (Cv + (L0 * MAlpha) ^ 2) * Real.rpow h (2 * alpha) :=
    fun x hx => statopia_math_node_2486692478_7ec19360 d alpha halpha n hn h hh hh_pos
      P g f0 L0 MAlpha Cv hL0 hMAlpha hCv h_package.inner_integrable
      h_package.centered_fluctuation_bound h_bias h_bw x hx
  have hmass : muI.real {x : Cube d | InInteriorBand h x} ≤ 1 := by
    have hone : (1 : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    simpa using ENNReal.toReal_mono hone h_package.interior_mass
  have hcoef : 0 ≤ (Cv + (L0 * MAlpha) ^ 2) * Real.rpow h (2 * alpha) := by
    have h1 : 0 ≤ Cv + (L0 * MAlpha) ^ 2 := by nlinarith [sq_nonneg (L0 * MAlpha)]
    exact mul_nonneg h1 (le_of_lt (Real.rpow_pos_of_pos hh_pos (2 * alpha)))
  have hmain : ∫ x in {x : Cube d | InInteriorBand h x},
      (∫ ω, (g x ω - f0 x) ^ 2 ∂P) ∂muI ≤
        (Cv + (L0 * MAlpha) ^ 2) * Real.rpow h (2 * alpha) := by
    have hconst_int : Integrable
        (fun _ : Cube d => (Cv + (L0 * MAlpha) ^ 2) * Real.rpow h (2 * alpha))
        (muI.restrict {x : Cube d | InInteriorBand h x}) := integrable_const _
    have hmem : ∀ᵐ x ∂(muI.restrict {x : Cube d | InInteriorBand h x}),
        x ∈ {x : Cube d | InInteriorBand h x} := by
      rw [MeasureTheory.ae_iff]
      show muI.restrict {x : Cube d | InInteriorBand h x}
          {x : Cube d | InInteriorBand h x}ᶜ = 0
      rw [MeasureTheory.Measure.restrict_apply hband_meas.compl]
      simp
    have hae : ∀ᵐ x ∂(muI.restrict {x : Cube d | InInteriorBand h x}),
        (∫ ω, (g x ω - f0 x) ^ 2 ∂P) ≤
          (Cv + (L0 * MAlpha) ^ 2) * Real.rpow h (2 * alpha) := by
      filter_upwards [hmem] with x hx
      exact hpt x hx
    have hmono := MeasureTheory.integral_mono_ae h_package.risk_integrable
      hconst_int hae
    have hrv : (muI.restrict {x : Cube d | InInteriorBand h x}).real Set.univ
        = muI.real {x : Cube d | InInteriorBand h x} := by
      show ((muI.restrict {x : Cube d | InInteriorBand h x}) Set.univ).toReal
        = (muI {x : Cube d | InInteriorBand h x}).toReal
      rw [MeasureTheory.Measure.restrict_apply_univ]
    rw [MeasureTheory.integral_const, hrv, smul_eq_mul] at hmono
    refine le_trans hmono ?_
    nlinarith [hmass, hcoef]
  have hgoal : ∫ x in {x : Cube d | InInteriorBand h x},
      (∫ ω, (g x ω - f0 x) ^ 2 ∂P) ∂muI ≤
        (1 + (L0 * MAlpha) ^ 2 + Cv) *
          Real.rpow (n : ℝ) (-2 * alpha / (2 * alpha + (d : ℝ))) := by
    calc ∫ x in {x : Cube d | InInteriorBand h x},
        (∫ ω, (g x ω - f0 x) ^ 2 ∂P) ∂muI
        ≤ (Cv + (L0 * MAlpha) ^ 2) * Real.rpow h (2 * alpha) := hmain
      _ = (Cv + (L0 * MAlpha) ^ 2) *
            Real.rpow (n : ℝ) (-2 * alpha / (2 * alpha + (d : ℝ))) := by rw [hbw2]
      _ ≤ (1 + (L0 * MAlpha) ^ 2 + Cv) *
            Real.rpow (n : ℝ) (-2 * alpha / (2 * alpha + (d : ℝ))) :=
          mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (L0 * MAlpha)])
            (le_of_lt (Real.rpow_pos_of_pos hn_pos _))
  exact hgoal
  /- @proof-region region.root.d6108a46516c end -/

end Msc62GroundTruth
