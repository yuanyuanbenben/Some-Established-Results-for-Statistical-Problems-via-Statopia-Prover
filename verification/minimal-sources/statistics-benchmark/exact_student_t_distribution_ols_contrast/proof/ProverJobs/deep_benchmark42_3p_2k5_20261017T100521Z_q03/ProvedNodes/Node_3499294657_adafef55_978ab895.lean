import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q03.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q03.Base

open MeasureTheory Matrix ProbabilityTheory

open MeasureTheory Matrix ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_3499294657_adafef55 : ∀ (nu : ℝ) (hnu : 0 < nu) (t : ℝ),
    ∫⁻ v in Set.Ioi (0 : ℝ),
        ENNReal.ofReal
          (gammaConvDensity (nu / 2) v * Real.sqrt (v / nu) *
            ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(t ^ 2 * v / (2 * nu)))))
          ∂volume
      = ENNReal.ofReal
          (Real.Gamma ((nu + 1) / 2) / (Real.sqrt (nu * Real.pi) * Real.Gamma (nu / 2)) *
            Real.rpow (1 + t ^ 2 / nu) (-(nu + 1) / 2)) := by
  /- @proof-region region.target-node.session.e4f14ba319039a4a begin -/
  intro nu hnu t
  set a : ℝ := (nu + 1) / 2 with ha_def
  set r : ℝ := (1 + t ^ 2 / nu) / 2 with hr_def
  set K : ℝ := (Real.sqrt (2 * Real.pi))⁻¹ * (Real.sqrt nu)⁻¹ * (Real.rpow 2 (nu / 2) * Real.Gamma (nu / 2))⁻¹ with hK_def
  have ha_pos : 0 < a := by rw [ha_def]; positivity
  have hr_pos : 0 < r := by
    rw [hr_def]
    have h : (0:ℝ) < 1 + t ^ 2 / nu := by positivity
    linarith
  have hKpos : 0 < K := by
    rw [hK_def]
    have h1 : (0:ℝ) < Real.sqrt (2 * Real.pi) := by positivity
    have h2 : (0:ℝ) < Real.sqrt nu := by positivity
    have h3 : (0:ℝ) < Real.rpow 2 (nu / 2) := Real.rpow_pos_of_pos (by norm_num) _
    have h4 : (0:ℝ) < Real.Gamma (nu / 2) := Real.Gamma_pos_of_pos (by linarith : (0:ℝ) < nu / 2)
    have h5 : (0:ℝ) < Real.rpow 2 (nu / 2) * Real.Gamma (nu / 2) := by positivity
    positivity
  have hf_eq : ∀ v ∈ Set.Ioi (0:ℝ),
      gammaConvDensity (nu / 2) v * Real.sqrt (v / nu) *
        ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(t ^ 2 * v / (2 * nu))))
      = K * (v ^ (a - 1) * Real.exp (-(r * v))) := by
    intro v hv
    have hv0 : 0 < v := Set.mem_Ioi.mp hv
    have hnu0 : nu ≠ 0 := ne_of_gt hnu
    have hsqrt : Real.sqrt (v / nu) = v ^ ((1:ℝ)/2) * (Real.sqrt nu)⁻¹ := by
      rw [Real.sqrt_div (le_of_lt hv0) nu, Real.sqrt_eq_rpow v, div_eq_mul_inv]
    have hexp : Real.exp (-(v/2)) * Real.exp (-(t^2*v/(2*nu))) = Real.exp (-(r*v)) := by
      rw [← Real.exp_add]
      congr 1
      rw [hr_def]
      field_simp
      ring
    have hp : v ^ (nu/2-1) * v ^ ((1:ℝ)/2) = v ^ (a-1) := by
      calc v ^ (nu/2-1) * v ^ ((1:ℝ)/2) = v ^ ((nu/2-1) + ((1:ℝ)/2)) := (Real.rpow_add hv0 (nu/2-1) ((1:ℝ)/2)).symm
        _ = v ^ (a - 1) := by rw [ha_def]; congr 1; ring
    rw [show gammaConvDensity (nu / 2) v = (if 0 < v then Real.rpow v (nu / 2 - 1) * Real.exp (-(v / 2)) / (Real.rpow 2 (nu / 2) * Real.Gamma (nu / 2)) else 0) from rfl]
    rw [if_pos hv0, hsqrt]
    rw [div_eq_mul_inv (Real.rpow v (nu / 2 - 1) * Real.exp (-(v / 2))) (Real.rpow 2 (nu / 2) * Real.Gamma (nu / 2))]
    rw [hK_def, ← hp, ← hexp]
    rw [show Real.rpow v (nu / 2 - 1) = v ^ (nu / 2 - 1) from rfl]
    ring
  have hφ_int : IntegrableOn (fun v : ℝ => v ^ (a - 1) * Real.exp (-(r * v))) (Set.Ioi 0) volume := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1:ℝ)) (s := a - 1) (b := r) (by linarith) (le_refl (1:ℝ)) hr_pos
    simpa only [Real.rpow_one, neg_mul] using h
  have hIntK : IntegrableOn (fun v : ℝ => K * (v ^ (a - 1) * Real.exp (-(r * v)))) (Set.Ioi 0) volume := by
    have h := hφ_int.const_mul K
    simpa only [smul_eq_mul] using h
  have hInt : IntegrableOn (fun v : ℝ =>
      gammaConvDensity (nu / 2) v * Real.sqrt (v / nu) *
        ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(t ^ 2 * v / (2 * nu))))) (Set.Ioi 0) volume := by
    refine hIntK.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with v hv
    exact (hf_eq v hv).symm
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi 0)] (fun v : ℝ =>
      gammaConvDensity (nu / 2) v * Real.sqrt (v / nu) *
        ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(t ^ 2 * v / (2 * nu))))) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with v hv
    rw [hf_eq v hv]
    exact mul_nonneg (le_of_lt hKpos) (mul_nonneg (Real.rpow_nonneg (le_of_lt (Set.mem_Ioi.mp hv)) _) (le_of_lt (Real.exp_pos _)))
  have hreal : ∫ v in Set.Ioi (0:ℝ),
      (gammaConvDensity (nu / 2) v * Real.sqrt (v / nu) *
        ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(t ^ 2 * v / (2 * nu)))))
      = Real.Gamma a / (Real.sqrt (nu * Real.pi) * Real.Gamma (nu / 2)) * Real.rpow (1 + t ^ 2 / nu) (-(nu + 1) / 2) := by
    have hcongr : ∫ v in Set.Ioi (0:ℝ),
        (gammaConvDensity (nu / 2) v * Real.sqrt (v / nu) *
          ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(t ^ 2 * v / (2 * nu)))))
        = ∫ v in Set.Ioi (0:ℝ), K * (v ^ (a - 1) * Real.exp (-(r * v))) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with v hv
      exact hf_eq v hv
    rw [hcongr, MeasureTheory.integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi ha_pos hr_pos]
    have hqpos : (0:ℝ) < 1 + t ^ 2 / nu := by positivity
    have hqne : (1 + t ^ 2 / nu) ≠ 0 := ne_of_gt hqpos
    have hrq : (1:ℝ) / r = (2:ℝ) / (1 + t ^ 2 / nu) := by
      rw [hr_def]; field_simp
    rw [hK_def, hrq]
    rw [Real.div_rpow (by norm_num : (0:ℝ) ≤ 2) (le_of_lt hqpos)]
    rw [div_eq_mul_inv ((2:ℝ) ^ a) ((1 + t ^ 2 / nu) ^ a)]
    rw [← Real.rpow_neg (le_of_lt hqpos)]
    rw [_root_.mul_inv_rev]
    rw [show Real.rpow 2 (nu / 2) = (2:ℝ) ^ (nu / 2) from rfl]
    rw [show Real.rpow (1 + t ^ 2 / nu) (-(nu + 1) / 2) = (1 + t ^ 2 / nu) ^ (-(nu + 1) / 2) from rfl]
    rw [show -a = -(nu + 1) / 2 from by rw [ha_def]; ring]
    have h2pow : (2:ℝ) ^ a * ((2:ℝ) ^ (nu / 2))⁻¹ = Real.sqrt 2 := by
      rw [← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      rw [show a + -(nu / 2) = (1:ℝ)/2 from by rw [ha_def]; ring, ← Real.sqrt_eq_rpow]
    have hsq1 : (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt 2 = (Real.sqrt Real.pi)⁻¹ := by
      rw [show Real.sqrt (2 * Real.pi) = Real.sqrt 2 * Real.sqrt Real.pi from Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) Real.pi, _root_.mul_inv_rev]
      rw [_root_.mul_assoc, inv_mul_cancel₀ (ne_of_gt (by positivity : (0:ℝ) < Real.sqrt 2)), _root_.mul_one]
    have hsq2 : (Real.sqrt nu)⁻¹ * (Real.sqrt Real.pi)⁻¹ = (Real.sqrt (nu * Real.pi))⁻¹ := by
      rw [show Real.sqrt (nu * Real.pi) = Real.sqrt nu * Real.sqrt Real.pi from Real.sqrt_mul (le_of_lt hnu) Real.pi, _root_.mul_inv_rev, _root_.mul_comm]
    have e1 : (Real.sqrt (2 * Real.pi))⁻¹ * (Real.sqrt nu)⁻¹ *
        ((Real.Gamma (nu / 2))⁻¹ * ((2:ℝ) ^ (nu / 2))⁻¹) *
        ((((2:ℝ) ^ a) * (1 + t ^ 2 / nu) ^ (-(nu + 1) / 2)) * Real.Gamma a)
        = (((2:ℝ) ^ a) * ((2:ℝ) ^ (nu / 2))⁻¹) *
          ((Real.sqrt (2 * Real.pi))⁻¹ * (Real.sqrt nu)⁻¹ * (Real.Gamma (nu / 2))⁻¹ *
            Real.Gamma a * (1 + t ^ 2 / nu) ^ (-(nu + 1) / 2)) := by ring
    rw [e1, h2pow]
    have e2 : Real.sqrt 2 *
          ((Real.sqrt (2 * Real.pi))⁻¹ * (Real.sqrt nu)⁻¹ * (Real.Gamma (nu / 2))⁻¹ *
            Real.Gamma a * (1 + t ^ 2 / nu) ^ (-(nu + 1) / 2))
        = ((Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt 2) *
          ((Real.sqrt nu)⁻¹ * (Real.Gamma (nu / 2))⁻¹ *
            Real.Gamma a * (1 + t ^ 2 / nu) ^ (-(nu + 1) / 2)) := by ring
    rw [e2, hsq1]
    have e3 : (Real.sqrt Real.pi)⁻¹ *
          ((Real.sqrt nu)⁻¹ * (Real.Gamma (nu / 2))⁻¹ * Real.Gamma a * (1 + t ^ 2 / nu) ^ (-(nu + 1) / 2))
        = ((Real.sqrt nu)⁻¹ * (Real.sqrt Real.pi)⁻¹) *
          ((Real.Gamma (nu / 2))⁻¹ * Real.Gamma a * (1 + t ^ 2 / nu) ^ (-(nu + 1) / 2)) := by ring
    rw [e3, hsq2]
    rw [div_eq_mul_inv (Real.Gamma a) (Real.sqrt (nu * Real.pi) * Real.Gamma (nu / 2))]
    rw [_root_.mul_inv_rev]
    ring
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (μ := volume.restrict (Set.Ioi 0)) hInt hnn, hreal]
  /- @proof-region region.target-node.session.e4f14ba319039a4a end -/
