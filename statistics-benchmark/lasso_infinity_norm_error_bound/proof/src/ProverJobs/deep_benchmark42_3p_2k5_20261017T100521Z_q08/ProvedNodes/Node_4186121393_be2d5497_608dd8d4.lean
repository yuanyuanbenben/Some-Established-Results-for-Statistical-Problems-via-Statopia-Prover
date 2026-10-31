import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q08.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q08.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q08.ProvedNodes.Node_1420316284_290236b8_d1fde729
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q08.ProvedNodes.Node_2136473782_eb90246c_2f034c21


open MeasureTheory Matrix ProbabilityTheory

open MeasureTheory Matrix ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_4186121393_be2d5497 : ∀ (n d : ℕ) (hn : 1 ≤ n) (hd : 2 ≤ d)
    (sigma : ℝ) (hsigma : 0 < sigma)
    (X : Matrix (Fin n) (Fin d) ℝ)
    (S : Finset (Fin d))
    (gamma : ℝ) (hgamma : 0 < gamma)
    (hRE : ∀ Delta : Fin d → ℝ,
      (∑ j, if j ∈ S then (0 : ℝ) else |Delta j|) ≤
          3 * (∑ j, if j ∈ S then |Delta j| else (0 : ℝ)) →
      (⨆ j, |(((n : ℝ)⁻¹ • (X.transpose * X)) *ᵥ Delta) j|) ≥
        gamma * ⨆ j, |Delta j|)
    (thetaStar : Fin d → ℝ)
    (hsupport : ∀ j, j ∉ S → thetaStar j = 0)
    (w : Fin n → ℝ)
    (thetaHat : Fin d → ℝ)
    (hmin : ∀ eta : Fin d → ℝ,
      dotProduct (X *ᵥ thetaStar + w - X *ᵥ thetaHat)
          (X *ᵥ thetaStar + w - X *ᵥ thetaHat) / (2 * (n : ℝ)) +
          (4 * sigma * Real.sqrt (Real.log (d : ℝ) / (n : ℝ))) * (∑ j : Fin d, |thetaHat j|) ≤
        dotProduct (X *ᵥ thetaStar + w - X *ᵥ eta)
          (X *ᵥ thetaStar + w - X *ᵥ eta) / (2 * (n : ℝ)) +
          (4 * sigma * Real.sqrt (Real.log (d : ℝ) / (n : ℝ))) * (∑ j : Fin d, |eta j|))
    (hnoise : ∀ j : Fin d,
      |((Xᵀ *ᵥ w) j) / (n : ℝ)| ≤ (4 * sigma * Real.sqrt (Real.log (d : ℝ) / (n : ℝ))) / 2),
    (⨆ j : Fin d, |(thetaHat - thetaStar) j|) ≤
      6 * sigma / gamma * Real.sqrt (Real.log (d : ℝ) / (n : ℝ)) := by
  /- @proof-region region.target-node.session.4b7f5b19903e6935 begin -/
  intro n d hn hd sigma hsigma X S gamma hgamma hRE thetaStar hsupport w thetaHat hmin hnoise
  let lam : ℝ := 4 * sigma * Real.sqrt (Real.log (d : ℝ) / (n : ℝ))
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnR : (0 : ℝ) < (n : ℝ) := by linarith
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hlogd : 0 < Real.log (d : ℝ) := Real.log_pos (by linarith)
  have hq : 0 < Real.log (d : ℝ) / (n : ℝ) := div_pos hlogd hnR
  have hsqrt : 0 < Real.sqrt (Real.log (d : ℝ) / (n : ℝ)) := Real.sqrt_pos.mpr hq
  have hlam_lit : 0 < 4 * sigma * Real.sqrt (Real.log (d : ℝ) / (n : ℝ)) :=
    mul_pos (by linarith) hsqrt
  have hlam : 0 < lam := hlam_lit
  have hlam0 : 0 ≤ lam := le_of_lt hlam
  have hnoise' : ∀ j : Fin d, |((Xᵀ *ᵥ w) j) / (n : ℝ)| ≤ lam / 2 := hnoise
  have hmin_lam : ∀ eta : Fin d → ℝ,
      dotProduct (X *ᵥ thetaStar + w - X *ᵥ thetaHat)
          (X *ᵥ thetaStar + w - X *ᵥ thetaHat) / (2 * (n : ℝ)) + lam * (∑ j : Fin d, |thetaHat j|) ≤
        dotProduct (X *ᵥ thetaStar + w - X *ᵥ eta)
          (X *ᵥ thetaStar + w - X *ᵥ eta) / (2 * (n : ℝ)) + lam * (∑ j : Fin d, |eta j|) := hmin
  have hmin' : ∀ eta : Fin d → ℝ,
      (∑ i : Fin n, ((X *ᵥ thetaStar + w) i - (X *ᵥ thetaHat) i) ^ 2) / (2 * (n : ℝ)) +
          lam * (∑ j : Fin d, |thetaHat j|) ≤
        (∑ i : Fin n, ((X *ᵥ thetaStar + w) i - (X *ᵥ eta) i) ^ 2) / (2 * (n : ℝ)) +
          lam * (∑ j : Fin d, |eta j|) := by
    intro eta
    simpa only [dotProduct, pow_two, Pi.sub_apply, Pi.add_apply] using hmin_lam eta
  have hcert := statopia_math_node_1420316284_290236b8 n d hn (by omega) X
      (X *ᵥ thetaStar + w) lam hlam0 thetaHat hmin'
  obtain ⟨hcert_j, _⟩ := hcert
  have hcone := statopia_math_node_2136473782_eb90246c n d hn (by omega) X S thetaStar
      hsupport (4 * sigma * Real.sqrt (Real.log (d : ℝ) / (n : ℝ))) hlam_lit w thetaHat hmin hnoise
  have hres : (X *ᵥ thetaStar + w) - X *ᵥ thetaHat = w - X *ᵥ (thetaHat - thetaStar) := by
    funext i
    simp only [Pi.sub_apply, Pi.add_apply, Matrix.mulVec_sub]
    ring
  have hvec : Xᵀ *ᵥ ((X *ᵥ thetaStar + w) - X *ᵥ thetaHat)
      = Xᵀ *ᵥ w - (Xᵀ * X) *ᵥ (thetaHat - thetaStar) := by
    rw [hres, Matrix.mulVec_sub, Matrix.mulVec_mulVec]
  have hcoord : ∀ j : Fin d,
      |(((n : ℝ)⁻¹ • (Xᵀ * X)) *ᵥ (thetaHat - thetaStar)) j| ≤ 3 * lam / 2 := by
    intro j
    have hb : |(1 / (n : ℝ)) * (Xᵀ *ᵥ ((X *ᵥ thetaStar + w) - X *ᵥ thetaHat)) j| ≤ lam := hcert_j j
    have hg : |(1 / (n : ℝ)) * (Xᵀ *ᵥ w) j| ≤ lam / 2 := by
      simpa [one_div, div_eq_mul_inv, mul_comm] using hnoise' j
    have hid : (((n : ℝ)⁻¹ • (Xᵀ * X)) *ᵥ (thetaHat - thetaStar)) j
        = (1 / (n : ℝ)) * (Xᵀ *ᵥ w) j
          - (1 / (n : ℝ)) * (Xᵀ *ᵥ ((X *ᵥ thetaStar + w) - X *ᵥ thetaHat)) j := by
      rw [Matrix.smul_mulVec, hvec]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, one_div]
      ring
    calc |(((n : ℝ)⁻¹ • (Xᵀ * X)) *ᵥ (thetaHat - thetaStar)) j|
        = |(1 / (n : ℝ)) * (Xᵀ *ᵥ w) j
            - (1 / (n : ℝ)) * (Xᵀ *ᵥ ((X *ᵥ thetaStar + w) - X *ᵥ thetaHat)) j| := by rw [hid]
      _ ≤ |(1 / (n : ℝ)) * (Xᵀ *ᵥ w) j|
            + |(1 / (n : ℝ)) * (Xᵀ *ᵥ ((X *ᵥ thetaStar + w) - X *ᵥ thetaHat)) j| := by
          have h := abs_add_le ((1 / (n : ℝ)) * (Xᵀ *ᵥ w) j)
            (-((1 / (n : ℝ)) * (Xᵀ *ᵥ ((X *ᵥ thetaStar + w) - X *ᵥ thetaHat)) j))
          simpa using h
      _ ≤ lam / 2 + lam := by linarith
      _ = 3 * lam / 2 := by ring
  have hsup : (⨆ j : Fin d, |(((n : ℝ)⁻¹ • (Xᵀ * X)) *ᵥ (thetaHat - thetaStar)) j|) ≤ 3 * lam / 2 :=
    Real.iSup_le hcoord (by linarith)
  have hREapp := hRE (thetaHat - thetaStar) hcone
  have hstep : gamma * (⨆ j : Fin d, |(thetaHat - thetaStar) j|) ≤ 3 * lam / 2 := le_trans hREapp hsup
  have hfinal : (⨆ j : Fin d, |(thetaHat - thetaStar) j|) ≤ (3 * lam / 2) / gamma := by
    rw [le_div_iff₀ hgamma]
    calc (⨆ j : Fin d, |(thetaHat - thetaStar) j|) * gamma
        = gamma * (⨆ j : Fin d, |(thetaHat - thetaStar) j|) := by ring
      _ ≤ 3 * lam / 2 := hstep
  calc (⨆ j : Fin d, |(thetaHat - thetaStar) j|)
      ≤ (3 * lam / 2) / gamma := hfinal
    _ = 6 * sigma / gamma * Real.sqrt (Real.log (d : ℝ) / (n : ℝ)) := by
        have hv : lam = 4 * sigma * Real.sqrt (Real.log (d : ℝ) / (n : ℝ)) := rfl
        rw [hv]
        field_simp [hgamma.ne']
        ring
  /- @proof-region region.target-node.session.4b7f5b19903e6935 end -/
