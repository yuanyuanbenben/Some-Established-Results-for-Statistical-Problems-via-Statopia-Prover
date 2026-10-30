import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q03.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q03.Base

open MeasureTheory Matrix ProbabilityTheory

open MeasureTheory Matrix ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_859487190_88621b65 : ∀ (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (s : ℝ) (hs : 0 < s),
    ∫ u in Set.Ioo 0 s, gammaConvDensity a u * gammaConvDensity b (s - u) =
      gammaConvDensity (a + b) s := by
  /- @proof-region region.target-node.session.a1112fa589569a81 begin -/
  intro a b ha hb s hs
  have hpt : ∀ u ∈ Set.Ioo 0 s,
      gammaConvDensity a u * gammaConvDensity b (s - u)
        = Real.exp (-(s / 2)) / (Real.rpow 2 (a + b) * (Real.Gamma a * Real.Gamma b))
            * (Real.rpow u (a - 1) * Real.rpow (s - u) (b - 1)) := by
    intro u hu
    have hu0 : 0 < u := hu.1
    have hus : 0 < s - u := by linarith [hu.2]
    have hexp : Real.exp (-(u / 2)) * Real.exp (-((s - u) / 2)) = Real.exp (-(s / 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h2 : Real.rpow 2 a * Real.rpow 2 b = Real.rpow 2 (a + b) :=
      (Real.rpow_add (by norm_num : (0 : ℝ) < 2) a b).symm
    have hden : (Real.rpow 2 a * Real.Gamma a) * (Real.rpow 2 b * Real.Gamma b)
        = Real.rpow 2 (a + b) * (Real.Gamma a * Real.Gamma b) := by
      rw [← h2]
      ring
    have hnum : (Real.rpow u (a - 1) * Real.exp (-(u / 2)))
          * (Real.rpow (s - u) (b - 1) * Real.exp (-((s - u) / 2)))
        = (Real.rpow u (a - 1) * Real.rpow (s - u) (b - 1))
            * (Real.exp (-(u / 2)) * Real.exp (-((s - u) / 2))) := by
      ring
    simp only [gammaConvDensity, if_pos hu0, if_pos hus]
    rw [div_mul_div_comm, hnum, hexp, hden, div_eq_mul_inv]
    ring
  have hcast : ∀ x : ℝ, 0 ≤ x → x ≤ s →
      ((Real.rpow x (a - 1) * Real.rpow (s - x) (b - 1) : ℝ) : ℂ)
        = (x : ℂ) ^ ((a : ℂ) - 1) * ((s : ℂ) - (x : ℂ)) ^ ((b : ℂ) - 1) := by
    intro x hx0 hxs
    have hae : (((a - 1 : ℝ)) : ℂ) = (a : ℂ) - 1 := by push_cast; ring
    have hbe : (((b - 1 : ℝ)) : ℂ) = (b : ℂ) - 1 := by push_cast; ring
    have h1 : ((Real.rpow x (a - 1) : ℝ) : ℂ) = (x : ℂ) ^ ((a : ℂ) - 1) := by
      have h := Complex.ofReal_cpow hx0 (a - 1)
      rwa [hae] at h
    have h2 : ((Real.rpow (s - x) (b - 1) : ℝ) : ℂ) = ((s : ℂ) - (x : ℂ)) ^ ((b : ℂ) - 1) := by
      have h := Complex.ofReal_cpow (show (0:ℝ) ≤ s - x by linarith) (b - 1)
      have hsx : ((s - x : ℝ) : ℂ) = (s : ℂ) - (x : ℂ) := by push_cast; ring
      rwa [hsx, hbe] at h
    calc ((Real.rpow x (a - 1) * Real.rpow (s - x) (b - 1) : ℝ) : ℂ)
        = ((Real.rpow x (a - 1) : ℝ) : ℂ) * ((Real.rpow (s - x) (b - 1) : ℝ) : ℂ) := by
          push_cast; ring
      _ = (x : ℂ) ^ ((a : ℂ) - 1) * ((Real.rpow (s - x) (b - 1) : ℝ) : ℂ) := by rw [h1]
      _ = (x : ℂ) ^ ((a : ℂ) - 1) * ((s : ℂ) - (x : ℂ)) ^ ((b : ℂ) - 1) := by rw [h2]
  have hsexp : ((s : ℂ)) ^ ((a : ℂ) + (b : ℂ) - 1)
      = ((Real.rpow s (a + b - 1) : ℝ) : ℂ) := by
    have hab : ((a : ℂ) + (b : ℂ) - 1) = (((a + b - 1 : ℝ)) : ℂ) := by push_cast; ring
    rw [hab]
    exact (Complex.ofReal_cpow hs.le (a + b - 1)).symm
  have hbetac : (a : ℂ).betaIntegral (b : ℂ)
      = ((Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) : ℝ) : ℂ) := by
    rw [Complex.betaIntegral_eq_Gamma_mul_div (a : ℂ) (b : ℂ) (by simpa using ha) (by simpa using hb)]
    rw [show ((a : ℂ) + (b : ℂ)) = ((a + b : ℝ) : ℂ) by push_cast; ring]
    simp only [Complex.Gamma_ofReal]
    push_cast
    ring
  have hval : (∫ u in (0 : ℝ)..s,
        (u : ℂ) ^ ((a : ℂ) - 1) * ((s : ℂ) - (u : ℂ)) ^ ((b : ℂ) - 1))
      = ((Real.rpow s (a + b - 1) * (Real.Gamma a * Real.Gamma b / Real.Gamma (a + b)) : ℝ) : ℂ) := by
    rw [Complex.betaIntegral_scaled (a : ℂ) (b : ℂ) hs]
    rw [hsexp, hbetac]
    push_cast
    ring
  have hIoc1 : (∫ u in Set.Ioc 0 s,
        ((Real.rpow u (a - 1) * Real.rpow (s - u) (b - 1) : ℝ) : ℂ))
      = ∫ u in Set.Ioc 0 s,
          (u : ℂ) ^ ((a : ℂ) - 1) * ((s : ℂ) - (u : ℂ)) ^ ((b : ℂ) - 1) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      (fun u hu => hcast u hu.1.le hu.2)
  have hIoc2 : (∫ u in Set.Ioc 0 s,
        (u : ℂ) ^ ((a : ℂ) - 1) * ((s : ℂ) - (u : ℂ)) ^ ((b : ℂ) - 1))
      = ∫ u in (0 : ℝ)..s,
          (u : ℂ) ^ ((a : ℂ) - 1) * ((s : ℂ) - (u : ℂ)) ^ ((b : ℂ) - 1) := by
    rw [intervalIntegral.integral_of_le hs.le]
  have hcomplex : (∫ u in Set.Ioc 0 s,
        ((Real.rpow u (a - 1) * Real.rpow (s - u) (b - 1) : ℝ) : ℂ))
      = ((Real.rpow s (a + b - 1) * (Real.Gamma a * Real.Gamma b / Real.Gamma (a + b)) : ℝ) : ℂ) :=
    hIoc1.trans (hIoc2.trans hval)
  have hreal : (∫ u in Set.Ioc 0 s, Real.rpow u (a - 1) * Real.rpow (s - u) (b - 1))
      = Real.rpow s (a + b - 1) * (Real.Gamma a * Real.Gamma b / Real.Gamma (a + b)) := by
    have hcastmain : ((∫ u in Set.Ioc 0 s,
          Real.rpow u (a - 1) * Real.rpow (s - u) (b - 1) : ℝ) : ℂ)
        = ((Real.rpow s (a + b - 1) * (Real.Gamma a * Real.Gamma b / Real.Gamma (a + b)) : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      exact hcomplex
    have hre := congrArg Complex.re hcastmain
    simpa using hre
  have hbridge : (∫ u in Set.Ioo 0 s, Real.rpow u (a - 1) * Real.rpow (s - u) (b - 1))
      = ∫ u in Set.Ioc 0 s, Real.rpow u (a - 1) * Real.rpow (s - u) (b - 1) := by
    have hmeas : volume.restrict (Set.Ioo 0 s) = volume.restrict (Set.Ioc 0 s) :=
      MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Ioc
    rw [hmeas]
  have hbeta : (∫ u in Set.Ioo 0 s, Real.rpow u (a - 1) * Real.rpow (s - u) (b - 1))
      = Real.rpow s (a + b - 1) * (Real.Gamma a * Real.Gamma b / Real.Gamma (a + b)) :=
    hbridge.trans hreal
  have hC : Real.exp (-(s / 2)) / (Real.rpow 2 (a + b) * (Real.Gamma a * Real.Gamma b))
        * (Real.rpow s (a + b - 1) * (Real.Gamma a * Real.Gamma b / Real.Gamma (a + b)))
      = gammaConvDensity (a + b) s := by
    rw [gammaConvDensity, if_pos hs]
    have h2p : Real.rpow 2 (a + b) ≠ 0 := (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _).ne'
    have hga : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
    have hgb : Real.Gamma b ≠ 0 := (Real.Gamma_pos_of_pos hb).ne'
    have hgab : Real.Gamma (a + b) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
    have hprod : Real.Gamma a * Real.Gamma b ≠ 0 := mul_ne_zero hga hgb
    have hden0 : Real.rpow 2 (a + b) * (Real.Gamma a * Real.Gamma b) ≠ 0 :=
      mul_ne_zero h2p hprod
    field_simp
  calc ∫ u in Set.Ioo 0 s, gammaConvDensity a u * gammaConvDensity b (s - u)
      = ∫ u in Set.Ioo 0 s,
          Real.exp (-(s / 2)) / (Real.rpow 2 (a + b) * (Real.Gamma a * Real.Gamma b))
            * (Real.rpow u (a - 1) * Real.rpow (s - u) (b - 1)) :=
        MeasureTheory.setIntegral_congr_fun measurableSet_Ioo hpt
    _ = Real.exp (-(s / 2)) / (Real.rpow 2 (a + b) * (Real.Gamma a * Real.Gamma b))
          * ∫ u in Set.Ioo 0 s, Real.rpow u (a - 1) * Real.rpow (s - u) (b - 1) := by
        rw [MeasureTheory.integral_const_mul]
    _ = Real.exp (-(s / 2)) / (Real.rpow 2 (a + b) * (Real.Gamma a * Real.Gamma b))
          * (Real.rpow s (a + b - 1) * (Real.Gamma a * Real.Gamma b / Real.Gamma (a + b))) := by
        rw [hbeta]
    _ = gammaConvDensity (a + b) s := hC
  /- @proof-region region.target-node.session.a1112fa589569a81 end -/
