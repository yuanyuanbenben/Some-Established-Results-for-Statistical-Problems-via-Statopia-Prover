import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q15.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q15.Base

open Filter MeasureTheory ProbabilityTheory

open Filter MeasureTheory ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_4073185746_5120f090 : ∀ (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1),
    let f : ℝ → ℝ := fun x => 2 * Real.arcsin (Real.sqrt x)
    HasDerivAt f (1 / Real.sqrt (θ * (1 - θ))) θ ∧
      Real.sqrt (θ * (1 - θ)) > 0 ∧
      Real.sqrt (θ * (1 - θ)) * (1 / Real.sqrt (θ * (1 - θ))) = 1 := by
  /- @proof-region region.target-node.session.257ce8938a7684c7 begin -/
  intro θ hθ0 hθ1
  dsimp only
  have h1θ : 0 < 1 - θ := by linarith
  have hprod : 0 < θ * (1 - θ) := mul_pos hθ0 h1θ
  have hσpos : 0 < Real.sqrt (θ * (1 - θ)) := Real.sqrt_pos.mpr hprod
  have hθne : θ ≠ 0 := ne_of_gt hθ0
  have hApos : 0 < Real.sqrt θ := Real.sqrt_pos.mpr hθ0
  have hAne : Real.sqrt θ ≠ 0 := ne_of_gt hApos
  have hBpos : 0 < Real.sqrt (1 - θ) := Real.sqrt_pos.mpr h1θ
  have hBne : Real.sqrt (1 - θ) ≠ 0 := ne_of_gt hBpos
  have hABne : Real.sqrt θ * Real.sqrt (1 - θ) ≠ 0 := mul_ne_zero hAne hBne
  have hsq : Real.sqrt θ ^ 2 = θ := Real.sq_sqrt hθ0.le
  have hsqrt_lt_one : Real.sqrt θ < 1 := by
    have h := Real.sqrt_lt_sqrt hθ0.le hθ1
    simpa using h
  refine ⟨?_, hσpos, ?_⟩
  · have hsqrth := Real.hasDerivAt_sqrt hθne
    have harcsin := Real.hasDerivAt_arcsin (x := Real.sqrt θ)
      (by linarith : Real.sqrt θ ≠ -1) (by linarith : Real.sqrt θ ≠ 1)
    have hcomp := harcsin.comp θ hsqrth
    have h2 := hcomp.const_mul (2 : ℝ)
    have hderiv : 2 * ((1 / Real.sqrt (1 - Real.sqrt θ ^ 2)) * (1 / (2 * Real.sqrt θ)))
        = 1 / Real.sqrt (θ * (1 - θ)) := by
      rw [hsq, Real.sqrt_mul hθ0.le]
      field_simp [hAne, hBne, hABne]
    simpa only [hderiv] using h2
  · rw [one_div, mul_inv_cancel₀ (ne_of_gt hσpos)]
  /- @proof-region region.target-node.session.257ce8938a7684c7 end -/
