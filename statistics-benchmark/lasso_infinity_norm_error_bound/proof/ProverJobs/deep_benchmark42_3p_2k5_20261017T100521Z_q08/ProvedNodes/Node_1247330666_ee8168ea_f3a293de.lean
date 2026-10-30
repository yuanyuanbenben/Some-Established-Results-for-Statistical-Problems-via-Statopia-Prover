import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q08.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q08.Base

open MeasureTheory Matrix ProbabilityTheory

open MeasureTheory Matrix ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_1247330666_ee8168ea : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (v : NNReal) (T : ℝ) (hT : 0 < T) (Y : Ω → ℝ)
    (hY : HasLaw Y (gaussianReal 0 v) P),
    (v = 0 → P {ω | T < |Y ω|} = 0) ∧
      (0 < v → P {ω | T < |Y ω|} ≤
        ENNReal.ofReal (2 * Real.exp (-(T ^ 2 / (2 * (v : ℝ)))))) := by
  /- @proof-region region.target-node.session.f9692099707d966d begin -/
  intro Ω instΩ P hPprob v T hT Y hY
  constructor
  · intro hv0
    have hd : gaussianReal 0 v = Measure.dirac (0 : ℝ) := by
      rw [hv0]
      simp
    have hzero : gaussianReal 0 v {x : ℝ | T < |x|} = 0 := by
      rw [hd, Measure.dirac_apply]
      simp [abs_zero, hT.le]
    have hae : ∀ᵐ x ∂gaussianReal 0 v, ¬ (T < |x|) := by
      rw [ae_iff]
      simpa using hzero
    have hp : Measurable (fun x : ℝ => ¬ (T < |x|)) := by measurability
    have h1 : ∀ᵐ ω ∂P, ¬ (T < |Y ω|) := (hY.ae_iff hp).mpr hae
    rw [ae_iff] at h1
    simpa using h1
  · intro hv
    have hint : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * Y ω)) P := by
      intro t
      by_contra h
      have h0 : ∫ ω, Real.exp (t * Y ω) ∂P = 0 := MeasureTheory.integral_undef h
      have hval : ∫ ω, Real.exp (t * Y ω) ∂P = Real.exp (t ^ 2 * (v : ℝ) / 2) := by
        rw [show ∫ ω, Real.exp (t * Y ω) ∂P = ∫ x, Real.exp (t * x) ∂gaussianReal 0 v from
          hY.integral_comp (f := fun x : ℝ => Real.exp (t * x)) (by fun_prop)]
        exact Statlib.StatFoundation.Statistics.Asymptotic.gaussianReal_integral_exp t (v : ℝ) v.coe_nonneg
      rw [h0] at hval
      exact (Real.exp_pos (t ^ 2 * (v : ℝ) / 2)).ne hval
    have hmgf_eq : ∀ u : ℝ, mgf Y P u = Real.exp (u ^ 2 * (v : ℝ) / 2) := by
      intro u
      rw [show mgf Y P u = ∫ ω, Real.exp (u * Y ω) ∂P from rfl]
      rw [show ∫ ω, Real.exp (u * Y ω) ∂P = ∫ x, Real.exp (u * x) ∂gaussianReal 0 v from
        hY.integral_comp (f := fun x : ℝ => Real.exp (u * x)) (by fun_prop)]
      exact Statlib.StatFoundation.Statistics.Asymptotic.gaussianReal_integral_exp u (v : ℝ) v.coe_nonneg
    have hsub : HasSubgaussianMGF Y v P := by
      refine ⟨hint, ?_⟩
      intro t
      rw [hmgf_eq t]
      exact le_of_eq (congrArg Real.exp (by ring))
    have htail : P.real {ω | T ≤ |Y ω|} ≤ 2 * Real.exp (-(T ^ 2 / (2 * (v : ℝ)))) := by
      have h := Statlib.StatFoundation.RandomVariable.SubExponential.sub_gauss_tail_abs (X := Y) (c := v) hsub (ε := T) (le_of_lt hT)
      simpa [neg_div] using h
    have hconv : P {ω | T ≤ |Y ω|} = ENNReal.ofReal (P.real {ω | T ≤ |Y ω|}) := by
      show P {ω | T ≤ |Y ω|} = ENNReal.ofReal ((P {ω | T ≤ |Y ω|}).toReal)
      exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    calc P {ω | T < |Y ω|} ≤ P {ω | T ≤ |Y ω|} :=
          measure_mono (fun ω hω => le_of_lt (show T < |Y ω| from hω))
      _ = ENNReal.ofReal (P.real {ω | T ≤ |Y ω|}) := hconv
      _ ≤ ENNReal.ofReal (2 * Real.exp (-(T ^ 2 / (2 * (v : ℝ))))) := ENNReal.ofReal_le_ofReal htail
  /- @proof-region region.target-node.session.f9692099707d966d end -/
