import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q25.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q25.Base

open MeasureTheory ProbabilityTheory
open scoped BigOperators

open MeasureTheory ProbabilityTheory
open scoped BigOperators

set_option autoImplicit false in
theorem statopia_math_node_401495820_d3a33ec9 : ∀ (t : ℝ),
    expMeasure 1 (Set.Iic t) = ENNReal.ofReal (1 - Real.exp (-t)) := by
  /- @proof-region region.target-node.session.c6c341b7d80eee83 begin -/
  intro t
  haveI : IsProbabilityMeasure (expMeasure 1) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (show (0 : ℝ) < 1 by norm_num)
  rw [← ProbabilityTheory.ofReal_cdf (expMeasure 1) t]
  rw [ProbabilityTheory.cdf_expMeasure_eq (r := 1) (show (0 : ℝ) < 1 by norm_num) t, one_mul]
  by_cases ht : 0 ≤ t
  · simp only [if_pos ht]
  · rw [if_neg ht]
    have hlt : t < 0 := not_le.mp ht
    have hexp : (1 : ℝ) < Real.exp (-t) := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by linarith)
    have hneg : 1 - Real.exp (-t) ≤ 0 := by linarith
    rw [ENNReal.ofReal_eq_zero.mpr hneg, ENNReal.ofReal_zero]
  /- @proof-region region.target-node.session.c6c341b7d80eee83 end -/
