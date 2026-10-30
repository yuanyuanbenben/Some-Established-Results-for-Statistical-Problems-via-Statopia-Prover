import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q25.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q25.Base

open MeasureTheory ProbabilityTheory
open scoped BigOperators

open MeasureTheory ProbabilityTheory
open scoped BigOperators

set_option autoImplicit false in
theorem statopia_math_node_1239051236_4b1511cf : ∀ (z : ℝ) (hz : 0 ≤ z),
    Real.exp (-z) ≤ 1 - z + z ^ 2 / 2 := by
  /- @proof-region region.target-node.session.190348a31aaa2e37 begin -/
  intro z hz
  have hC : 0 < 1 - z + z ^ 2 / 2 := by nlinarith [sq_nonneg (z - 1)]
  have hsum : (∑ i ∈ Finset.range 3, z ^ i / i.factorial) = 1 + z + z ^ 2 / 2 := by
    simp [Finset.sum_range_succ]
  have hexp : 1 + z + z ^ 2 / 2 ≤ Real.exp z := by
    rw [← hsum]
    exact Real.sum_le_exp_of_nonneg hz 3
  have hAC : 1 ≤ (1 - z + z ^ 2 / 2) * (1 + z + z ^ 2 / 2) := by
    have hid : (1 - z + z ^ 2 / 2) * (1 + z + z ^ 2 / 2) = 1 + z ^ 4 / 4 := by ring
    nlinarith [sq_nonneg (z ^ 2)]
  have h1 : 1 ≤ (1 - z + z ^ 2 / 2) * Real.exp z := by
    have h := mul_le_mul_of_nonneg_left hexp hC.le
    linarith
  have hprod : Real.exp (-z) * Real.exp z = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hstep := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-z)).le
  have hR : Real.exp (-z) * ((1 - z + z ^ 2 / 2) * Real.exp z) = 1 - z + z ^ 2 / 2 := by
    rw [mul_comm (1 - z + z ^ 2 / 2) (Real.exp z), ← mul_assoc, hprod, one_mul]
  simpa [hR] using hstep
  /- @proof-region region.target-node.session.190348a31aaa2e37 end -/
