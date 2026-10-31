import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q25.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q25.Base

open MeasureTheory ProbabilityTheory
open scoped BigOperators

open MeasureTheory ProbabilityTheory
open scoped BigOperators

set_option autoImplicit false in
theorem statopia_math_node_3138288691_f6d99626 : ∀ (n : ℕ) (hn : 1 ≤ n) (z : ℝ) (hz_nonneg : 0 ≤ z) (hz_le_one : z ≤ 1),
    (1 - z) ^ n ≤ Real.exp (-(n : ℝ) * z) := by
  /- @proof-region region.target-node.session.a447ed5a27700d46 begin -/
  intro n hn z hz_nonneg hz_le_one
  have h1 : 0 ≤ 1 - z := by linarith
  have h2 : 1 - z ≤ Real.exp (-z) := by
    have h := Real.add_one_le_exp (-z)
    linarith
  have key : ∀ k : ℕ, (1 - z) ^ k ≤ Real.exp (-(k : ℝ) * z) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hmul : (1 - z) ^ k * (1 - z) ≤ Real.exp (-(k : ℝ) * z) * Real.exp (-z) :=
        mul_le_mul ih h2 h1 (Real.exp_pos _).le
      have heq : Real.exp (-(k : ℝ) * z) * Real.exp (-z)
          = Real.exp (-((k + 1 : ℕ) : ℝ) * z) := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        ring
      rw [heq] at hmul
      simpa [pow_succ] using hmul
  exact key n
  /- @proof-region region.target-node.session.a447ed5a27700d46 end -/
