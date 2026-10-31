import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q20.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q20.Base

open MeasureTheory ProbabilityTheory
open scoped BigOperators

open MeasureTheory ProbabilityTheory
open scoped BigOperators

set_option autoImplicit false in
theorem statopia_math_node_4171527340_5abf08e7 : ∀ (x : ℝ), NormedSpace.exp x = Real.exp x := by
  /- @proof-region region.target-node.session.1946d84365184bc6 begin -/
  intro x
  apply Complex.ofReal_injective
  have h3 : Complex.exp (x : ℂ) = NormedSpace.exp (x : ℂ) :=
    congrFun Complex.exp_eq_exp_ℂ (x : ℂ)
  calc ((NormedSpace.exp x : ℝ) : ℂ)
      = NormedSpace.exp (x : ℂ) := NormedSpace.ofReal_exp_ℝ_ℝ x
    _ = Complex.exp (x : ℂ) := h3.symm
    _ = ((Real.exp x : ℝ) : ℂ) := (Complex.ofReal_exp x).symm
  /- @proof-region region.target-node.session.1946d84365184bc6 end -/
