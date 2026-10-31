import ProverJobs.job_paper_c93669ef201447419b92d6591d8bc1aa.Vocabulary
import ProverJobs.job_paper_c93669ef201447419b92d6591d8bc1aa.Base

open Statlib.Imported
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators

namespace Statlib.Imported
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators

set_option autoImplicit false in
theorem statopia_math_node_226752033_d30a6425 : ∀ (nu Lambda A : ℝ) (hnu : 0 < nu) (hLambda : 1 ≤ Lambda)
    (hA : 0 ≤ A), min 1 (nu * Lambda * A) / (nu * Lambda) ≤ min A (1 / nu) := by
  /- @proof-region region.target-node.session.24a0ab2a146fc90e begin -/
  intro nu Lambda A hnu hLambda hA
  have hLam0 : (0 : ℝ) < Lambda := lt_of_lt_of_le zero_lt_one hLambda
  have hnuL : (0 : ℝ) < nu * Lambda := mul_pos hnu hLam0
  have hne : nu * Lambda ≠ 0 := ne_of_gt hnuL
  have hrec : 1 / (nu * Lambda) ≤ 1 / nu := by
    apply one_div_le_one_div_of_le hnu
    nlinarith
  by_cases h : nu * Lambda * A ≤ 1
  · have hAeq : nu * Lambda * A / (nu * Lambda) = A := by
      field_simp
    rw [min_eq_right h, hAeq]
    refine le_min le_rfl ?_
    calc A ≤ 1 / (nu * Lambda) := by
          rw [le_div_iff₀ hnuL]
          nlinarith
      _ ≤ 1 / nu := hrec
  · have h1 : 1 < nu * Lambda * A := lt_of_not_ge h
    rw [min_eq_left (le_of_lt h1)]
    refine le_min ?_ hrec
    rw [div_le_iff₀ hnuL]
    nlinarith
  /- @proof-region region.target-node.session.24a0ab2a146fc90e end -/

end Statlib.Imported
