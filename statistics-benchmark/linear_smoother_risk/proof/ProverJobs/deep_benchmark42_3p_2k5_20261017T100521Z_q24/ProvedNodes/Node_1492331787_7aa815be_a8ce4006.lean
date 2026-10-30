import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q24.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q24.Base

open MeasureTheory

open MeasureTheory

set_option autoImplicit false in
theorem statopia_math_node_1492331787_7aa815be : ∀ (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ),
    Matrix.trace (S.transpose * S) = ∑ i : Fin n, ∑ j : Fin n, (S i j) ^ 2 := by
  /- @proof-region region.target-node.session.2f9b7a0a4ab5c2ce begin -/
  intro n S
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, pow_two]
  rw [Finset.sum_comm]
  /- @proof-region region.target-node.session.2f9b7a0a4ab5c2ce end -/
