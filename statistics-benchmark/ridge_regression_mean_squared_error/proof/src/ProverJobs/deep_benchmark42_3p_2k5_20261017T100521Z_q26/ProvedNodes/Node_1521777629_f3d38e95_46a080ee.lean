import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q26.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q26.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q26.ProvedNodes.Node_3749075562_82ca6ac8_7fe8f0fc

open MeasureTheory Matrix

open MeasureTheory Matrix

set_option autoImplicit false in
theorem statopia_math_node_1521777629_f3d38e95 : ∀ (n d : ℕ)
    (X : Matrix (Fin n) (Fin d) ℝ)
    (A : Matrix (Fin d) (Fin d) ℝ)
    (hAsymm : A.transpose = A)
    (hAinv : (A⁻¹).transpose = A⁻¹),
    let L : Matrix (Fin d) (Fin n) ℝ := A⁻¹ * X.transpose
    (A⁻¹ * X.transpose * X * A⁻¹).trace =
      ∑ k : Fin d, ∑ i : Fin n, (L k i) ^ 2 := by
  /- @proof-region region.target-node.session.94f9840e8225aaaa begin -/
  intro n d X A hAsymm hAinv
  dsimp only
  have hL : A⁻¹ * X.transpose * X * A⁻¹
      = (A⁻¹ * X.transpose) * (A⁻¹ * X.transpose).transpose := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, hAinv, Matrix.mul_assoc]
  rw [hL]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, sq]

  /- @proof-region region.target-node.session.94f9840e8225aaaa end -/
