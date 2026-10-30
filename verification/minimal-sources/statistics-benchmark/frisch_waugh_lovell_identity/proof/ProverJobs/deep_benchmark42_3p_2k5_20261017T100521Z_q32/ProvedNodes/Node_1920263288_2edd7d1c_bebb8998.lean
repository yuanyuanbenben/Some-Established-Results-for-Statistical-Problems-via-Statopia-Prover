import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q32.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q32.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q32.ProvedNodes.Node_1186866411_2dc9d967_9cad2af0

open Matrix

open Matrix

set_option autoImplicit false in
theorem statopia_math_node_1920263288_2edd7d1c : ∀ (n p : ℕ) (X1 : Matrix (Fin n) (Fin p) ℝ)
    (Ainv : Matrix (Fin p) (Fin p) ℝ)
    (hAinv : (X1.transpose * X1) * Ainv = 1)
    (hAsym : (X1.transpose * X1).transpose = X1.transpose * X1),
    let M1 : Matrix (Fin n) (Fin n) ℝ := 1 - X1 * Ainv * X1.transpose
    Ainv.transpose = Ainv ∧
      X1.transpose * M1 = 0 ∧
      M1.transpose = M1 ∧
      M1 * M1 = M1 ∧
      M1.transpose * M1 = M1 := by
  /- @proof-region region.target-node.session.88460e43a8bcffaf begin -/
  intro n p X1 Ainv hAinv hAsym
  have hP : X1.transpose * (X1 * Ainv * X1.transpose) = X1.transpose := by
    simp only [← Matrix.mul_assoc, hAinv, Matrix.one_mul]
  have hAinvT : Ainv.transpose = Ainv := by
    have h1 : Ainv.transpose * (X1.transpose * X1) = 1 := by
      rw [← hAsym, ← Matrix.transpose_mul, hAinv, Matrix.transpose_one]
    calc Ainv.transpose = Ainv.transpose * 1 := by rw [Matrix.mul_one]
      _ = Ainv.transpose * ((X1.transpose * X1) * Ainv) := by rw [hAinv]
      _ = (Ainv.transpose * (X1.transpose * X1)) * Ainv := by
            simp only [← Matrix.mul_assoc]
      _ = 1 * Ainv := by rw [h1]
      _ = Ainv := by rw [Matrix.one_mul]
  have hPP : (X1 * Ainv * X1.transpose) * (X1 * Ainv * X1.transpose)
      = X1 * Ainv * X1.transpose := by
    calc (X1 * Ainv * X1.transpose) * (X1 * Ainv * X1.transpose)
        = (X1 * Ainv) * (X1.transpose * (X1 * Ainv * X1.transpose)) :=
          Matrix.mul_assoc (X1 * Ainv) X1.transpose (X1 * Ainv * X1.transpose)
      _ = (X1 * Ainv) * X1.transpose := by rw [hP]
  have hM1sym : (1 - X1 * Ainv * X1.transpose).transpose
      = 1 - X1 * Ainv * X1.transpose := by
    simp only [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
      Matrix.transpose_transpose, hAinvT, ← Matrix.mul_assoc]
  have hM1idem : (1 - X1 * Ainv * X1.transpose) * (1 - X1 * Ainv * X1.transpose)
      = 1 - X1 * Ainv * X1.transpose := by
    have hexp : (1 - X1 * Ainv * X1.transpose) * (1 - X1 * Ainv * X1.transpose)
        = (1 - X1 * Ainv * X1.transpose)
          - (X1 * Ainv * X1.transpose
              - (X1 * Ainv * X1.transpose) * (X1 * Ainv * X1.transpose)) := by
      rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul]
    rw [hexp, hPP, sub_self, sub_zero]
  refine ⟨hAinvT, ?_, hM1sym, hM1idem, ?_⟩
  · rw [Matrix.mul_sub, Matrix.mul_one, hP, sub_self]
  · rw [hM1sym, hM1idem]
  /- @proof-region region.target-node.session.88460e43a8bcffaf end -/
