import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q16.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q16.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q16.ProvedNodes.Node_415881013_e54b3026_044df4d9

open MeasureTheory Matrix ProbabilityTheory

open MeasureTheory Matrix ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_1353280134_668c18e6 : ∀ (n p : ℕ) (X : Matrix (Fin n) (Fin p) ℝ)
    (hMleft : (X.transpose * X)⁻¹ * (X.transpose * X) = 1)
    (hMright : (X.transpose * X) * (X.transpose * X)⁻¹ = 1),
    (X.transpose * X).transpose = X.transpose * X ∧
      ((X.transpose * X)⁻¹).transpose = (X.transpose * X)⁻¹ ∧
      (X * (X.transpose * X)⁻¹ * X.transpose).transpose
        = X * (X.transpose * X)⁻¹ * X.transpose ∧
      (1 - X * (X.transpose * X)⁻¹ * X.transpose).transpose
        = 1 - X * (X.transpose * X)⁻¹ * X.transpose ∧
      (X * (X.transpose * X)⁻¹ * X.transpose) * X = X ∧
      X.transpose * (1 - X * (X.transpose * X)⁻¹ * X.transpose) = 0 := by
  /- @proof-region region.target-node.session.7ce87f8a667b3186 begin -/
  intro n p X hMleft hMright
  have hMtr : (X.transpose * X).transpose = X.transpose * X := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hAtr : ((X.transpose * X)⁻¹).transpose = (X.transpose * X)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hMtr]
  have hH : (X * (X.transpose * X)⁻¹ * X.transpose).transpose
      = X * (X.transpose * X)⁻¹ * X.transpose := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hAtr, Matrix.mul_assoc]
  have hXH : X.transpose * (X * (X.transpose * X)⁻¹ * X.transpose) = X.transpose := by
    calc X.transpose * (X * (X.transpose * X)⁻¹ * X.transpose)
        = (X.transpose * X) * (X.transpose * X)⁻¹ * X.transpose := by
          simp only [Matrix.mul_assoc]
      _ = (1 : Matrix (Fin p) (Fin p) ℝ) * X.transpose := by rw [hMright]
      _ = X.transpose := by rw [Matrix.one_mul]
  refine ⟨hMtr, hAtr, hH, ?_, ?_, ?_⟩
  · rw [Matrix.transpose_sub, Matrix.transpose_one, hH]
  · calc (X * (X.transpose * X)⁻¹ * X.transpose) * X
        = X * ((X.transpose * X)⁻¹ * (X.transpose * X)) := by
          simp only [Matrix.mul_assoc]
      _ = X * (1 : Matrix (Fin p) (Fin p) ℝ) := by rw [hMleft]
      _ = X := by rw [Matrix.mul_one]
  · rw [Matrix.mul_sub, Matrix.mul_one, hXH, sub_self]
  /- @proof-region region.target-node.session.7ce87f8a667b3186 end -/
