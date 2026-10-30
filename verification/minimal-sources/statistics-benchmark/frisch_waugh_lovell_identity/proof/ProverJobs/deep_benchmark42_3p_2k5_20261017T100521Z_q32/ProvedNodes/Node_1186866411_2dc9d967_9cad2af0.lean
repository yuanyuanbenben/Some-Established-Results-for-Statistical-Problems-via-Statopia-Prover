import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q32.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q32.Base

open Matrix

open Matrix

set_option autoImplicit false in
theorem statopia_math_node_1186866411_2dc9d967 : ∀ (n p : ℕ) (X1 : Matrix (Fin n) (Fin p) ℝ)
    (hker : ∀ u : Fin p → ℝ, X1 *ᵥ u = 0 → u = 0),
    (X1.transpose * X1).transpose = X1.transpose * X1 ∧
      ∀ x : Fin p → ℝ, x ≠ 0 →
        0 < dotProduct x ((X1.transpose * X1) *ᵥ x) := by
  /- @proof-region region.target-node.session.b6f28ff4cb9b3ed0 begin -/
  intro n p X1 hker
  constructor
  · rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  · intro x hx
    have hne : X1 *ᵥ x ≠ 0 := fun h => hx (hker x h)
    have hvec : Matrix.vecMul x X1.transpose = X1 *ᵥ x := by
      funext i
      simp only [Matrix.vecMul, Matrix.mulVec, Matrix.transpose_apply]
      exact dotProduct_comm x (fun j => X1 i j)

    have hquad : dotProduct x ((X1.transpose * X1) *ᵥ x)
        = dotProduct (X1 *ᵥ x) (X1 *ᵥ x) := by
      rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hvec]
    rw [hquad]
    simpa using (Matrix.dotProduct_self_star_pos_iff (v := X1 *ᵥ x)).mpr hne


  /- @proof-region region.target-node.session.b6f28ff4cb9b3ed0 end -/
