import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q29.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q29.Base

open Matrix

open Matrix

set_option autoImplicit false in
theorem statopia_math_node_2617968406_fa05324d : ∀ (d : ℕ) (v : Fin d → Fin d → ℝ)
    (horth : ∀ j k : Fin d, dotProduct (v j) (v k) = if j = k then 1 else 0)
    (hspan : Submodule.span ℝ (Set.range v) = ⊤)
    (A : Matrix (Fin d) (Fin d) ℝ),
    ∑ j : Fin d, dotProduct (v j) (A *ᵥ v j) = A.trace := by
  /- @proof-region region.target-node.session.789c40e2f0ba1026 begin -/
  intro d v horth hspan A
  classical
  let U : Matrix (Fin d) (Fin d) ℝ := fun i j => v j i
  have hUapp : ∀ i j : Fin d, U i j = v j i := fun i j => rfl
  have hU : Uᵀ * U = 1 := by
    ext j k
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, hUapp]
    simpa [dotProduct] using horth j k
  have hUU : U * Uᵀ = 1 := (Matrix.mul_eq_one_comm).mpr hU
  have hdiag : (∑ j : Fin d, dotProduct (v j) (A *ᵥ v j)) = (Uᵀ * (A * U)).trace := by
    simp [Matrix.trace, Matrix.mul_apply, Matrix.transpose_apply, hUapp, dotProduct, Matrix.mulVec]
  calc ∑ j : Fin d, dotProduct (v j) (A *ᵥ v j)
      = (Uᵀ * (A * U)).trace := hdiag
    _ = ((A * U) * Uᵀ).trace := Matrix.trace_mul_comm Uᵀ (A * U)
    _ = (A * (U * Uᵀ)).trace := by rw [Matrix.mul_assoc]
    _ = (A * 1).trace := by rw [hUU]
    _ = A.trace := by rw [Matrix.mul_one]
  /- @proof-region region.target-node.session.789c40e2f0ba1026 end -/
