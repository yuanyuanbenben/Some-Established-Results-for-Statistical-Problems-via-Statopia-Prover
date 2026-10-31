import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q16.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q16.Base

open MeasureTheory Matrix ProbabilityTheory

open MeasureTheory Matrix ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_415881013_e54b3026 : ∀ (n p : ℕ) (X : Matrix (Fin n) (Fin p) ℝ)
    (hX : Function.Injective X.mulVec),
    IsUnit (X.transpose * X) ∧
      (X.transpose * X)⁻¹ * (X.transpose * X) = 1 ∧
      (X.transpose * X) * (X.transpose * X)⁻¹ = 1 := by
  /- @proof-region region.target-node.session.753fee0e246d9bea begin -/
  intro n p X hX
  have hker : ∀ v : Fin p → ℝ, (Xᵀ * X) *ᵥ v = 0 → v = 0 := by
    intro v hv
    have key : v ⬝ᵥ ((Xᵀ * X) *ᵥ v) = (X *ᵥ v) ⬝ᵥ (X *ᵥ v) := by
      rw [← Matrix.mulVec_mulVec v Xᵀ X]
      rw [Matrix.dotProduct_mulVec v Xᵀ (X *ᵥ v)]
      rw [show Matrix.vecMul v Xᵀ = X *ᵥ v from by
        rw [← Matrix.mulVec_transpose (A := Xᵀ) (x := v)]
        simp]
    have h2 : (X *ᵥ v) ⬝ᵥ (X *ᵥ v) = 0 := by
      rw [← key, hv]
      simp
    have h3 : X *ᵥ v = 0 := dotProduct_self_eq_zero.mp h2
    exact hX (by simpa using h3)
  have hne : (Xᵀ * X).det ≠ 0 := by
    intro h0
    obtain ⟨v, hv1, hv2⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := Xᵀ * X)).mpr h0
    exact hv1 (hker v hv2)
  have hu : IsUnit (Xᵀ * X).det := isUnit_iff_ne_zero.mpr hne
  exact ⟨(Matrix.isUnit_iff_isUnit_det (Xᵀ * X)).mpr hu,
    Matrix.nonsing_inv_mul _ hu, Matrix.mul_nonsing_inv _ hu⟩
  /- @proof-region region.target-node.session.753fee0e246d9bea end -/
