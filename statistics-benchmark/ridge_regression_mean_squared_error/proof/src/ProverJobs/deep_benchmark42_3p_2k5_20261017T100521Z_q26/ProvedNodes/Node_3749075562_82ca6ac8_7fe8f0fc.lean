import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q26.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q26.Base

open MeasureTheory Matrix

open MeasureTheory Matrix

set_option autoImplicit false in
theorem statopia_math_node_3749075562_82ca6ac8 : ∀ (n d : ℕ)
    (X : Matrix (Fin n) (Fin d) ℝ)
    (lambda : ℝ) (hlambda : 0 < lambda),
    let A : Matrix (Fin d) (Fin d) ℝ := X.transpose * X + lambda • 1
    A.PosDef ∧ 0 < A.det ∧ IsUnit A ∧ A⁻¹ * A = 1 ∧ A * A⁻¹ = 1 ∧
      A.transpose = A ∧ (A⁻¹).transpose = A⁻¹ := by
  /- @proof-region region.target-node.session.42f684de458ee5a2 begin -/
  intro n d X lambda hlambda
  let A : Matrix (Fin d) (Fin d) ℝ := X.transpose * X + lambda • 1
  have hA : A = X.transpose * X + lambda • 1 := rfl
  have hpsd : (X.transpose * X).PosSemidef := by
    have h := Matrix.posSemidef_conjTranspose_mul_self (R := ℝ) X
    rw [Matrix.conjTranspose_eq_transpose_of_trivial X] at h
    exact h
  have hone : (1 : Matrix (Fin d) (Fin d) ℝ).PosDef := Matrix.PosDef.one
  have hsc : (lambda • (1 : Matrix (Fin d) (Fin d) ℝ)).PosDef :=
    Matrix.PosDef.smul hone hlambda
  have hpd : A.PosDef := by
    have h : (lambda • (1 : Matrix (Fin d) (Fin d) ℝ) + X.transpose * X).PosDef :=
      hsc.add_posSemidef hpsd
    rw [hA, add_comm]
    exact h
  have hdet : 0 < A.det := hpd.det_pos
  have hunit : IsUnit A := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    exact ne_of_gt hdet
  haveI : Invertible A :=
    Matrix.invertibleOfIsUnitDet A ((Matrix.isUnit_iff_isUnit_det A).mp hunit)
  have hinv1 : A⁻¹ * A = 1 := Matrix.inv_mul_of_invertible A
  have hinv2 : A * A⁻¹ = 1 := Matrix.mul_inv_of_invertible A
  have hsym : A.transpose = A := by
    rw [hA, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_smul,
      Matrix.transpose_one, Matrix.transpose_transpose]
  have hsyminv : (A⁻¹).transpose = A⁻¹ := by
    have ht : A.transpose * (A⁻¹).transpose = 1 := by
      rw [← Matrix.transpose_mul, hinv1, Matrix.transpose_one]
    rw [hsym] at ht
    calc (A⁻¹).transpose = 1 * (A⁻¹).transpose := (one_mul _).symm
      _ = (A⁻¹ * A) * (A⁻¹).transpose := by rw [hinv1]
      _ = A⁻¹ * (A * (A⁻¹).transpose) := by rw [mul_assoc]
      _ = A⁻¹ * 1 := by rw [ht]
      _ = A⁻¹ := mul_one _
  show A.PosDef ∧ 0 < A.det ∧ IsUnit A ∧ A⁻¹ * A = 1 ∧ A * A⁻¹ = 1 ∧
      A.transpose = A ∧ (A⁻¹).transpose = A⁻¹
  exact ⟨hpd, hdet, hunit, hinv1, hinv2, hsym, hsyminv⟩
  /- @proof-region region.target-node.session.42f684de458ee5a2 end -/
