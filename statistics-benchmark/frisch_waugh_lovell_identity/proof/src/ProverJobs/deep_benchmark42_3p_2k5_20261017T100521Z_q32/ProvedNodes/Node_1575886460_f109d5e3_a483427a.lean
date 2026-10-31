import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q32.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q32.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q32.ProvedNodes.Node_1920263288_2edd7d1c_bebb8998

open Matrix

open Matrix

set_option autoImplicit false in
theorem statopia_math_node_1575886460_f109d5e3 : ∀ (n p q : ℕ)
    (X1 : Matrix (Fin n) (Fin p) ℝ)
    (X2 : Matrix (Fin n) (Fin q) ℝ)
    (hfull : ∀ (u : Fin p → ℝ) (v : Fin q → ℝ),
      X1 *ᵥ u + X2 *ᵥ v = 0 → u = 0 ∧ v = 0)
    (hMsym : (1 - X1 * (X1.transpose * X1)⁻¹ * X1.transpose).transpose =
      1 - X1 * (X1.transpose * X1)⁻¹ * X1.transpose)
    (hMidem : (1 - X1 * (X1.transpose * X1)⁻¹ * X1.transpose) *
        (1 - X1 * (X1.transpose * X1)⁻¹ * X1.transpose) =
      1 - X1 * (X1.transpose * X1)⁻¹ * X1.transpose),
    let M1 : Matrix (Fin n) (Fin n) ℝ :=
      1 - X1 * (X1.transpose * X1)⁻¹ * X1.transpose
    let S : Matrix (Fin q) (Fin q) ℝ := X2.transpose * M1 * X2
    S.transpose = S ∧ ∀ v : Fin q → ℝ, v ≠ 0 → 0 < v ⬝ᵥ (S *ᵥ v) := by
  /- @proof-region region.target-node.session.3420b7b53b7353b1 begin -/
  intro n p q X1 X2 hfull hMsym hMidem
  dsimp only
  set Ainv : Matrix (Fin p) (Fin p) ℝ := (X1.transpose * X1)⁻¹ with hAinv
  set M1 : Matrix (Fin n) (Fin n) ℝ := 1 - X1 * Ainv * X1.transpose with hM1
  set S : Matrix (Fin q) (Fin q) ℝ := X2.transpose * M1 * X2 with hS
  have hMsym' : M1.transpose = M1 := hMsym
  have hMidem' : M1 * M1 = M1 := hMidem
  have hMtM : M1.transpose * M1 = M1 := by rw [hMsym', hMidem']
  have hnegmul : ∀ (A : Matrix (Fin n) (Fin p) ℝ) (x : Fin p → ℝ), A *ᵥ (-x) = -(A *ᵥ x) := by
    intro A x
    have h0 : A *ᵥ (0 : Fin p → ℝ) = 0 := by
      simpa using Matrix.mulVec_sub A x x
    rw [← zero_sub x, Matrix.mulVec_sub, h0, zero_sub]
  have hre : ∀ {m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (x : Fin m → ℝ) (z : Fin n → ℝ),
      (A *ᵥ x) ⬝ᵥ z = x ⬝ᵥ (A.transpose *ᵥ z) := by
    intro m A x z
    rw [Matrix.dotProduct_mulVec x A.transpose z, Matrix.vecMul_transpose]
  constructor
  · simp only [hS, Matrix.transpose_mul, Matrix.transpose_transpose, hMsym', Matrix.mul_assoc]
  · intro v hv
    set y : Fin n → ℝ := X2 *ᵥ v with hy
    have hvec : (X1 * Ainv * X1.transpose) *ᵥ y = X1 *ᵥ (Ainv *ᵥ (X1.transpose *ᵥ y)) := by
      rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    set w : Fin p → ℝ := -(Ainv *ᵥ (X1.transpose *ᵥ y)) with hw
    have hXw : X1 *ᵥ w = -(X1 *ᵥ (Ainv *ᵥ (X1.transpose *ᵥ y))) := by
      rw [hw, hnegmul]
    have hblock : M1 *ᵥ y = y + X1 *ᵥ w := by
      rw [hM1, hXw, Matrix.sub_mulVec, Matrix.one_mulVec, hvec, sub_eq_add_neg]
    have hSvec : S *ᵥ v = X2.transpose *ᵥ (M1 *ᵥ y) := by
      rw [hS, hy, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have hdot1 : v ⬝ᵥ (S *ᵥ v) = y ⬝ᵥ (M1 *ᵥ y) := by
      rw [hSvec, ← hre X2 v (M1 *ᵥ y), hy]
    have hstep : ∀ x : Fin n → ℝ, M1 *ᵥ x = M1.transpose *ᵥ (M1 *ᵥ x) := by
      intro x
      rw [Matrix.mulVec_mulVec, hMtM]
    have hdot2 : y ⬝ᵥ (M1 *ᵥ y) = (M1 *ᵥ y) ⬝ᵥ (M1 *ᵥ y) :=
      (congrArg (fun t : Fin n → ℝ => y ⬝ᵥ t) (hstep y)).trans
        (hre M1 y (M1 *ᵥ y)).symm


    have hz : M1 *ᵥ y ≠ 0 := by
      intro h
      have h2 : y + X1 *ᵥ w = 0 := by
        rw [← hblock]
        exact h
      rw [hy] at h2
      have h1 : X1 *ᵥ w + X2 *ᵥ v = 0 := by
        rw [add_comm]
        exact h2
      obtain ⟨-, hv0⟩ := hfull w v h1
      exact hv hv0
    have hpos : 0 < (M1 *ᵥ y) ⬝ᵥ (M1 *ᵥ y) := by
      have h := (Matrix.dotProduct_self_star_pos_iff (R := ℝ) (v := M1 *ᵥ y)).mpr hz
      simpa using h
    rw [hdot1, hdot2]
    exact hpos

  /- @proof-region region.target-node.session.3420b7b53b7353b1 end -/
