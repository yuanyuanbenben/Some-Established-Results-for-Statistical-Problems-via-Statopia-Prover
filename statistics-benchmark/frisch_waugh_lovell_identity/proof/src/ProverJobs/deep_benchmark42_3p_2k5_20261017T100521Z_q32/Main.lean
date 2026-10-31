import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q32.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q32.ProvedNodes
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q32.Base

open Matrix

theorem frisch_waugh_lovell_identity
    (n p q : ℕ) (hn : p + q ≤ n) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (X₁ : Matrix (Fin n) (Fin p) ℝ)
    (X₂ : Matrix (Fin n) (Fin q) ℝ)
    (y : Fin n → ℝ)
    (hfull : ∀ beta : Fin p → ℝ, ∀ gamma : Fin q → ℝ,
      X₁ *ᵥ beta + X₂ *ᵥ gamma = 0 → beta = 0 ∧ gamma = 0)
    (betaHat : Fin p → ℝ)
    (gammaHat : Fin q → ℝ)
    (hmin : ∀ beta : Fin p → ℝ, ∀ gamma : Fin q → ℝ,
      dotProduct (y - X₁ *ᵥ betaHat - X₂ *ᵥ gammaHat)
          (y - X₁ *ᵥ betaHat - X₂ *ᵥ gammaHat) ≤
        dotProduct (y - X₁ *ᵥ beta - X₂ *ᵥ gamma)
          (y - X₁ *ᵥ beta - X₂ *ᵥ gamma)) :
    let M₁ : Matrix (Fin n) (Fin n) ℝ :=
      1 - X₁ * (X₁.transpose * X₁)⁻¹ * X₁.transpose
    gammaHat =
      (X₂.transpose * M₁ * X₂)⁻¹ *ᵥ
        (X₂.transpose *ᵥ (M₁ *ᵥ y))
:= by
  /- @proof-region region.root.ded0cc0401c4 begin -/
  dsimp only
  obtain ⟨hres1, hres2⟩ :=
    statopia_math_node_3562999774_d294b84d n p q X₁ X₂ y betaHat gammaHat hmin
  have hinj : ∀ u : Fin p → ℝ, X₁ *ᵥ u = 0 → u = 0 := by
    intro u hu
    exact (hfull u 0 (by simpa using hu)).1
  set A : Matrix (Fin p) (Fin p) ℝ := X₁.transpose * X₁ with hA
  set P : Matrix (Fin n) (Fin n) ℝ := X₁ * A⁻¹ * X₁.transpose with hP
  set M : Matrix (Fin n) (Fin n) ℝ := 1 - P with hM
  set S : Matrix (Fin q) (Fin q) ℝ := X₂.transpose * M * X₂ with hS
  set b : Fin q → ℝ := X₂.transpose *ᵥ (M *ᵥ y) with hb
  have hAherm : A.IsHermitian := by
    rw [hA]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_conjTranspose_mul_self X₁
  have hApos : A.PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos hAherm ?_
    intro x hx
    have hne : X₁ *ᵥ x ≠ 0 := fun h => hx (hinj x h)
    have hpos : 0 < (X₁ *ᵥ x) ⬝ᵥ (X₁ *ᵥ x) := by
      simpa using (Matrix.dotProduct_self_star_pos_iff (v := X₁ *ᵥ x)).2 hne
    rw [hA, ← Matrix.mulVec_mulVec]
    have hst : star x = x := by
      funext i
      simp
    rw [hst, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    exact hpos
  have hAunit : IsUnit A.det :=
    (Matrix.isUnit_iff_isUnit_det A).1 (Matrix.PosDef.isUnit hApos)
  have hAmul : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hAunit
  have hinvmul : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hAunit
  have hAT : A.transpose = A := by
    rw [hA, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hinvT : A⁻¹.transpose = A⁻¹ := by
    have hTA : A * A⁻¹.transpose = 1 := by
      have h : (A⁻¹ * A).transpose = A * A⁻¹.transpose := by
        rw [Matrix.transpose_mul, hAT]
      rw [← h, hinvmul, Matrix.transpose_one]
    rw [← Matrix.nonsing_inv_mul_cancel_left A A⁻¹.transpose hAunit, hTA, Matrix.mul_one]
  have hPsym : P.transpose = P := by
    simp only [hP, Matrix.transpose_mul, Matrix.transpose_transpose, hinvT,
      Matrix.mul_assoc]
  have hPidem : P * P = P := by
    have hmid : A⁻¹ * X₁.transpose * X₁ * A⁻¹ = A⁻¹ := by
      have h1 : X₁.transpose * X₁ = A := hA.symm
      calc A⁻¹ * X₁.transpose * X₁ * A⁻¹ = A⁻¹ * (X₁.transpose * X₁) * A⁻¹ := by
            simp only [Matrix.mul_assoc]
        _ = A⁻¹ * A * A⁻¹ := by rw [h1]
        _ = 1 * A⁻¹ := by rw [hinvmul]
        _ = A⁻¹ := Matrix.one_mul _
    rw [hP]
    calc (X₁ * A⁻¹ * X₁.transpose) * (X₁ * A⁻¹ * X₁.transpose)
        = X₁ * (A⁻¹ * X₁.transpose * X₁ * A⁻¹) * X₁.transpose := by
          simp only [Matrix.mul_assoc]
      _ = X₁ * A⁻¹ * X₁.transpose := by rw [hmid]
  have hMT : M.transpose = M := by
    rw [hM, Matrix.transpose_sub, Matrix.transpose_one, hPsym]
  have hMM : M * M = M := by
    have hP0 : P * (1 - P) = 0 := by
      rw [Matrix.mul_sub, Matrix.mul_one, hPidem, sub_self]
    rw [hM, Matrix.sub_mul, Matrix.one_mul, hP0, sub_zero]
  have hMsym : (1 - X₁ * (X₁.transpose * X₁)⁻¹ * X₁.transpose).transpose
      = 1 - X₁ * (X₁.transpose * X₁)⁻¹ * X₁.transpose := by
    rw [← hA, ← hP, ← hM]
    exact hMT
  have hMidem : (1 - X₁ * (X₁.transpose * X₁)⁻¹ * X₁.transpose)
        * (1 - X₁ * (X₁.transpose * X₁)⁻¹ * X₁.transpose)
      = 1 - X₁ * (X₁.transpose * X₁)⁻¹ * X₁.transpose := by
    rw [← hA, ← hP, ← hM]
    exact hMM
  have hXu : X₁.transpose *ᵥ (y - X₂ *ᵥ gammaHat)
      = X₁.transpose *ᵥ y - (X₁.transpose * X₂) *ᵥ gammaHat := by
    simp only [Matrix.mulVec_sub, Matrix.mulVec_mulVec]
  have hexp1 : X₁.transpose *ᵥ (y - X₁ *ᵥ betaHat - X₂ *ᵥ gammaHat)
      = X₁.transpose *ᵥ y - A *ᵥ betaHat - (X₁.transpose * X₂) *ᵥ gammaHat := by
    rw [hA]
    simp only [Matrix.mulVec_sub, Matrix.mulVec_mulVec]
  have hAβ : A *ᵥ betaHat = X₁.transpose *ᵥ (y - X₂ *ᵥ gammaHat) := by
    rw [hXu]
    have h := hres1
    rw [hexp1] at h
    funext i
    have hi := congrFun h i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply] at hi ⊢
    linarith
  have hbeta : betaHat = A⁻¹ *ᵥ (X₁.transpose *ᵥ (y - X₂ *ᵥ gammaHat)) := by
    rw [← hAβ, Matrix.mulVec_mulVec, hinvmul, Matrix.one_mulVec]
  have hXβ : X₁ *ᵥ betaHat = P *ᵥ (y - X₂ *ᵥ gammaHat) := by
    rw [hbeta, hP]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hexp2 : X₂.transpose *ᵥ (y - X₁ *ᵥ betaHat - X₂ *ᵥ gammaHat)
      = X₂.transpose *ᵥ y - (X₂.transpose * X₁) *ᵥ betaHat
        - (X₂.transpose * X₂) *ᵥ gammaHat := by
    simp only [Matrix.mulVec_sub, Matrix.mulVec_mulVec]
  have hblk2 : (X₂.transpose * X₁) *ᵥ betaHat + (X₂.transpose * X₂) *ᵥ gammaHat
      = X₂.transpose *ᵥ y := by
    have h := hres2
    rw [hexp2] at h
    funext i
    have hi := congrFun h i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply] at hi ⊢
    linarith
  have hkey : X₂.transpose *ᵥ (X₂ *ᵥ gammaHat)
        - X₂.transpose *ᵥ (P *ᵥ (X₂ *ᵥ gammaHat))
      = X₂.transpose *ᵥ y - X₂.transpose *ᵥ (P *ᵥ y) := by
    have h2 := hblk2
    simp only [← Matrix.mulVec_mulVec] at h2
    rw [hXβ] at h2
    simp only [Matrix.mulVec_sub] at h2
    funext i
    have hi := congrFun h2 i
    simp only [Pi.add_apply, Pi.sub_apply] at hi ⊢
    linarith
  have hSγ : S *ᵥ gammaHat = b := by
    have h1 : S *ᵥ gammaHat = X₂.transpose *ᵥ ((1 - P) *ᵥ (X₂ *ᵥ gammaHat)) := by
      rw [hS, hM]
      simp only [← Matrix.mulVec_mulVec]
    have h2 : X₂.transpose *ᵥ ((1 - P) *ᵥ (X₂ *ᵥ gammaHat))
        = X₂.transpose *ᵥ (X₂ *ᵥ gammaHat)
          - X₂.transpose *ᵥ (P *ᵥ (X₂ *ᵥ gammaHat)) := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub]
    have h4 : X₂.transpose *ᵥ y - X₂.transpose *ᵥ (P *ᵥ y)
        = X₂.transpose *ᵥ ((1 - P) *ᵥ y) := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub]
    rw [h1, h2, hkey, h4]
  obtain ⟨hStrans, hSpos⟩ :=
    statopia_math_node_1575886460_f109d5e3 n p q X₁ X₂ hfull hMsym hMidem
  have hSsym : S.transpose = S := by
    rw [hS, hM, hP, hA]
    exact hStrans
  have hSsymH : S.conjTranspose = S := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, hSsym]
  have hSposdef : S.PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos hSsymH ?_
    intro v hv
    have hp : 0 < v ⬝ᵥ (S *ᵥ v) := by
      have h := hSpos v hv
      rwa [← hA, ← hP, ← hM, ← hS] at h
    simpa using hp
  have hSun : IsUnit S.det :=
    (Matrix.isUnit_iff_isUnit_det S).1 (Matrix.PosDef.isUnit hSposdef)
  have hSinv : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hSun
  rw [← hSγ, Matrix.mulVec_mulVec, hSinv, Matrix.one_mulVec]
  /- @proof-region region.root.ded0cc0401c4 end -/
