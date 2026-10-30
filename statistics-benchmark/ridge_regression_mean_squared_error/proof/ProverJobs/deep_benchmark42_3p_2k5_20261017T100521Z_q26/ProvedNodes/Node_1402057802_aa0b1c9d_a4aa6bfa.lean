import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q26.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q26.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q26.ProvedNodes.Node_3749075562_82ca6ac8_7fe8f0fc

open MeasureTheory Matrix

open MeasureTheory Matrix

set_option autoImplicit false in
theorem statopia_math_node_1402057802_aa0b1c9d : ∀ {Ω : Type*}
    (n d : ℕ)
    (X : Matrix (Fin n) (Fin d) ℝ)
    (betaStar : Fin d → ℝ)
    (epsilon : Ω → Fin n → ℝ)
    (lambda : ℝ)
    (hinv_left : (X.transpose * X + lambda • 1)⁻¹ * (X.transpose * X + lambda • 1) = 1)
    (hinv_right : (X.transpose * X + lambda • 1) * (X.transpose * X + lambda • 1)⁻¹ = 1),
    let A : Matrix (Fin d) (Fin d) ℝ := X.transpose * X + lambda • 1
    let L : Matrix (Fin d) (Fin n) ℝ := A⁻¹ * X.transpose
    let c : Fin d → ℝ := A⁻¹ *ᵥ betaStar
    let y : Ω → Fin n → ℝ := fun ω => X *ᵥ betaStar + epsilon ω
    let betaHat : Ω → Fin d → ℝ := fun ω => A⁻¹ *ᵥ (X.transpose *ᵥ y ω)
    (∀ ω : Ω, betaHat ω - betaStar = L *ᵥ epsilon ω - lambda • c) ∧
      (∀ (ω : Ω) (k : Fin d),
        (betaHat ω - betaStar) k =
          (∑ i : Fin n, L k i * epsilon ω i) - lambda * c k) := by
  /- @proof-region region.target-node.session.31a71b56928fd632 begin -/
  intro Ω n d X betaStar epsilon lambda hinv_left hinv_right
  dsimp only
  have hBI : ∀ v : Fin d → ℝ,
      (X.transpose * X + lambda • 1)⁻¹ *ᵥ ((X.transpose * X + lambda • 1) *ᵥ v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, hinv_left, Matrix.one_mulVec]
  have hAbeta : (X.transpose * X + lambda • 1) *ᵥ betaStar
      = (X.transpose * X) *ᵥ betaStar + lambda • betaStar := by
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hXeps : ∀ ω : Ω, X.transpose *ᵥ (X *ᵥ betaStar + epsilon ω)
      = (X.transpose * X) *ᵥ betaStar + X.transpose *ᵥ epsilon ω := by
    intro ω
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec]
  have hBh : ∀ ω : Ω,
      (X.transpose * X + lambda • 1) *ᵥ ((X.transpose * X + lambda • 1)⁻¹ *ᵥ
          (X.transpose *ᵥ (X *ᵥ betaStar + epsilon ω)))
        = (X.transpose * X) *ᵥ betaStar + X.transpose *ᵥ epsilon ω := by
    intro ω
    rw [Matrix.mulVec_mulVec, hinv_right, Matrix.one_mulVec, hXeps ω]
  have hmain : ∀ ω : Ω,
      (X.transpose * X + lambda • 1)⁻¹ *ᵥ (X.transpose *ᵥ (X *ᵥ betaStar + epsilon ω)) - betaStar
        = ((X.transpose * X + lambda • 1)⁻¹ * X.transpose) *ᵥ epsilon ω
          - lambda • ((X.transpose * X + lambda • 1)⁻¹ *ᵥ betaStar) := by
    intro ω
    have key : (X.transpose * X + lambda • 1) *ᵥ
        ((X.transpose * X + lambda • 1)⁻¹ *ᵥ (X.transpose *ᵥ (X *ᵥ betaStar + epsilon ω))
          - betaStar)
          = X.transpose *ᵥ epsilon ω - lambda • betaStar := by
      rw [Matrix.mulVec_sub, hBh ω, hAbeta]
      abel
    calc (X.transpose * X + lambda • 1)⁻¹ *ᵥ (X.transpose *ᵥ (X *ᵥ betaStar + epsilon ω)) - betaStar
        = (X.transpose * X + lambda • 1)⁻¹ *ᵥ ((X.transpose * X + lambda • 1) *ᵥ
            ((X.transpose * X + lambda • 1)⁻¹ *ᵥ
              (X.transpose *ᵥ (X *ᵥ betaStar + epsilon ω)) - betaStar)) := by
            rw [hBI]
      _ = (X.transpose * X + lambda • 1)⁻¹ *ᵥ (X.transpose *ᵥ epsilon ω - lambda • betaStar) := by
            rw [key]
      _ = (X.transpose * X + lambda • 1)⁻¹ *ᵥ (X.transpose *ᵥ epsilon ω)
            - (X.transpose * X + lambda • 1)⁻¹ *ᵥ (lambda • betaStar) := by
            rw [Matrix.mulVec_sub]
      _ = ((X.transpose * X + lambda • 1)⁻¹ * X.transpose) *ᵥ epsilon ω
            - lambda • ((X.transpose * X + lambda • 1)⁻¹ *ᵥ betaStar) := by
            rw [Matrix.mulVec_mulVec, Matrix.mulVec_smul]
  exact ⟨hmain, fun ω k => congrFun (hmain ω) k⟩
  /- @proof-region region.target-node.session.31a71b56928fd632 end -/
