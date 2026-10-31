import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q14.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q14.Base

open MeasureTheory Matrix

open MeasureTheory Matrix

set_option autoImplicit false in
theorem statopia_math_node_2814431898_39cb855d : ∀ (d q : ℕ) (Lambda : Matrix (Fin d) (Fin q) ℝ)
    (hLambda : Function.Injective Lambda.mulVec),
    LinearMap.range (Lambda * Lambda.transpose).mulVecLin
        = LinearMap.range Lambda.mulVecLin ∧
      Module.finrank ℝ ↥(LinearMap.range Lambda.mulVecLin) = q ∧
      Module.finrank ℝ ↥(LinearMap.range (Lambda * Lambda.transpose).mulVecLin) = q := by
  /- @proof-region region.target-node.session.4ebf80ca99999fae begin -/
  intro d q Lambda hLambda
  have hAker : Lambda.mulVecLin.ker = ⊥ := by
    rw [Matrix.ker_mulVecLin_eq_bot_iff]
    intro v hv
    exact hLambda (by simpa using hv)
  have hCker : (Lambda.transpose * Lambda).mulVecLin.ker = ⊥ := by
    rw [Matrix.ker_mulVecLin_transpose_mul_self]
    exact hAker
  have hCtop : (Lambda.transpose * Lambda).mulVecLin.range = ⊤ := by
    refine (LinearMap.ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank
      (show Module.finrank ℝ (Fin q → ℝ) = Module.finrank ℝ (Fin q → ℝ) from rfl)).mp ?_
    exact hCker
  have hBC : (Lambda.transpose * Lambda).mulVecLin.range ≤ Lambda.transpose.mulVecLin.range := by
    intro x hx
    rw [LinearMap.mem_range] at hx ⊢
    obtain ⟨z, rfl⟩ := hx
    exact ⟨Lambda *ᵥ z, by simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]⟩
  have hBtop : Lambda.transpose.mulVecLin.range = ⊤ := by
    refine le_antisymm le_top ?_
    rw [hCtop] at hBC
    exact hBC
  have hmain : (Lambda * Lambda.transpose).mulVecLin.range = Lambda.mulVecLin.range := by
    refine le_antisymm ?_ ?_
    · intro x hx
      rw [LinearMap.mem_range] at hx ⊢
      obtain ⟨y, rfl⟩ := hx
      exact ⟨Lambda.transpose *ᵥ y, by
        simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]⟩
    · intro x hx
      rw [LinearMap.mem_range] at hx ⊢
      obtain ⟨z, rfl⟩ := hx
      have hz : z ∈ Lambda.transpose.mulVecLin.range := by
        rw [hBtop]
        trivial
      rw [LinearMap.mem_range] at hz
      obtain ⟨y, hy⟩ := hz
      refine ⟨y, ?_⟩
      rw [← hy]
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
  have hfinA : Module.finrank ℝ ↥(Lambda.mulVecLin.range) = q := by
    have h := LinearMap.finrank_range_add_finrank_ker
      (Lambda.mulVecLin : (Fin q → ℝ) →ₗ[ℝ] (Fin d → ℝ))
    rw [hAker, Module.finrank_fin_fun ℝ] at h
    simpa using h
  exact ⟨hmain, hfinA, by rw [hmain]; exact hfinA⟩
  /- @proof-region region.target-node.session.4ebf80ca99999fae end -/
