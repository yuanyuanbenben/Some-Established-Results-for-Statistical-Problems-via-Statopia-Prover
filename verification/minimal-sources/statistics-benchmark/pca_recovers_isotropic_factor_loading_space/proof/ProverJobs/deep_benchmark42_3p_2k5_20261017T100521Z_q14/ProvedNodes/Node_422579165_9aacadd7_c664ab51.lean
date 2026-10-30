import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q14.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q14.Base

open MeasureTheory Matrix

open MeasureTheory Matrix

set_option autoImplicit false in
theorem statopia_math_node_422579165_9aacadd7 : ∀ (d q : ℕ) (Lambda : Matrix (Fin d) (Fin q) ℝ)
    (v : Fin d → ℝ) (lam : ℝ)
    (hv : dotProduct v v = 1)
    (heig : (Lambda * Lambda.transpose) *ᵥ v = lam • v),
    lam = dotProduct (Lambda.transpose *ᵥ v) (Lambda.transpose *ᵥ v) ∧ 0 ≤ lam := by
  /- @proof-region region.target-node.session.28b988fa8b817446 begin -/
  intro d q Lambda v lam hv heig
  have hkey : lam = dotProduct (Lambda.transpose *ᵥ v) (Lambda.transpose *ᵥ v) := by
    calc lam = lam * dotProduct v v := by rw [hv, mul_one]
      _ = dotProduct v (lam • v) := by rw [dotProduct_smul]; simp
      _ = dotProduct v ((Lambda * Lambda.transpose) *ᵥ v) := by rw [heig]
      _ = dotProduct v (Lambda *ᵥ (Lambda.transpose *ᵥ v)) := by rw [← Matrix.mulVec_mulVec]
      _ = Matrix.vecMul v Lambda ⬝ᵥ (Lambda.transpose *ᵥ v) := by rw [Matrix.dotProduct_mulVec]
      _ = (Lambda.transpose *ᵥ v) ⬝ᵥ (Lambda.transpose *ᵥ v) := by rw [← Matrix.mulVec_transpose]
  refine ⟨hkey, ?_⟩
  rw [hkey]
  have hnn : 0 ≤ ∑ i, (Lambda.transpose *ᵥ v) i * (Lambda.transpose *ᵥ v) i :=
    Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  simpa [dotProduct] using hnn
  /- @proof-region region.target-node.session.28b988fa8b817446 end -/
