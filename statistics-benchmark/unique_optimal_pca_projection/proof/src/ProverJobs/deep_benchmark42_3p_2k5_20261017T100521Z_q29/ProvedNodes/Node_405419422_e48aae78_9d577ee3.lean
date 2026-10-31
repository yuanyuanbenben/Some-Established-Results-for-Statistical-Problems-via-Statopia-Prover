import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q29.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q29.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q29.ProvedNodes.Node_231152612_c7bdfebf_9dc2168f

open Matrix

open Matrix

set_option autoImplicit false in
theorem statopia_math_node_405419422_e48aae78 : ∀ (n d : ℕ)
    (x : Fin n → Fin d → ℝ)
    (P : Matrix (Fin d) (Fin d) ℝ)
    (hPsymm : P.transpose = P)
    (hPidem : P * P = P),
    let S : Matrix (Fin d) (Fin d) ℝ :=
      (n : ℝ)⁻¹ • ∑ i, vecMulVec (x i) (x i);
    (n : ℝ)⁻¹ * ∑ i, dotProduct (x i - P *ᵥ x i) (x i - P *ᵥ x i)
      = S.trace - (P * S).trace := by
  /- @proof-region region.target-node.session.f709fb445da31b70 begin -/
  intro n d x P hPsymm hPidem
  dsimp only
  have hP : ∀ i j : Fin d, P i j = P j i := by
    intro i j
    have h := congrFun (congrFun hPsymm i) j
    simp only [Matrix.transpose_apply] at h
    exact h.symm
  have hbridge : ∀ a b : Fin d → ℝ, (P * vecMulVec a b).trace = dotProduct a (P *ᵥ b) := by
    intro a b
    have hmul : vecMulVec a b * P = vecMulVec a (P *ᵥ b) := by
      ext i j
      simp only [Matrix.mul_apply, Matrix.vecMulVec, Matrix.of_apply, Matrix.mulVec,
        dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [hP k j]
      ring
    rw [Matrix.trace_mul_comm, hmul, Matrix.trace_vecMulVec]
  have hS : ((n : ℝ)⁻¹ • ∑ i, vecMulVec (x i) (x i)).trace
      = (n : ℝ)⁻¹ * ∑ i, dotProduct (x i) (x i) := by
    rw [Matrix.trace_smul, Matrix.trace_sum]
    simp only [Matrix.trace_vecMulVec, smul_eq_mul]
  have hPS : (P * ((n : ℝ)⁻¹ • ∑ i, vecMulVec (x i) (x i))).trace
      = (n : ℝ)⁻¹ * ∑ i, dotProduct (x i) (P *ᵥ x i) := by
    rw [Matrix.mul_smul, Matrix.mul_sum, Matrix.trace_smul, Matrix.trace_sum]
    simp only [hbridge, smul_eq_mul]

  have hterm : ∀ i : Fin n, dotProduct (x i - P *ᵥ x i) (x i - P *ᵥ x i)
      = dotProduct (x i) (x i) - dotProduct (x i) (P *ᵥ x i) :=
    fun i => (statopia_math_node_231152612_c7bdfebf d P hPsymm hPidem (x i)).2
  rw [hS, hPS]
  simp only [hterm, Finset.sum_sub_distrib]
  ring
  /- @proof-region region.target-node.session.f709fb445da31b70 end -/
