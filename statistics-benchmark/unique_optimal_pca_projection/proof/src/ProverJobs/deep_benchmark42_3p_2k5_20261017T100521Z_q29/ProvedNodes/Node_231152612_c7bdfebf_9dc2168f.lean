import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q29.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q29.Base

open Matrix

open Matrix

set_option autoImplicit false in
theorem statopia_math_node_231152612_c7bdfebf : ∀ (d : ℕ)
    (P : Matrix (Fin d) (Fin d) ℝ)
    (hPsymm : P.transpose = P) (hPidem : P * P = P),
    ∀ u : Fin d → ℝ,
      (dotProduct (P *ᵥ u) (P *ᵥ u) = dotProduct u (P *ᵥ u)) ∧
      (dotProduct (u - P *ᵥ u) (u - P *ᵥ u)
        = dotProduct u u - dotProduct u (P *ᵥ u)) := by
  /- @proof-region region.target-node.session.676625b0db7b9d74 begin -/
  intro d P hPsymm hPidem u
  have hcomm : ∀ x y : Fin d → ℝ, dotProduct x y = dotProduct y x := by
    intro x y
    simp only [dotProduct]
    exact Finset.sum_congr rfl fun i _ => mul_comm (x i) (y i)
  have hsub_lhs : ∀ x y z : Fin d → ℝ,
      dotProduct (x - y) z = dotProduct x z - dotProduct y z := by
    intro x y z
    simp only [dotProduct, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  have hsub_rhs : ∀ x y z : Fin d → ℝ,
      dotProduct x (y - z) = dotProduct x y - dotProduct x z := by
    intro x y z
    simp only [dotProduct, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  have hadj : ∀ x y : Fin d → ℝ, dotProduct (P *ᵥ x) y = dotProduct x (P *ᵥ y) := by
    intro x y
    have hvec : vecMul y P = P.transpose *ᵥ y := by
      simpa using Matrix.vecMul_transpose (A := P.transpose) y
    rw [hcomm (P *ᵥ x) y, Matrix.dotProduct_mulVec, hvec, hPsymm]
    exact hcomm (P *ᵥ y) x
  have hmul : P *ᵥ (P *ᵥ u) = P *ᵥ u := by
    rw [Matrix.mulVec_mulVec, hPidem]
  have h1 : dotProduct (P *ᵥ u) (P *ᵥ u) = dotProduct u (P *ᵥ u) := by
    rw [hadj u (P *ᵥ u), hmul]
  refine ⟨h1, ?_⟩
  rw [hsub_lhs u (P *ᵥ u) (u - P *ᵥ u), hsub_rhs u u (P *ᵥ u),
    hsub_rhs (P *ᵥ u) u (P *ᵥ u), hcomm (P *ᵥ u) u, h1]
  ring
  /- @proof-region region.target-node.session.676625b0db7b9d74 end -/
