import ProverJobs.real_main_theorem_e7f39350f194.Vocabulary
import ProverJobs.real_main_theorem_e7f39350f194.Base
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_3469497786_231dbb85_34eaf8d3
open EuclideanGeometry

open EuclideanGeometry

set_option autoImplicit false in
theorem statopia_math_node_81477081_e9900e38 : ∀ (A B C : Plane)
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set Plane)) (P Q : ℝ),
    ∃ W : Plane, inner ℝ (B - A) W = P ∧ inner ℝ (C - A) W = Q := by
  /- @proof-region region.target-node.session.1d57fac72a377e85 begin -/
  intro A B C hABC P Q
  let D : ℝ := ‖B - A‖ ^ 2 * ‖C - A‖ ^ 2 - (inner ℝ (B - A) (C - A)) ^ 2
  have hDdef : D = ‖B - A‖ ^ 2 * ‖C - A‖ ^ 2 - (inner ℝ (B - A) (C - A)) ^ 2 := rfl
  have hD : D ≠ 0 := by
    rw [hDdef]
    exact statopia_math_node_3469497786_231dbb85 A B C hABC
  refine ⟨((P * ‖C - A‖ ^ 2 - Q * inner ℝ (B - A) (C - A)) / D) • (B - A)
      + ((Q * ‖B - A‖ ^ 2 - P * inner ℝ (B - A) (C - A)) / D) • (C - A),
      ?_, ?_⟩
  · rw [inner_add_right, inner_smul_right, inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
    rw [hDdef]
    ring
  · have hcomm : inner ℝ (C - A) (B - A) = inner ℝ (B - A) (C - A) := by
      rw [real_inner_comm]
    rw [inner_add_right, inner_smul_right, inner_smul_right, real_inner_self_eq_norm_sq, hcomm]
    field_simp
    rw [hDdef]
    ring
  /- @proof-region region.target-node.session.1d57fac72a377e85 end -/
