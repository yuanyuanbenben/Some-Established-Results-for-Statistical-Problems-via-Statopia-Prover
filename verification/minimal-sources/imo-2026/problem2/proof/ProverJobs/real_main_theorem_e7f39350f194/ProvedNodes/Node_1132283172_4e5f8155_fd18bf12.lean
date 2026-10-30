import ProverJobs.real_main_theorem_e7f39350f194.Vocabulary
import ProverJobs.real_main_theorem_e7f39350f194.Base
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_3104088338_a1318138_0aa6cce4
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_3431605529_2a745110_37ebd9aa
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_507356754_65c92604_8612fcae
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_981975689_c1054012_46ac252e
open EuclideanGeometry

open EuclideanGeometry

set_option autoImplicit false in
theorem statopia_math_node_1132283172_4e5f8155 : ∀ (A B C K L M : Plane) (v : ℝ)
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set Plane))
    (hM : M = midpoint ℝ A B)
    (hK : InsideTriangle B M C K)
    (hv : 0 < v)
    (hLC : L - C = v • (M - C))
    (h3 : ∠ L C K = ∠ B M K),
    ∃ U : Plane, ∃ r2 : ℝ,
      (‖C - U‖ ^ 2 - r2 = 0) ∧ (‖K - U‖ ^ 2 - r2 = 0) ∧ (‖M - U‖ ^ 2 - r2 = 0) ∧
      inner ℝ (B - A) (M - U) = 0 := by
  /- @proof-region region.target-node.session.28e583a633975b2f begin -/
  intro A B C K L M v hABC hM hK hv hLC h3
  have hMCK : ∠ M C K = ∠ B M K := by
    rw [← h3]
    have hinner : inner ℝ (L - C) (K - C) = v * inner ℝ (M - C) (K - C) := by
      rw [hLC]
      rw [Statlib.HighDim.Vocabulary.inner_eq_sum, Statlib.HighDim.Vocabulary.inner_eq_sum,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      have hcomp : (v • (M - C) : Plane).ofLp i = v * (M - C).ofLp i := by
        simp [smul_eq_mul]
      rw [hcomp]
      ring
    have hnorm : ‖L - C‖ = v * ‖M - C‖ := by
      rw [hLC, norm_smul, Real.norm_of_nonneg hv.le]
    have harg : inner ℝ (M - C) (K - C) / (‖M - C‖ * ‖K - C‖)
        = inner ℝ (L - C) (K - C) / (‖L - C‖ * ‖K - C‖) := by
      rw [hinner, hnorm, mul_assoc]
      by_cases hden : ‖M - C‖ * ‖K - C‖ = 0
      · rw [hden]
        simp
      · have h2 : v * (‖M - C‖ * ‖K - C‖) ≠ 0 := mul_ne_zero hv.ne' hden
        field_simp [hden, h2]
    unfold angle InnerProductGeometry.angle
    congr 1
  have hnc : ¬ Collinear ℝ ({C, K, M} : Set Plane) :=
    statopia_math_node_3104088338_a1318138 A B C K M hABC hM hK
  obtain ⟨U, r2, hCU, hKU, hMU⟩ :=
    statopia_math_node_981975689_c1054012 C K M hnc (0 : ℝ) (0 : ℝ)
  have htan : inner ℝ (B - A) (M - U) = 0 :=
    statopia_math_node_507356754_65c92604 A B C K M U r2 hABC hM hK hMCK hCU hKU hMU
  exact ⟨U, r2, hCU, hKU, hMU, htan⟩
  /- @proof-region region.target-node.session.28e583a633975b2f end -/
