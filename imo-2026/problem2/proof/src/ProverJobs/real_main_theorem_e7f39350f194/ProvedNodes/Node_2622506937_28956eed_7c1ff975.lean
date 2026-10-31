import ProverJobs.real_main_theorem_e7f39350f194.Vocabulary
import ProverJobs.real_main_theorem_e7f39350f194.Base
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_1132283172_4e5f8155_fd18bf12
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_3431605529_2a745110_37ebd9aa
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_981975689_c1054012_46ac252e
open EuclideanGeometry

open EuclideanGeometry

set_option autoImplicit false in
theorem statopia_math_node_2622506937_28956eed : ∀ (A B C K L : Plane)
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set Plane))
    (M N : Plane) (hM : M = midpoint ℝ A B) (hN : N = midpoint ℝ A C)
    (hK : InsideTriangle B M C K) (hL : InsideTriangle B N C L)
    (s t u v : ℝ)
    (hs : 0 < s) (hs1 : s < 1) (ht : 0 < t) (ht1 : t < 1)
    (hu : 0 < u) (hu1 : u < 1) (hv : 0 < v) (hv1 : v < 1)
    (X Y : Plane)
    (hY : Y = A + s • (C - A)) (hX : X = A + t • (B - A))
    (hKtrace : K = B + u • (Y - B)) (hLtrace : L = C + v • (X - C))
    (h3 : ∠ L C K = ∠ B M K) (ht2 : t = 1 / 2),
    ∃ U : Plane, ∃ r2 : ℝ,
      (‖C - U‖ ^ 2 - r2 = 0) ∧ (‖K - U‖ ^ 2 - r2 = 0) ∧ (‖M - U‖ ^ 2 - r2 = 0) ∧
      inner ℝ (B - A) (M - U) = 0 := by
  /- @proof-region region.target-node.session.83914b03da5b5b0b begin -/
  intro A B C K L hABC M N hM hN hK hL s t u v hs hs1 ht ht1 hu hu1 hv hv1 X Y hY hX hKtrace hLtrace h3 ht2
  have hMA : M - A = (2⁻¹ : ℝ) • (B - A) := by
    rw [hM, midpoint, AffineMap.lineMap_apply]
    simp only [vsub_eq_sub, vadd_eq_add]
    abel
  have hKA : K - A = (1 - u) • (B - A) + (u * s) • (C - A) := by
    rw [hKtrace, hY]
    module
  have hXM : X = M := by
    rw [hX, ht2]
    simp only [one_div]
    rw [← hMA]
    module
  have hLC : L - C = v • (M - C) := by
    rw [hLtrace, hXM]
    module
  obtain ⟨U, r2, hCU, hKU, hMU, htan⟩ :=
    statopia_math_node_1132283172_4e5f8155 A B C K L M v hABC hM hK hv hLC h3
  exact ⟨U, r2, hCU, hKU, hMU, htan⟩
  /- @proof-region region.target-node.session.83914b03da5b5b0b end -/
