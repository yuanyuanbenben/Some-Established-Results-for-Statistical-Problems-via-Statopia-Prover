import ProverJobs.real_main_theorem_e7f39350f194.Vocabulary
import ProverJobs.real_main_theorem_e7f39350f194.Base
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_1009185205_43daf791_8c70c533
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_1641763193_b67e03b9_e850df6b
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_3431605529_2a745110_37ebd9aa
open EuclideanGeometry

open EuclideanGeometry

set_option autoImplicit false in
theorem statopia_math_node_393965618_6807243a : ∀ (A B C K L : Plane)
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set Plane))
    (M N : Plane) (hM : M = midpoint ℝ A B) (hN : N = midpoint ℝ A C)
    (hK : InsideTriangle B M C K) (hL : InsideTriangle B N C L)
    (hKangle : InsideAngle L B A K)
    (s t u v : ℝ)
    (hs : 0 < s) (hs1 : s < 1) (ht : 0 < t) (ht1 : t < 1)
    (hu : 0 < u) (hu1 : u < 1) (hv : 0 < v) (hv1 : v < 1)
    (Y X : Plane) (hY : Y = A + s • (C - A)) (hX : X = A + t • (B - A))
    (hLtrace : L = C + v • (X - C)) (hKtrace : K = B + u • (Y - B))
    (h2 : ∠ L B K = ∠ L N C),
    ∃ U : Plane, ∃ r2 : ℝ,
      (‖B - U‖ ^ 2 - r2 = 0) ∧ (‖L - U‖ ^ 2 - r2 = 0) ∧ (‖N - U‖ ^ 2 - r2 = 0) ∧
        (s = 1 / 2 → inner ℝ (C - A) (N - U) = 0) ∧
        (s ≠ 1 / 2 → (‖Y - U‖ ^ 2 - r2 = 0)) := by
  /- @proof-region region.target-node.session.233f1770fe3168e9 begin -/
  intro A B C K L hABC M N hM hN hK hL hKangle s t u v hs hs1 ht ht1 hu hu1 hv hv1 Y X hY hX hLtrace hKtrace h2
  obtain ⟨U, r2, hBU, hLU, hNU⟩ :=
    statopia_math_node_1641763193_b67e03b9 A B C N L X t v hABC hN hL hX hLtrace
  obtain ⟨htan, hYU⟩ :=
    statopia_math_node_1009185205_43daf791 A B C K L hABC M N hM hN hK hL hKangle
      s t u v hs hs1 ht ht1 hu hu1 hv hv1 Y X hY hX hLtrace hKtrace h2 U r2 hBU hLU hNU
  exact ⟨U, r2, hBU, hLU, hNU, htan, hYU⟩
  /- @proof-region region.target-node.session.233f1770fe3168e9 end -/
