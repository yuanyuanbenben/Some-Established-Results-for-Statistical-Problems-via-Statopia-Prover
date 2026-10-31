import ProverJobs.real_main_theorem_e7f39350f194.Vocabulary
import ProverJobs.real_main_theorem_e7f39350f194.Base
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_1079600542_410cd104_a404688e
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_1167546614_414fb77c_d86710ea
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_2622506937_28956eed_7c1ff975
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_3431605529_2a745110_37ebd9aa
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_353979784_5af30e36_38420c98
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_981975689_c1054012_46ac252e
open EuclideanGeometry

open EuclideanGeometry

set_option autoImplicit false in
theorem statopia_math_node_4006387899_007deac2 : ∀ (A B C K L : Plane)
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set Plane))
    (M N : Plane) (hM : M = midpoint ℝ A B) (hN : N = midpoint ℝ A C)
    (hK : InsideTriangle B M C K) (hL : InsideTriangle B N C L)
    (s t u v : ℝ)
    (hs : 0 < s) (hs1 : s < 1) (ht : 0 < t) (ht1 : t < 1)
    (hu : 0 < u) (hu1 : u < 1) (hv : 0 < v) (hv1 : v < 1)
    (X Y : Plane)
    (hY : Y = A + s • (C - A)) (hX : X = A + t • (B - A))
    (hKtrace : K = B + u • (Y - B)) (hLtrace : L = C + v • (X - C))
    (h3 : ∠ L C K = ∠ B M K)
    (hbranch : t < 1 / 2 ∨ 0 < (1 - u) - t * (1 - u * s)),
    ∃ U : Plane, ∃ r2 : ℝ,
      (‖C - U‖ ^ 2 - r2 = 0) ∧ (‖K - U‖ ^ 2 - r2 = 0) ∧ (‖M - U‖ ^ 2 - r2 = 0) ∧
      (t ≠ 1 / 2 → ‖X - U‖ ^ 2 - r2 = 0) ∧
      (t = 1 / 2 → inner ℝ (B - A) (M - U) = 0) := by
  /- @proof-region region.target-node.session.2cb50142312ecaca begin -/
  intro A B C K L hABC M N hM hN hK hL s t u v hs hs1 ht ht1 hu hu1 hv hv1 X Y hY hX hKtrace hLtrace h3 hbranch
  by_cases hth : t = 1 / 2
  · obtain ⟨U, r2, hCU, hKU, hMU, htan⟩ :=
      statopia_math_node_2622506937_28956eed A B C K L hABC M N hM hN hK hL
        s t u v hs hs1 ht ht1 hu hu1 hv hv1 X Y hY hX hKtrace hLtrace h3 hth
    exact ⟨U, r2, hCU, hKU, hMU, (fun h => absurd hth h), fun _ => htan⟩
  · obtain ⟨U, r2, hCU, hKU, hMU, hXU⟩ :=
      statopia_math_node_1167546614_414fb77c A B C K L hABC M N hM hN hK hL
        s t u v hs hs1 ht ht1 hu hu1 hv hv1 X Y hY hX hKtrace hLtrace h3 hbranch hth
    exact ⟨U, r2, hCU, hKU, hMU, fun _ => hXU, fun h => absurd h hth⟩
  /- @proof-region region.target-node.session.2cb50142312ecaca end -/
