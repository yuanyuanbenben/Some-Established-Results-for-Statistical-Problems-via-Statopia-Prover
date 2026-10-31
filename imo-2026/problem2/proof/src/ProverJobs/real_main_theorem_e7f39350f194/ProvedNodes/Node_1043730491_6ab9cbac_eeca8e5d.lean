import ProverJobs.real_main_theorem_e7f39350f194.Vocabulary
import ProverJobs.real_main_theorem_e7f39350f194.Base
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_302587009_faa16c35_f3bee5f9
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_81477081_e9900e38_e6ba2edb
open EuclideanGeometry

open EuclideanGeometry

set_option autoImplicit false in
theorem statopia_math_node_1043730491_6ab9cbac : ∀ (A B C K L : Plane)
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set Plane))
    (M N : Plane) (hM : M = midpoint ℝ A B) (hN : N = midpoint ℝ A C)
    (hK : InsideTriangle B M C K) (hL : InsideTriangle B N C L)
    (hKangle : InsideAngle L B A K) (hLangle : InsideAngle A C K L)
    (h2 : ∠ L B K = ∠ L N C) (h3 : ∠ L C K = ∠ B M K)
    (s t u v : ℝ)
    (hs : 0 < s) (hs1 : s < 1) (ht : 0 < t) (ht1 : t < 1)
    (hu : 0 < u) (hu1 : u < 1) (hv : 0 < v) (hv1 : v < 1)
    (X Y : Plane)
    (hY : Y = A + s • (C - A)) (hX : X = A + t • (B - A))
    (hKu : K = B + u • (Y - B)) (hLv : L = C + v • (X - C))
    (hE : dist A B ^ 2 * t = dist A C ^ 2 * s),
    ∃ (U : Plane) (r2 : ℝ),
      ‖A - U‖ ^ 2 - r2 = 0 ∧ ‖K - U‖ ^ 2 - r2 = 0 ∧ ‖L - U‖ ^ 2 - r2 = 0 ∧
      ‖B - U‖ ^ 2 - r2 = dist A B ^ 2 * (1 - t) / 2 ∧
      ‖C - U‖ ^ 2 - r2 = dist A C ^ 2 * (1 - s) / 2 := by
  /- @proof-region region.target-node.session.dc6656d1d8deb057 begin -/
  intro A B C K L hABC M N hM hN hK hL hKangle hLangle h2 h3 s t u v hs hs1 ht ht1 hu hu1 hv hv1 X Y hY hX hKu hLv hE

  obtain ⟨W, hWa, hWb⟩ :=
    statopia_math_node_81477081_e9900e38 A B C hABC
      (‖B - A‖ ^ 2 * (1 + t) / 4) (‖C - A‖ ^ 2 * (1 + s) / 4)
  obtain ⟨hKc, hLc⟩ :=
    statopia_math_node_302587009_faa16c35 A B C K L hABC M N hM hN hK hL hKangle hLangle
      h2 h3 s t u v hs hs1 ht ht1 hu hu1 hv hv1 X Y hY hX hKu hLv hE W hWa hWb
  refine ⟨A + W, ‖W‖ ^ 2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show A - (A + W) = -W by abel, norm_neg]
    ring_nf
  · exact hKc
  · exact hLc
  · have h4 : B - (A + W) = (B - A) - W := by abel
    have hc4 : dist A B ^ 2 = ‖B - A‖ ^ 2 := by rw [dist_eq_norm, norm_sub_rev]
    rw [h4, norm_sub_sq_real, hWa, hc4]
    ring_nf
  · have h5 : C - (A + W) = (C - A) - W := by abel
    have hc5 : dist A C ^ 2 = ‖C - A‖ ^ 2 := by rw [dist_eq_norm, norm_sub_rev]
    rw [h5, norm_sub_sq_real, hWb, hc5]
    ring_nf

  /- @proof-region region.target-node.session.dc6656d1d8deb057 end -/
