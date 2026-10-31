import ProverJobs.real_main_theorem_e7f39350f194.Vocabulary
import ProverJobs.real_main_theorem_e7f39350f194.Base
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_1079600542_410cd104_a404688e
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_3431605529_2a745110_37ebd9aa
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_726603668_6c32cefd_9f4b3dd2
open EuclideanGeometry

open EuclideanGeometry

set_option autoImplicit false in
theorem statopia_math_node_1009185205_43daf791 : ∀ (A B C K L : Plane)
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set Plane))
    (M N : Plane) (hM : M = midpoint ℝ A B) (hN : N = midpoint ℝ A C)
    (hK : InsideTriangle B M C K) (hL : InsideTriangle B N C L)
    (hKangle : InsideAngle L B A K)
    (s t u v : ℝ)
    (hs : 0 < s) (hs1 : s < 1) (ht : 0 < t) (ht1 : t < 1)
    (hu : 0 < u) (hu1 : u < 1) (hv : 0 < v) (hv1 : v < 1)
    (Y X : Plane) (hY : Y = A + s • (C - A)) (hX : X = A + t • (B - A))
    (hLtrace : L = C + v • (X - C)) (hKtrace : K = B + u • (Y - B))
    (h2 : ∠ L B K = ∠ L N C)
    (U : Plane) (r2 : ℝ)
    (hBU : ‖B - U‖ ^ 2 - r2 = 0) (hLU : ‖L - U‖ ^ 2 - r2 = 0) (hNU : ‖N - U‖ ^ 2 - r2 = 0),
    (s = 1 / 2 → inner ℝ (C - A) (N - U) = 0) ∧
    (s ≠ 1 / 2 → (‖Y - U‖ ^ 2 - r2 = 0)) := by
  /- @proof-region region.target-node.session.1895e597590fc465 begin -/
  intro A B C K L hABC M N hM hN hK hL hKangle s t u v hs hs1 ht ht1 hu hu1 hv hv1 Y X hY hX hLtrace hKtrace h2 U r2 hBU hLU hNU
  have h2' : ∠ L B Y = ∠ L N C := by
    rw [← h2]
    have hk : K -ᵥ B = u • (Y -ᵥ B) := by
      change K - B = u • (Y - B)
      rw [hKtrace, add_sub_cancel_left]
    simp only [EuclideanGeometry.angle]
    rw [hk]
    exact (InnerProductGeometry.angle_smul_right_of_pos (L -ᵥ B) (Y -ᵥ B) hu).symm
  have hL' : L = C + v • ((A + t • (B - A)) - C) := by rw [hLtrace, hX]
  have hbranch : (1 - v) - (1 - v * t) * s > 0 :=
    statopia_math_node_726603668_6c32cefd A B C K L hABC M N hM hN hK hL hKangle s t u v hs hs1 ht ht1 hu hu1 hv hv1 Y X hY hX hKtrace hLtrace h2'
  have hE : 2 * inner ℝ (C - A) (N - U) + (s - 1 / 2) * ‖C - A‖ ^ 2 = 0 :=
    statopia_math_node_1079600542_410cd104 A B C L N Y U t v s r2 hN hY hL' hABC ht ht1 hv hv1 hs hs1 hL hBU hLU hNU h2' hbranch
  constructor
  · intro hs12
    have hz : s - 1 / 2 = 0 := by rw [hs12]; norm_num
    rw [hz, zero_mul, add_zero] at hE
    linarith
  · intro hsne
    have hYN : Y - N = (s - 1 / 2) • (C - A) := by
      rw [hY, hN, midpoint_eq_smul_add, invOf_eq_inv]
      module
    obtain ⟨_, _, _, _, hQe, _, _, _⟩ := statopia_math_node_3431605529_2a745110
    have hYN2 : N + (s - 1 / 2) • (C - A) = Y := by rw [← hYN]; abel
    have hid : ‖Y - U‖ ^ 2 - r2 = (s - 1 / 2) * (2 * inner ℝ (C - A) (N - U) + (s - 1 / 2) * ‖C - A‖ ^ 2) + (‖N - U‖ ^ 2 - r2) := by
      have h := hQe U r2 N (C - A) (s - 1 / 2)
      rw [hYN2] at h
      rw [h]
      ring
    rw [hid, hE, mul_zero, zero_add, hNU]
  /- @proof-region region.target-node.session.1895e597590fc465 end -/
