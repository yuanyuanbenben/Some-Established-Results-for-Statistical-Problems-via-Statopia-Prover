import ProverJobs.real_main_theorem_e7f39350f194.Vocabulary
import ProverJobs.real_main_theorem_e7f39350f194.Base
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_3179275638_03586b8a_390e08f7
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_3431605529_2a745110_37ebd9aa
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_3516123686_7891845d_0c45db7d
open EuclideanGeometry

open EuclideanGeometry

set_option autoImplicit false in
theorem statopia_math_node_2640265524_f2e3bdd6 : ∀ (A B C K L O : Plane)
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set Plane))
    (M N : Plane) (hM : M = midpoint ℝ A B) (hN : N = midpoint ℝ A C)
    (hK : InsideTriangle B M C K)
    (hL : InsideTriangle B N C L)
    (hKangle : InsideAngle L B A K)
    (hO : IsCircumcentre A K L O)
    (s t : ℝ) (hs : 0 < s) (hs1 : s < 1) (ht : 0 < t) (ht1 : t < 1)
    (Q : Plane → ℝ) (W : Plane) (rho2 : ℝ)
    (hQ : ∀ P : Plane, Q P = ‖P - W‖ ^ 2 - rho2)
    (hQA : Q A = 0) (hQK : Q K = 0) (hQL : Q L = 0)
    (hQB : Q B = dist A B ^ 2 * (1 - t) / 2)
    (hQC : Q C = dist A C ^ 2 * (1 - s) / 2),
    (∀ P : Plane, dist O P ^ 2 - dist O A ^ 2 = Q P) ∧
      (dist O B ^ 2 - dist O A ^ 2 = dist A B ^ 2 * (1 - t) / 2) ∧
      (dist O C ^ 2 - dist O A ^ 2 = dist A C ^ 2 * (1 - s) / 2) := by
  /- @proof-region region.target-node.session.7a4b1f3ed1cfa812 begin -/
  intro A B C K L O hABC M N hM hN hK hL hKangle hO s t hs hs1 ht ht1 Q W rho2 hQ hQA hQK hQL hQB hQC
  obtain ⟨_, _, _, h3pts, _, _, _, _⟩ := statopia_math_node_3431605529_2a745110
  have hdist : ∀ P : Plane, dist O P ^ 2 = ‖P - O‖ ^ 2 := fun P => by
    rw [dist_comm, dist_eq_norm]
  have hNCL : ¬ Collinear ℝ ({A, K, L} : Set Plane) :=
    statopia_math_node_3516123686_7891845d A B C K L O hABC M N hM hN hK hL hKangle hO
  have hZA : (‖A - O‖ ^ 2 - dist O A ^ 2) - (‖A - W‖ ^ 2 - rho2) = 0 := by
    rw [← hdist A, ← hQ A, hQA]; ring
  have hZK : (‖K - O‖ ^ 2 - dist O A ^ 2) - (‖K - W‖ ^ 2 - rho2) = 0 := by
    have h1 : ‖K - O‖ ^ 2 = dist O A ^ 2 := by rw [← hdist K, ← hO.1]
    rw [h1, ← hQ K, hQK]; ring
  have hZL : (‖L - O‖ ^ 2 - dist O A ^ 2) - (‖L - W‖ ^ 2 - rho2) = 0 := by
    have h1 : ‖L - O‖ ^ 2 = dist O A ^ 2 := by rw [← hdist L, ← hO.2]
    rw [h1, ← hQ L, hQL]; ring
  have hR : ∀ P : Plane, (‖P - O‖ ^ 2 - dist O A ^ 2) - (‖P - W‖ ^ 2 - rho2) = 0 :=
    h3pts O (dist O A ^ 2) W rho2 A K L hNCL hZA hZK hZL
  refine ⟨?_, ?_, ?_⟩
  · intro P
    have h := hR P
    rw [← hdist P, ← hQ P] at h
    linarith
  · have h := hR B
    rw [← hdist B, ← hQ B] at h
    rw [hQB] at h
    linarith
  · have h := hR C
    rw [← hdist C, ← hQ C] at h
    rw [hQC] at h
    linarith
  /- @proof-region region.target-node.session.7a4b1f3ed1cfa812 end -/
