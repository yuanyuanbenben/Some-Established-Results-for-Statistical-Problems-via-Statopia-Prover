import ProverJobs.real_main_theorem_e7f39350f194.Vocabulary
import ProverJobs.real_main_theorem_e7f39350f194.Base
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_1160496100_1a4ca7a9_71914603
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_2572412618_fc84ca75_76d868b1
open EuclideanGeometry

open EuclideanGeometry

set_option autoImplicit false in
theorem statopia_math_node_3691240324_1176a2cb : ∀ (A B C K L : Plane)
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set Plane))
    (M N : Plane) (hM : M = midpoint ℝ A B) (hN : N = midpoint ℝ A C)
    (hK : InsideTriangle B M C K)
    (hL : InsideTriangle B N C L)
    (s t u v : ℝ)
    (hs : 0 < s) (hs1 : s < 1) (ht : 0 < t) (ht1 : t < 1)
    (hu : 0 < u) (hu1 : u < 1) (hv : 0 < v) (hv1 : v < 1)
    (Y X : Plane) (hY : Y = A + s • (C - A)) (hX : X = A + t • (B - A))
    (hKu : K = B + u • (Y - B)) (hLv : L = C + v • (X - C))
    (h1 : ∠ K B A = ∠ A C L),
    dist A B ^ 2 * t = dist A C ^ 2 * s := by
  /- @proof-region region.target-node.session.ea1fd0c22cbe42de begin -/
  intro A B C K L hABC M N hM hN hK hL s t u v hs hs1 ht ht1 hu hu1 hv hv1 Y X hY hX hKu hLv h1
  have hYvec : Y - A = s • (C - A) := by rw [hY]; abel
  have hXvec : X - A = t • (B - A) := by rw [hX]; abel
  have hAY : dist A Y = s * dist A C := by
    rw [dist_comm A Y, dist_comm A C, dist_eq_norm Y A, dist_eq_norm C A, hYvec, norm_smul,
      Real.norm_of_nonneg (le_of_lt hs)]
  have hAX : dist A X = t * dist A B := by
    rw [dist_comm A X, dist_comm A B, dist_eq_norm X A, dist_eq_norm B A, hXvec, norm_smul,
      Real.norm_of_nonneg (le_of_lt ht)]
  have hangle : ∠ A B Y = ∠ X C A := by
    have hA : ∠ K B A = ∠ A B Y := by
      rw [angle_comm A B Y, hKu]
      unfold EuclideanGeometry.angle
      simp only [vsub_eq_sub]
      have hvu : B + u • (Y - B) - B = u • (Y - B) := by abel
      rw [hvu]
      exact InnerProductGeometry.angle_smul_left_of_pos (Y - B) (A - B) hu
    have hC : ∠ A C L = ∠ X C A := by
      rw [angle_comm X C A, hLv]
      unfold EuclideanGeometry.angle
      simp only [vsub_eq_sub]
      have hwv : C + v • (X - C) - C = v • (X - C) := by abel
      rw [hwv]
      exact InnerProductGeometry.angle_smul_right_of_pos (A - C) (X - C) hv
    rw [hA, hC] at h1
    exact h1
  have hcore : dist A Y * dist A C = dist A B * dist A X :=
    statopia_math_node_1160496100_1a4ca7a9 A B C X Y s t hABC hs ht hY hX hangle
  rw [hAY, hAX] at hcore
  nlinarith [hcore]
  /- @proof-region region.target-node.session.ea1fd0c22cbe42de end -/
