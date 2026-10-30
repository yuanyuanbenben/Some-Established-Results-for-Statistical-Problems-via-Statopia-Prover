import ProverJobs.real_main_theorem_e7f39350f194.Vocabulary
import ProverJobs.real_main_theorem_e7f39350f194.Base
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_2572412618_fc84ca75_76d868b1
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_3431605529_2a745110_37ebd9aa
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_4006387899_007deac2_aab74f68
open EuclideanGeometry

open EuclideanGeometry

set_option autoImplicit false in
theorem statopia_math_node_2237241960_78eabb87 : ∀ (A B C K L M N X Y : Plane) (s t u v : ℝ)
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set Plane))
    (hM : M = midpoint ℝ A B) (hN : N = midpoint ℝ A C)
    (hK : InsideTriangle B M C K) (hL : InsideTriangle B N C L)
    (hs : 0 < s) (hs1 : s < 1) (ht : 0 < t) (ht1 : t < 1)
    (hu : 0 < u) (hu1 : u < 1) (hv : 0 < v) (hv1 : v < 1)
    (hY : Y = A + s • (C - A)) (hX : X = A + t • (B - A))
    (hKtrace : K = B + u • (Y - B)) (hLtrace : L = C + v • (X - C))
    (h3 : ∠ L C K = ∠ B M K)
    (hbranch : t < 1 / 2 ∨ 0 < (1 - u) - t * (1 - u * s)),
    ∃ (U : Plane) (r2 : ℝ),
      (‖C - U‖ ^ 2 - r2 = 0) ∧ (‖K - U‖ ^ 2 - r2 = 0) ∧
      (∀ z : ℝ, ‖A + z • (B - A) - U‖ ^ 2 - r2 = dist A B ^ 2 * (z - 1 / 2) * (z - t)) := by
  /- @proof-region region.target-node.session.6299f0b60e016650 begin -/
  intro A B C K L M N X Y s t u v hABC hM hN hK hL hs hs1 ht ht1 hu hu1 hv hv1 hY hX hKtrace hLtrace h3 hbranch
  obtain ⟨U, r2, hC, hK', hM', hX', htan⟩ :=
    statopia_math_node_4006387899_007deac2 A B C K L hABC M N hM hN hK hL s t u v
      hs hs1 ht ht1 hu hu1 hv hv1 X Y hY hX hKtrace hLtrace h3 hbranch
  have c7 := (statopia_math_node_3431605529_2a745110).2.2.2.2.2.2.1
  have c8 := (statopia_math_node_3431605529_2a745110).2.2.2.2.2.2.2
  have h2 : (⅟2 : ℝ) = 1 / 2 := by
    first
      | norm_num
      | rfl
      | (rw [one_div]; rfl)
      | exact inv_eq_one_div (2 : ℝ)
      | (rw [one_div]; norm_num)
      | simp
  have hmid : A + (1 / 2 : ℝ) • (B - A) = M := by
    rw [hM]
    simp only [midpoint, AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub]
    rw [h2]
    abel
  have hroot1 : ‖(A + (1 / 2 : ℝ) • (B - A)) - U‖ ^ 2 - r2 = 0 := by
    rw [hmid]; exact hM'
  have hdist : dist A B = ‖B - A‖ := by rw [dist_comm A B, dist_eq_norm]
  refine ⟨U, r2, hC, hK', ?_⟩
  intro z
  by_cases hw0 : B - A = 0
  · have hL : A + z • (B - A) - U = A + (1 / 2 : ℝ) • (B - A) - U := by
      simp only [hw0, smul_zero, add_zero]
    have hR : dist A B ^ 2 * (z - 1 / 2) * (z - t) = 0 := by
      rw [hdist, hw0, norm_zero]
      ring
    rw [hL, hR]
    exact hroot1
  · have hBAnz : B - A ≠ 0 := hw0
    by_cases ht2 : t = 1 / 2
    · have htang : inner ℝ (B - A) (A + (1 / 2 : ℝ) • (B - A) - U) = 0 := by
        rw [hmid]; exact htan ht2
      have key := c8 U r2 A (B - A) (1 / 2) hBAnz hroot1 htang
      rw [hdist, key z, ht2]
      ring
    · have htne : (1 / 2 : ℝ) ≠ t := fun h => ht2 h.symm
      have hroot2 : ‖(A + t • (B - A)) - U‖ ^ 2 - r2 = 0 := by
        rw [← hX]; exact hX' ht2
      have key := c7 U r2 A (B - A) (1 / 2) t hBAnz htne hroot1 hroot2
      simpa [hdist] using key z
  /- @proof-region region.target-node.session.6299f0b60e016650 end -/
