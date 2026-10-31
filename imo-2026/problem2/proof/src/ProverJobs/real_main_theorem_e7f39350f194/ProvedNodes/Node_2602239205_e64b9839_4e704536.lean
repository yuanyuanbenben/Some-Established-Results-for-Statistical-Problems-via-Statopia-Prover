import ProverJobs.real_main_theorem_e7f39350f194.Vocabulary
import ProverJobs.real_main_theorem_e7f39350f194.Base

open EuclideanGeometry

open EuclideanGeometry

set_option autoImplicit false in
theorem statopia_math_node_2602239205_e64b9839 : ∀ (A B C O : Plane)
    (M N : Plane) (hM : M = midpoint ℝ A B) (hN : N = midpoint ℝ A C),
    (dist O M) ^ 2 - (dist O N) ^ 2
      = ((dist O B) ^ 2 - (dist O A) ^ 2 - ((dist O C) ^ 2 - (dist O A) ^ 2)) / 2
        - ((dist A B) ^ 2 - (dist A C) ^ 2) / 4 := by
  /- @proof-region region.target-node.session.32ed6798f36f90a4 begin -/
  intro A B C O M N hM hN
  subst hM
  subst hN
  have p1 : ∀ (x y : Plane), ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * inner ℝ x y + ‖y‖ ^ 2 := by
    intro x y
    rw [norm_sub_sq_real]
  have p4 : ∀ (x : Plane) (r : ℝ), ‖r • x‖ ^ 2 = r ^ 2 * ‖x‖ ^ 2 := by
    intro x r
    simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] <;> ring
  have p5 : ∀ (x y : Plane), (dist x y) ^ 2 = ‖x - y‖ ^ 2 := by
    intro x y
    rw [dist_eq_norm]
  have p6 : ∀ (x y : Plane), midpoint ℝ x y = (2 : ℝ)⁻¹ • (x + y) := by
    intro x y
    rw [midpoint, AffineMap.lineMap_apply]
    simp only [invOf_eq_inv]
    change (2 : ℝ)⁻¹ • (y - x) + x = (2 : ℝ)⁻¹ • (x + y)
    rw [smul_add, smul_sub]
    set u : Plane := (2 : ℝ)⁻¹ • x with hu
    have hx : x = u + u := by
      rw [hu, ← add_smul, show (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ = 1 by norm_num, one_smul]
    rw [hx]
    abel
  have hMed : ∀ (p q : Plane), (dist O (midpoint ℝ p q)) ^ 2
      = ((dist O p) ^ 2 + (dist O q) ^ 2) / 2 - (dist p q) ^ 2 / 4 := by
    intro p q
    have hOs : O - midpoint ℝ p q = (2 : ℝ)⁻¹ • ((O - p) + (O - q)) := by
      rw [p6 p q]
      simp only [smul_add, smul_sub]
      set u : Plane := (2 : ℝ)⁻¹ • O with hu
      have hO : O = u + u := by
        rw [hu, ← add_smul, show (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ = 1 by norm_num, one_smul]
      rw [hO]
      abel
    have h1 : ‖O - midpoint ℝ p q‖ ^ 2 = (1 / 4 : ℝ) * ‖(O - p) + (O - q)‖ ^ 2 := by
      rw [hOs, p4]
      norm_num
    have h2 : ‖(O - p) + (O - q)‖ ^ 2
        = ‖O - p‖ ^ 2 + 2 * inner ℝ (O - p) (O - q) + ‖O - q‖ ^ 2 :=
      norm_add_sq_real _ _
    have h3 : ‖(O - p) - (O - q)‖ ^ 2
        = ‖O - p‖ ^ 2 - 2 * inner ℝ (O - p) (O - q) + ‖O - q‖ ^ 2 :=
      p1 _ _
    have h4 : ‖(O - p) - (O - q)‖ ^ 2 = ‖p - q‖ ^ 2 := by
      have hs : (O - p) - (O - q) = q - p := by abel
      rw [hs, ← p5 q p, dist_comm q p, p5 p q]
    rw [p5 O (midpoint ℝ p q), p5 O p, p5 O q, p5 p q]
    nlinarith [h1, h2, h3, h4]
  rw [hMed A B, hMed A C]
  ring
  /- @proof-region region.target-node.session.32ed6798f36f90a4 end -/
