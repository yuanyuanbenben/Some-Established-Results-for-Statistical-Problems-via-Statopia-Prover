import ProverJobs.real_main_theorem_e7f39350f194.Vocabulary
import ProverJobs.real_main_theorem_e7f39350f194.Base
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_4100268325_31a302d7_f6a0c703
open EuclideanGeometry

open EuclideanGeometry

set_option autoImplicit false in
theorem statopia_math_node_3431605529_2a745110 : (∀ (U : Plane) (r2 : ℝ) (P : Plane),
      ‖P - U‖ ^ 2 - r2 = ‖P‖ ^ 2 - 2 * inner ℝ P U + (‖U‖ ^ 2 - r2))
    ∧
    
    (∀ (U1 : Plane) (r1 : ℝ) (U2 : Plane) (r2 : ℝ) (P P' : Plane) (a : ℝ),
      (‖((1 - a) • P + a • P') - U1‖ ^ 2 - r1)
          - (‖((1 - a) • P + a • P') - U2‖ ^ 2 - r2)
        = (1 - a) * ((‖P - U1‖ ^ 2 - r1) - (‖P - U2‖ ^ 2 - r2))
          + a * ((‖P' - U1‖ ^ 2 - r1) - (‖P' - U2‖ ^ 2 - r2)))
    ∧
    
    (∀ (U1 : Plane) (r1 : ℝ) (U2 : Plane) (r2 : ℝ) (P P' : Plane),
      P ≠ P' →
      (‖P - U1‖ ^ 2 - r1) - (‖P - U2‖ ^ 2 - r2) = 0 →
      (‖P' - U1‖ ^ 2 - r1) - (‖P' - U2‖ ^ 2 - r2) = 0 →
      ∀ a : ℝ,
        (‖((1 - a) • P + a • P') - U1‖ ^ 2 - r1)
          - (‖((1 - a) • P + a • P') - U2‖ ^ 2 - r2) = 0)
    ∧
    
    (∀ (U1 : Plane) (r1 : ℝ) (U2 : Plane) (r2 : ℝ) (A B C : Plane),
      ¬ Collinear ℝ ({A, B, C} : Set Plane) →
      (‖A - U1‖ ^ 2 - r1) - (‖A - U2‖ ^ 2 - r2) = 0 →
      (‖B - U1‖ ^ 2 - r1) - (‖B - U2‖ ^ 2 - r2) = 0 →
      (‖C - U1‖ ^ 2 - r1) - (‖C - U2‖ ^ 2 - r2) = 0 →
      ∀ W : Plane, (‖W - U1‖ ^ 2 - r1) - (‖W - U2‖ ^ 2 - r2) = 0)
    ∧
    
    (∀ (U : Plane) (r2 : ℝ) (P0 v : Plane) (z : ℝ),
      ‖(P0 + z • v) - U‖ ^ 2 - r2
        = ‖v‖ ^ 2 * z ^ 2 + 2 * z * inner ℝ v (P0 - U) + (‖P0 - U‖ ^ 2 - r2))
    ∧
    
    (∀ (U : Plane) (r2 : ℝ) (P0 v : Plane) (u1 u2 : ℝ),
      v ≠ 0 →
      (‖(P0 + u1 • v) - U‖ ^ 2 - r2 = 0) →
      (‖(P0 + u2 • v) - U‖ ^ 2 - r2 = 0) →
      (u1 = u2 → 2 * (‖v‖ ^ 2 * u1 + inner ℝ v (P0 - U)) = 0) →
      ∀ z : ℝ, ‖(P0 + z • v) - U‖ ^ 2 - r2 = ‖v‖ ^ 2 * (z - u1) * (z - u2))
    ∧
    
    (∀ (U : Plane) (r2 : ℝ) (P0 v : Plane) (u1 u2 : ℝ),
      v ≠ 0 → u1 ≠ u2 →
      (‖(P0 + u1 • v) - U‖ ^ 2 - r2 = 0) →
      (‖(P0 + u2 • v) - U‖ ^ 2 - r2 = 0) →
      ∀ z : ℝ, ‖(P0 + z • v) - U‖ ^ 2 - r2 = ‖v‖ ^ 2 * (z - u1) * (z - u2))
    ∧
    
    (∀ (U : Plane) (r2 : ℝ) (P0 v : Plane) (u0 : ℝ),
      v ≠ 0 →
      (‖(P0 + u0 • v) - U‖ ^ 2 - r2 = 0) →
      inner ℝ v (P0 + u0 • v - U) = 0 →
      ∀ z : ℝ, ‖(P0 + z • v) - U‖ ^ 2 - r2 = ‖v‖ ^ 2 * (z - u0) ^ 2) := by
  /- @proof-region region.target-node.session.25370982a00d698e begin -/
  have affine_zeros : ∀ (R : Plane → ℝ),
      (∀ (P P' : Plane) (a : ℝ), R ((1 - a) • P + a • P') = (1 - a) * R P + a * R P') →
      ∀ (A B C : Plane), ¬ Collinear ℝ ({A, B, C} : Set Plane) →
      R A = 0 → R B = 0 → R C = 0 → ∀ W : Plane, R W = 0 := by
    intro R haff A B C hcol hA hB hC W
    have hscale : ∀ (c : ℝ) (z : Plane), R (A + c • z) = c * R (A + z) := by
      intro c z
      have h := haff A (A + z) c
      have harg : (1 - c) • A + c • (A + z) = A + c • z := by
        have hc : (1 : ℝ) - c + c = 1 := by ring
        rw [smul_add, ← add_assoc, ← add_smul, hc, one_smul]
      rw [harg, hA] at h
      simpa using h
    have hAA : (1 / 2 : ℝ) • A + (1 / 2 : ℝ) • A = A := by
      rw [← add_smul, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, one_smul]
    have hadd : ∀ (x y : Plane), R (A + (x + y)) = R (A + x) + R (A + y) := by
      intro x y
      have hmid2 := haff (A + x) (A + y) (1 / 2)
      have hmarg : (1 - (1 / 2 : ℝ)) • (A + x) + (1 / 2 : ℝ) • (A + y)
          = A + (1 / 2 : ℝ) • (x + y) := by
        rw [show (1 : ℝ) - (1 / 2 : ℝ) = 1 / 2 by norm_num]
        rw [← smul_add]
        rw [show (A + x) + (A + y) = (A + A) + (x + y) by abel]
        simp only [smul_add, hAA]
      rw [hmarg] at hmid2
      have h2 := hscale (1 / 2) (x + y)
      linarith
    obtain ⟨s, t, hW⟩ := statopia_math_node_4100268325_31a302d7 A B C W hcol
    have hWeq : W = A + (s • (B - A) + t • (C - A)) := by
      rw [← hW]
      abel
    have hBu : A + (B - A) = B := by abel
    have hCv : A + (C - A) = C := by abel
    rw [hWeq, hadd (s • (B - A)) (t • (C - A)), hscale s (B - A), hscale t (C - A),
      hBu, hCv, hB, hC]
    ring



  have expandsub : ∀ (U : Plane) (r2 : ℝ) (P : Plane),
      ‖P - U‖ ^ 2 - r2 = ‖P‖ ^ 2 - 2 * inner ℝ P U + (‖U‖ ^ 2 - r2) := by
    intro U r2 P
    rw [norm_sub_sq_real]
    ring
  have expand : ∀ (U : Plane) (r2 : ℝ) (P0 v : Plane) (z : ℝ),
      ‖(P0 + z • v) - U‖ ^ 2 - r2
        = ‖v‖ ^ 2 * z ^ 2 + 2 * z * inner ℝ v (P0 - U) + (‖P0 - U‖ ^ 2 - r2) := by
    intro U r2 P0 v z
    have h : P0 + z • v - U = (P0 - U) + z • v := by abel
    have hv : ‖z • v‖ ^ 2 = z ^ 2 * ‖v‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have hi : inner ℝ (P0 - U) (z • v) = z * inner ℝ v (P0 - U) := by
      rw [inner_smul_right, real_inner_comm (P0 - U) v]
    rw [h, norm_add_sq_real, hv, hi]
    ring
  have inner_affine : ∀ (X Y D : Plane) (c d : ℝ),
      inner ℝ (c • X + d • Y) D = c * inner ℝ X D + d * inner ℝ Y D := by
    intro X Y D c d
    rw [real_inner_comm D (c • X + d • Y)]
    simp only [inner_add_right, inner_smul_right]
    rw [real_inner_comm X D, real_inner_comm Y D]
  have affine : ∀ (U1 : Plane) (r1 : ℝ) (U2 : Plane) (r2 : ℝ) (P P' : Plane) (a : ℝ),
      (‖((1 - a) • P + a • P') - U1‖ ^ 2 - r1)
          - (‖((1 - a) • P + a • P') - U2‖ ^ 2 - r2)
        = (1 - a) * ((‖P - U1‖ ^ 2 - r1) - (‖P - U2‖ ^ 2 - r2))
          + a * ((‖P' - U1‖ ^ 2 - r1) - (‖P' - U2‖ ^ 2 - r2)) := by
    intro U1 r1 U2 r2 P P' a
    rw [expandsub U1 r1 ((1 - a) • P + a • P'), expandsub U2 r2 ((1 - a) • P + a • P'),
      expandsub U1 r1 P, expandsub U2 r2 P, expandsub U1 r1 P', expandsub U2 r2 P',
      inner_affine P P' U1 (1 - a) a, inner_affine P P' U2 (1 - a) a]
    ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact expandsub
  · exact affine
  · intro U1 r1 U2 r2 P P' hne hP hP' a
    have hb := affine U1 r1 U2 r2 P P' a
    rw [hP, hP'] at hb
    rw [hb]
    ring
  · intro U1 r1 U2 r2 A B C hcol hA hB hC W
    exact affine_zeros (fun P => (‖P - U1‖ ^ 2 - r1) - (‖P - U2‖ ^ 2 - r2))
      (fun P P' a => affine U1 r1 U2 r2 P P' a) A B C hcol hA hB hC W
  · exact expand
  · intro U r2 P0 v u1 u2 hv h1 h2 hdup z
    rw [expand U r2 P0 v u1] at h1
    rw [expand U r2 P0 v u2] at h2
    rw [expand U r2 P0 v z]
    have hkey : ‖v‖ ^ 2 * (u1 + u2) + 2 * inner ℝ v (P0 - U) = 0 := by
      rcases eq_or_ne u1 u2 with h | h
      · have hd := hdup h
        linear_combination hd - ‖v‖ ^ 2 * h
      · have hsub : (u1 - u2) * (‖v‖ ^ 2 * (u1 + u2) + 2 * inner ℝ v (P0 - U)) = 0 := by
          linear_combination h1 - h2
        rcases mul_eq_zero.mp hsub with h' | h'
        · exact absurd (sub_eq_zero.mp h') h
        · exact h'
    linear_combination h1 + (z - u1) * hkey
  · intro U r2 P0 v u1 u2 hv hne h1 h2 z
    rw [expand U r2 P0 v u1] at h1
    rw [expand U r2 P0 v u2] at h2
    rw [expand U r2 P0 v z]
    have hkey : ‖v‖ ^ 2 * (u1 + u2) + 2 * inner ℝ v (P0 - U) = 0 := by
      have hsub : (u1 - u2) * (‖v‖ ^ 2 * (u1 + u2) + 2 * inner ℝ v (P0 - U)) = 0 := by
        linear_combination h1 - h2
      rcases mul_eq_zero.mp hsub with h' | h'
      · exact absurd (sub_eq_zero.mp h') hne
      · exact h'
    linear_combination h1 + (z - u1) * hkey
  · intro U r2 P0 v u0 hv h1 htang z
    have hβ : inner ℝ v (P0 - U) = -(‖v‖ ^ 2) * u0 := by
      have hh : P0 + u0 • v - U = (P0 - U) + u0 • v := by abel
      have hsplit : inner ℝ v (P0 + u0 • v - U) = inner ℝ v (P0 - U) + u0 * ‖v‖ ^ 2 := by
        rw [hh, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq]
      rw [hsplit] at htang
      linarith
    rw [expand U r2 P0 v u0] at h1
    rw [expand U r2 P0 v z]
    linear_combination h1 + (2 * (z - u0)) * hβ
  /- @proof-region region.target-node.session.25370982a00d698e end -/
