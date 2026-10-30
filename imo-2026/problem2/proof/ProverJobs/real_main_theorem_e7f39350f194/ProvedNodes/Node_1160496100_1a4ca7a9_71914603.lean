import ProverJobs.real_main_theorem_e7f39350f194.Vocabulary
import ProverJobs.real_main_theorem_e7f39350f194.Base
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_3469497786_231dbb85_34eaf8d3
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_796628655_a7612b6d_7efadca1
open EuclideanGeometry

open EuclideanGeometry

set_option autoImplicit false in
theorem statopia_math_node_1160496100_1a4ca7a9 : ∀ (A B C X Y : Plane) (s t : ℝ)
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set Plane))
    (hs : 0 < s) (ht : 0 < t)
    (hY : Y = A + s • (C - A))
    (hX : X = A + t • (B - A))
    (hangle : ∠ A B Y = ∠ X C A),
    dist A Y * dist A C = dist A B * dist A X := by
  /- @proof-region region.target-node.session.6271619e40060e9e begin -/
  intro A B C X Y s t hABC hs ht hY hX hangle
  have hXA : X - A = t • (B - A) := by rw [hX]; abel
  have hYA : Y - A = s • (C - A) := by rw [hY]; abel
  have hdX : dist A X = t * dist A B := by
    calc dist A X = dist X A := dist_comm A X
      _ = ‖X - A‖ := dist_eq_norm X A
      _ = ‖t • (B - A)‖ := by rw [hXA]
      _ = ‖t‖ * ‖B - A‖ := norm_smul t (B - A)
      _ = t * dist A B := by
            rw [Real.norm_eq_abs, abs_of_pos ht, dist_eq_norm A B, norm_sub_rev]
  have hdY : dist A Y = s * dist A C := by
    calc dist A Y = dist Y A := dist_comm A Y
      _ = ‖Y - A‖ := dist_eq_norm Y A
      _ = ‖s • (C - A)‖ := by rw [hYA]
      _ = ‖s‖ * ‖C - A‖ := norm_smul s (C - A)
      _ = s * dist A C := by
            rw [Real.norm_eq_abs, abs_of_pos hs, dist_eq_norm A C, norm_sub_rev]
  unfold EuclideanGeometry.angle at hangle
  unfold InnerProductGeometry.angle at hangle
  have hvsub : ∀ u v : Plane, u -ᵥ v = u - v := fun u v => by simp
  have hcos : Real.cos (Real.arccos (inner ℝ (A -ᵥ B) (Y -ᵥ B) / (‖A -ᵥ B‖ * ‖Y -ᵥ B‖)))
      = Real.cos (Real.arccos (inner ℝ (X -ᵥ C) (A -ᵥ C) / (‖X -ᵥ C‖ * ‖A -ᵥ C‖))) :=
    congrArg Real.cos hangle
  have hbound : ∀ u v : Plane, |inner ℝ u v / (‖u‖ * ‖v‖)| ≤ 1 := by
    intro u v
    have hmain : |inner ℝ u v| ≤ ‖u‖ * ‖v‖ := by
      simpa using norm_inner_le_norm (𝕜 := ℝ) (E := Plane) u v
    have hden : (0 : ℝ) ≤ ‖u‖ * ‖v‖ := by positivity
    rcases eq_or_lt_of_le hden with h0 | hpos
    · have hi0 : inner ℝ u v = 0 := by
        refine abs_eq_zero.mp (le_antisymm ?_ (abs_nonneg _))
        rw [← h0] at hmain
        exact hmain
      rw [hi0, zero_div, abs_zero]
      norm_num
    · rw [abs_div, abs_of_nonneg hden, div_eq_mul_inv]
      have h1 : |inner ℝ u v| * (‖u‖ * ‖v‖)⁻¹ ≤ (‖u‖ * ‖v‖) * (‖u‖ * ‖v‖)⁻¹ :=
        mul_le_mul_of_nonneg_right hmain (by positivity)
      rwa [mul_inv_cancel₀ (ne_of_gt hpos)] at h1
  have hT : inner ℝ (A - B) (Y - B) / (‖A - B‖ * ‖Y - B‖)
      = inner ℝ (X - C) (A - C) / (‖X - C‖ * ‖A - C‖) := by
    have h1 : Real.cos (Real.arccos (inner ℝ (A - B) (Y - B) / (‖A - B‖ * ‖Y - B‖)))
        = Real.cos (Real.arccos (inner ℝ (X - C) (A - C) / (‖X - C‖ * ‖A - C‖))) := by
      simpa only [hvsub] using hcos
    rw [Real.cos_arccos (abs_le.mp (hbound (A - B) (Y - B))).1 (abs_le.mp (hbound (A - B) (Y - B))).2,
        Real.cos_arccos (abs_le.mp (hbound (X - C) (A - C))).1 (abs_le.mp (hbound (X - C) (A - C))).2] at h1
    exact h1
  obtain ⟨U, hU⟩ : ∃ U : Plane, U = B - A := ⟨B - A, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V : Plane, V = C - A := ⟨C - A, rfl⟩
  have hYB : Y - B = s • V - U := by rw [hY, hU, hV]; abel
  have hXC : X - C = t • U - V := by rw [hX, hU, hV]; abel
  have hAB : A - B = -U := by rw [hU]; abel
  have hAC : A - C = -V := by rw [hV]; abel
  have hT2 : inner ℝ (-U) (s • V - U) / (‖-U‖ * ‖s • V - U‖)
      = inner ℝ (t • U - V) (-V) / (‖t • U - V‖ * ‖-V‖) := by
    rw [hAB, hYB, hXC, hAC] at hT
    exact hT
  have hAng : Real.arccos (inner ℝ (-(B - A)) (s • (C - A) - (B - A)) / (‖-(B - A)‖ * ‖s • (C - A) - (B - A)‖))
      = Real.arccos (inner ℝ (t • (B - A) - (C - A)) (-(C - A)) / (‖t • (B - A) - (C - A)‖ * ‖-(C - A)‖)) := by
    rw [hU, hV] at hT2
    exact congrArg Real.arccos hT2
  have hG : ‖B - A‖ ^ 2 * ‖C - A‖ ^ 2 - (inner ℝ (B - A) (C - A)) ^ 2 ≠ 0 :=
    statopia_math_node_3469497786_231dbb85 A B C hABC
  have hkey : s * ‖C - A‖ ^ 2 = t * ‖B - A‖ ^ 2 :=
    statopia_math_node_796628655_a7612b6d (B - A) (C - A) s t hs ht hG hAng
  have hdAC : dist A C = ‖C - A‖ := by rw [dist_comm, dist_eq_norm]
  have hdAB : dist A B = ‖B - A‖ := by rw [dist_comm, dist_eq_norm]
  rw [hdY, hdX, hdAC, hdAB]
  nlinarith [hkey]
  /- @proof-region region.target-node.session.6271619e40060e9e end -/
