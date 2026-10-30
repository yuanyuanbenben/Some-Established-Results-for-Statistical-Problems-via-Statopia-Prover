import Statlib.HighDim.Vocabulary.Norms
import ProverJobs.real_main_theorem_e7f39350f194.Vocabulary
import ProverJobs.real_main_theorem_e7f39350f194.Base
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_3431605529_2a745110_37ebd9aa
open EuclideanGeometry

open EuclideanGeometry

set_option autoImplicit false in
theorem statopia_math_node_2737272013_69da5b5b : ∀ (A B C : EuclideanSpace ℝ (Fin 2))
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2)))),
    LinearIndependent ℝ ![B - A, C - A] := by
  /- @proof-region region.target-node.session.4dc746b60e946553 begin -/
  intro A B C hABC
  refine Fintype.linearIndependent_iff.mpr ?_
  intro g hg
  have hkey : g 0 • (B - A) + g 1 • (C - A) = 0 := by
    simpa [Fin.sum_univ_two] using hg
  have hneg : ¬ (g 0 ≠ 0 ∨ g 1 ≠ 0) := by
    intro hcon
    obtain ⟨w, hwne, hbw, hcw⟩ : ∃ w : Plane, w ≠ 0 ∧ inner ℝ (B - A) w = 0 ∧ inner ℝ (C - A) w = 0 := by
      have hofLp : ∀ f : Fin 2 → ℝ, (Statlib.HighDim.Vocabulary.toEuclidean f).ofLp = f := by
        intro f
        simp only [Statlib.HighDim.Vocabulary.toEuclidean]
        simp
      have he2 : inner ℝ (Statlib.HighDim.Vocabulary.toEuclidean ![(1:ℝ), (0:ℝ)])
          (Statlib.HighDim.Vocabulary.toEuclidean ![(1:ℝ), (0:ℝ)]) = 1 := by
        rw [Statlib.HighDim.Vocabulary.inner_eq_sum, Fin.sum_univ_two, hofLp]
        simp
      have hone : Statlib.HighDim.Vocabulary.toEuclidean ![(1:ℝ), (0:ℝ)] ≠ 0 := by
        intro h
        rw [h] at he2
        simpa using he2
      have hrot_orth : ∀ v : Plane,
          inner ℝ v (Statlib.HighDim.Vocabulary.toEuclidean ![(v.ofLp 1), -((v.ofLp 0))]) = 0 := by
        intro v
        rw [Statlib.HighDim.Vocabulary.inner_eq_sum, Fin.sum_univ_two, hofLp]
        simp
        ring
      have hrot_ne : ∀ v : Plane, v ≠ 0 →
          Statlib.HighDim.Vocabulary.toEuclidean ![(v.ofLp 1), -((v.ofLp 0))] ≠ 0 := by
        intro v hv h
        have hs : inner ℝ (Statlib.HighDim.Vocabulary.toEuclidean ![(v.ofLp 1), -((v.ofLp 0))])
            (Statlib.HighDim.Vocabulary.toEuclidean ![(v.ofLp 1), -((v.ofLp 0))]) = inner ℝ v v := by
          rw [Statlib.HighDim.Vocabulary.inner_eq_sum, Statlib.HighDim.Vocabulary.inner_eq_sum,
            Fin.sum_univ_two, Fin.sum_univ_two, hofLp]
          simp
          ring
        have hv0 : inner ℝ v v = 0 := by rw [← hs, h]; simp
        exact hv (inner_self_eq_zero.mp hv0)
      by_cases hc : C - A = 0
      · by_cases hb : B - A = 0
        · exact ⟨Statlib.HighDim.Vocabulary.toEuclidean ![(1:ℝ), (0:ℝ)], hone, by simp [hb], by simp [hc]⟩
        · exact ⟨Statlib.HighDim.Vocabulary.toEuclidean ![(B - A).ofLp 1, -((B - A).ofLp 0)],
            hrot_ne (B - A) hb, hrot_orth (B - A), by simp [hc]⟩
      · have hg0 : g 0 ≠ 0 := by
          intro hg0
          have h1 : g 1 • (C - A) = 0 := by
            have hh := hkey
            rw [hg0, zero_smul, zero_add] at hh
            exact hh
          have hg1 : g 1 = 0 := (smul_eq_zero.mp h1).resolve_right hc
          rcases hcon with h | h
          · exact h hg0
          · exact h hg1
        have h2 : g 0 • (B - A) = -(g 1 • (C - A)) := by
          rw [eq_neg_iff_add_eq_zero]
          exact hkey
        have hb_eq : B - A = ((g 0)⁻¹ * (-(g 1))) • (C - A) := by
          calc B - A = (g 0)⁻¹ • (g 0 • (B - A)) := by
                rw [smul_smul, inv_mul_cancel₀ hg0, one_smul]
            _ = (g 0)⁻¹ • (-(g 1 • (C - A))) := by rw [h2]
            _ = ((g 0)⁻¹ * (-(g 1))) • (C - A) := by rw [← neg_smul, smul_smul]
        refine ⟨Statlib.HighDim.Vocabulary.toEuclidean ![(C - A).ofLp 1, -((C - A).ofLp 0)],
          hrot_ne (C - A) hc, ?_, hrot_orth (C - A)⟩
        rw [hb_eq, inner_smul_left, hrot_orth (C - A)]
        ring
    have hcol : Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))) := by
      have hE := statopia_math_node_3431605529_2a745110
      let U2 : Plane := A + w
      let r2 : ℝ := ‖U2‖ ^ 2 - ‖A‖ ^ 2 - 2 * inner ℝ A w
      have hid : ∀ P : Plane, (‖P - A‖ ^ 2 - 0) - (‖P - U2‖ ^ 2 - r2) = 2 * inner ℝ (P - A) w := by
        intro P
        rw [hE.1 A 0 P, hE.1 U2 r2 P]
        dsimp only [U2, r2]
        simp only [inner_add_right, inner_sub_left]
        ring
      have hA : (‖A - A‖ ^ 2 - 0) - (‖A - U2‖ ^ 2 - r2) = 0 := by
        rw [hid A]; simp
      have hB : (‖B - A‖ ^ 2 - 0) - (‖B - U2‖ ^ 2 - r2) = 0 := by
        rw [hid B, hbw]; ring
      have hC : (‖C - A‖ ^ 2 - 0) - (‖C - U2‖ ^ 2 - r2) = 0 := by
        rw [hid C, hcw]; ring
      have h0 := hE.2.2.2.1 A 0 U2 r2 A B C hABC hA hB hC
      have h1 := h0 (A + w)
      rw [hid (A + w)] at h1
      have hww : 2 * inner ℝ w w = 0 := by simpa using h1
      have hww' : inner ℝ w w = 0 := by linarith [hww]
      exact False.elim (hwne (inner_self_eq_zero.mp hww'))
    exact hABC hcol
  have h0 : g 0 = 0 := by
    by_contra h
    exact hneg (Or.inl h)
  have h1 : g 1 = 0 := by
    by_contra h
    exact hneg (Or.inr h)
  intro i
  fin_cases i <;> assumption
  /- @proof-region region.target-node.session.4dc746b60e946553 end -/
