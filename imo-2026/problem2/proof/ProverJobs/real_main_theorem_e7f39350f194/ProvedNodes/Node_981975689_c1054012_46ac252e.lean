import ProverJobs.real_main_theorem_e7f39350f194.Vocabulary
import ProverJobs.real_main_theorem_e7f39350f194.Base
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_3431605529_2a745110_37ebd9aa
open EuclideanGeometry

open EuclideanGeometry

set_option autoImplicit false in
theorem statopia_math_node_981975689_c1054012 : ∀ (A B C : Plane)
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set Plane)) (beta gamma : ℝ),
    ∃ (U : Plane) (r : ℝ),
      ‖A - U‖ ^ 2 - r = 0 ∧ ‖B - U‖ ^ 2 - r = beta ∧ ‖C - U‖ ^ 2 - r = gamma := by
  /- @proof-region region.target-node.session.d0e3ecbb7f595ebe begin -/
  intro A B C hABC beta gamma
  obtain ⟨hQlin, _, _, hQident, _, _, _, _⟩ :=
    statopia_math_node_3431605529_2a745110
  let L : (Plane × ℝ) →ₗ[ℝ] (ℝ × ℝ × ℝ) :=
    { toFun := fun p => (-2 * inner ℝ A p.1 - p.2,
                        -2 * inner ℝ B p.1 - p.2,
                        -2 * inner ℝ C p.1 - p.2)
      map_add' := by
        rintro ⟨x, a⟩ ⟨y, b⟩
        refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [inner_add_right] <;> ring
      map_smul' := by
        rintro c ⟨x, a⟩
        refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [inner_smul_right] <;> ring }
  have hfin2 : Module.finrank ℝ Plane = 2 := by
    rw [finrank_euclideanSpace]
    simp
  have L_apply : ∀ (x : Plane) (s : ℝ),
      L (x, s) = (-2 * inner ℝ A x - s, -2 * inner ℝ B x - s, -2 * inner ℝ C x - s) :=
    fun x s => rfl
  have hL_inj : Function.Injective L := by
    rintro ⟨U1, s1⟩ ⟨U2, s2⟩ h
    have hA : (‖A - U1‖ ^ 2 - (s1 + ‖U1‖ ^ 2)) - (‖A - U2‖ ^ 2 - (s2 + ‖U2‖ ^ 2)) = 0 := by
      have hc : -2 * inner ℝ A U1 - s1 = -2 * inner ℝ A U2 - s2 := by
        have h1 := congrArg (fun p : ℝ × ℝ × ℝ => p.1) h
        simpa only [L_apply] using h1
      rw [hQlin U1 (s1 + ‖U1‖ ^ 2) A, hQlin U2 (s2 + ‖U2‖ ^ 2) A]
      linarith
    have hB : (‖B - U1‖ ^ 2 - (s1 + ‖U1‖ ^ 2)) - (‖B - U2‖ ^ 2 - (s2 + ‖U2‖ ^ 2)) = 0 := by
      have hc : -2 * inner ℝ B U1 - s1 = -2 * inner ℝ B U2 - s2 := by
        have h1 := congrArg (fun p : ℝ × ℝ × ℝ => p.2.1) h
        simpa only [L_apply] using h1
      rw [hQlin U1 (s1 + ‖U1‖ ^ 2) B, hQlin U2 (s2 + ‖U2‖ ^ 2) B]
      linarith
    have hC : (‖C - U1‖ ^ 2 - (s1 + ‖U1‖ ^ 2)) - (‖C - U2‖ ^ 2 - (s2 + ‖U2‖ ^ 2)) = 0 := by
      have hc : -2 * inner ℝ C U1 - s1 = -2 * inner ℝ C U2 - s2 := by
        have h1 := congrArg (fun p : ℝ × ℝ × ℝ => p.2.2) h
        simpa only [L_apply] using h1
      rw [hQlin U1 (s1 + ‖U1‖ ^ 2) C, hQlin U2 (s2 + ‖U2‖ ^ 2) C]
      linarith
    have hW := hQident U1 (s1 + ‖U1‖ ^ 2) U2 (s2 + ‖U2‖ ^ 2) A B C hABC hA hB hC
    have hs : s1 = s2 := by
      have h0 := hW 0
      rw [hQlin U1 (s1 + ‖U1‖ ^ 2) 0, hQlin U2 (s2 + ‖U2‖ ^ 2) 0] at h0
      simp at h0
      linarith
    have hU : U1 = U2 := by
      have hP : ∀ P : Plane, inner ℝ P U1 = inner ℝ P U2 := by
        intro P
        have hPv := hW P
        rw [hQlin U1 (s1 + ‖U1‖ ^ 2) P, hQlin U2 (s2 + ‖U2‖ ^ 2) P] at hPv
        rw [hs] at hPv
        linarith
      have hself : inner ℝ (U1 - U2) (U1 - U2) = 0 := by
        rw [inner_sub_right, hP (U1 - U2), sub_self]
      have hnorm : ‖U1 - U2‖ = 0 := by
        have h2 : ‖U1 - U2‖ ^ 2 = 0 := by
          rw [← real_inner_self_eq_norm_sq]
          exact hself
        nlinarith [norm_nonneg (U1 - U2)]
      exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
    exact Prod.ext hU hs
  have hfin : Module.finrank ℝ (Plane × ℝ) = Module.finrank ℝ (ℝ × ℝ × ℝ) := by
    simp only [Module.finrank_prod, Module.finrank_self, hfin2] <;> norm_num
  have hL_surj : Function.Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hL_inj
  obtain ⟨⟨U, s⟩, hUs⟩ := hL_surj ((-‖A‖ ^ 2, beta - ‖B‖ ^ 2, gamma - ‖C‖ ^ 2) : ℝ × ℝ × ℝ)
  refine ⟨U, s + ‖U‖ ^ 2, ?_, ?_, ?_⟩
  · have hc : -2 * inner ℝ A U - s = -‖A‖ ^ 2 := by
      have h1 := congrArg (fun p : ℝ × ℝ × ℝ => p.1) hUs
      simpa only [L_apply] using h1
    rw [hQlin U (s + ‖U‖ ^ 2) A]
    linarith
  · have hc : -2 * inner ℝ B U - s = beta - ‖B‖ ^ 2 := by
      have h1 := congrArg (fun p : ℝ × ℝ × ℝ => p.2.1) hUs
      simpa only [L_apply] using h1
    rw [hQlin U (s + ‖U‖ ^ 2) B]
    linarith
  · have hc : -2 * inner ℝ C U - s = gamma - ‖C‖ ^ 2 := by
      have h1 := congrArg (fun p : ℝ × ℝ × ℝ => p.2.2) hUs
      simpa only [L_apply] using h1
    rw [hQlin U (s + ‖U‖ ^ 2) C]
    linarith
  /- @proof-region region.target-node.session.d0e3ecbb7f595ebe end -/
