import ProverJobs.real_main_theorem_e7f39350f194.Vocabulary
import ProverJobs.real_main_theorem_e7f39350f194.Base

open EuclideanGeometry

open EuclideanGeometry

set_option autoImplicit false in
theorem statopia_math_node_3469497786_231dbb85 : ∀ (A B C : Plane)
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set Plane)),
    ‖B - A‖ ^ 2 * ‖C - A‖ ^ 2 - (inner ℝ (B - A) (C - A)) ^ 2 ≠ 0 := by
  /- @proof-region region.target-node.session.28b33437e29062e8 begin -/
  intro A B C hABC
  have h1 : ¬ (Module.rank ℝ ↥(vectorSpan ℝ ({A, B, C} : Set Plane)) ≤ 1) := hABC
  intro hG
  have hpairAB : Collinear ℝ ({A, B} : Set Plane) := collinear_pair ℝ A B
  have hpairAC : Collinear ℝ ({A, C} : Set Plane) := collinear_pair ℝ A C
  by_cases hU : B - A = 0
  · have hBA : B = A := sub_eq_zero.mp hU
    have hset : ({A, B, C} : Set Plane) = {A, C} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro (h | h | h)
        · exact Or.inl h
        · exact Or.inl (h.trans hBA)
        · exact Or.inr h
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
    rw [hset] at hABC
    exact hABC hpairAC
  · obtain ⟨r, hr⟩ : ∃ r : ℝ, C - A = r • (B - A) := by
      refine ⟨inner ℝ (B - A) (C - A) / ‖B - A‖ ^ 2, ?_⟩
      have hc : ‖B - A‖ ^ 2 ≠ 0 := by positivity
      have hA : inner ℝ (C - A) ((inner ℝ (B - A) (C - A) / ‖B - A‖ ^ 2) • (B - A))
          = (inner ℝ (B - A) (C - A) / ‖B - A‖ ^ 2) * inner ℝ (B - A) (C - A) := by
        rw [inner_smul_right, real_inner_comm]
      have hB : ‖(inner ℝ (B - A) (C - A) / ‖B - A‖ ^ 2) • (B - A)‖ ^ 2
          = (inner ℝ (B - A) (C - A) / ‖B - A‖ ^ 2) ^ 2 * ‖B - A‖ ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      have hsq : ‖(C - A) - (inner ℝ (B - A) (C - A) / ‖B - A‖ ^ 2) • (B - A)‖ ^ 2 = 0 := by
        rw [norm_sub_sq_real, hA, hB]
        field_simp
        nlinarith [hG]
      have hmul : ‖(C - A) - (inner ℝ (B - A) (C - A) / ‖B - A‖ ^ 2) • (B - A)‖
          * ‖(C - A) - (inner ℝ (B - A) (C - A) / ‖B - A‖ ^ 2) • (B - A)‖ = 0 := by
        rw [← pow_two]
        exact hsq
      have hnorm : ‖(C - A) - (inner ℝ (B - A) (C - A) / ‖B - A‖ ^ 2) • (B - A)‖ = 0 :=
        (mul_eq_zero.mp hmul).elim id id
      exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
    have hgen : ∀ (s : Set Plane) (p : Plane), p ∈ s →
        vectorSpan ℝ s = Submodule.span ℝ ((fun x => p -ᵥ x) '' s) :=
      fun s p hp => vectorSpan_eq_span_vsub_set_left ℝ hp
    have hle : vectorSpan ℝ ({A, B, C} : Set Plane) ≤ vectorSpan ℝ ({A, B} : Set Plane) := by
      rw [hgen ({A, B, C} : Set Plane) A (by simp), hgen ({A, B} : Set Plane) A (by simp)]
      apply Submodule.span_le.mpr
      rintro y ⟨x, hx, hxy⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rw [← hxy]
      rcases hx with h | h | h
      · rw [h]
        exact Submodule.subset_span (show A -ᵥ A ∈ (fun x => A -ᵥ x) '' ({A, B} : Set Plane) from
          ⟨A, by simp, rfl⟩)
      · rw [h]
        exact Submodule.subset_span (show A -ᵥ B ∈ (fun x => A -ᵥ x) '' ({A, B} : Set Plane) from
          ⟨B, by simp, rfl⟩)
      · rw [h]
        have hAC : A -ᵥ C = r • (A -ᵥ B) := by
          have e1 : A -ᵥ C = -(C - A) := by simp
          have e2 : A -ᵥ B = -(B - A) := by simp
          rw [e1, e2, smul_neg, ← hr]
        change A -ᵥ C ∈ Submodule.span ℝ ((fun x => A -ᵥ x) '' ({A, B} : Set Plane))
        rw [hAC]
        apply Submodule.smul_mem
        exact Submodule.subset_span (show A -ᵥ B ∈ (fun x => A -ᵥ x) '' ({A, B} : Set Plane) from
          ⟨B, by simp, rfl⟩)
    have hge : vectorSpan ℝ ({A, B} : Set Plane) ≤ vectorSpan ℝ ({A, B, C} : Set Plane) := by
      rw [hgen ({A, B} : Set Plane) A (by simp), hgen ({A, B, C} : Set Plane) A (by simp)]
      apply Submodule.span_le.mpr
      rintro y ⟨x, hx, hxy⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rw [← hxy]
      rcases hx with h | h
      · rw [h]
        exact Submodule.subset_span (show A -ᵥ A ∈ (fun x => A -ᵥ x) '' ({A, B, C} : Set Plane) from
          ⟨A, by simp, rfl⟩)
      · rw [h]
        exact Submodule.subset_span (show A -ᵥ B ∈ (fun x => A -ᵥ x) '' ({A, B, C} : Set Plane) from
          ⟨B, by simp, rfl⟩)
    have heq : vectorSpan ℝ ({A, B, C} : Set Plane) = vectorSpan ℝ ({A, B} : Set Plane) :=
      le_antisymm hle hge
    rw [heq] at h1
    exact h1 hpairAB
  /- @proof-region region.target-node.session.28b33437e29062e8 end -/
