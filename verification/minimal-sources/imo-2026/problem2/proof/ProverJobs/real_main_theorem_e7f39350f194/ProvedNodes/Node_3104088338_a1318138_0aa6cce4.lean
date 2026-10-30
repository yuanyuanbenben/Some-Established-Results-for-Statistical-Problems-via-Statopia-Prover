import ProverJobs.real_main_theorem_e7f39350f194.Vocabulary
import ProverJobs.real_main_theorem_e7f39350f194.Base

open EuclideanGeometry

open EuclideanGeometry

set_option autoImplicit false in
theorem statopia_math_node_3104088338_a1318138 : ∀ (A B C K M : Plane)
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set Plane))
    (hM : M = midpoint ℝ A B)
    (hK : InsideTriangle B M C K),
    ¬ Collinear ℝ ({C, K, M} : Set Plane) := by
  /- @proof-region region.target-node.session.b7e3e3914850be8a begin -/
  intro A B C K M hABC hM hK
  obtain ⟨α, β, γ, hα, hβ, hγ, hsum, hKdef⟩ := hK
  have hMv : M -ᵥ A = (2:ℝ)⁻¹ • (B -ᵥ A) := by
    rw [hM, midpoint_vsub_left]
    simp
  have hrank_singleton : ∀ d : Plane,
      Module.rank ℝ ↥(Submodule.span ℝ ({d} : Set Plane)) ≤ 1 := by
    intro d
    rw [rank_le_one_iff]
    refine ⟨⟨d, Submodule.subset_span (by simp)⟩, fun v => ?_⟩
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp v.2
    exact ⟨r, Subtype.ext hr⟩
  have hvsub1 : A -ᵥ B = -(B -ᵥ A) := by simp
  have hvsub2 : B -ᵥ C = (B -ᵥ A) - (C -ᵥ A) := by simp
  have hBA : B -ᵥ A = (2:ℝ) • (B -ᵥ M) := by
    have h : B -ᵥ M = (B -ᵥ A) - (M -ᵥ A) := by simp
    rw [h, hMv]
    module
  have hCA_full : C -ᵥ A = (C -ᵥ M) + (B -ᵥ M) := by
    have h : C -ᵥ A = (C -ᵥ M) - (A -ᵥ M) := by simp
    have h2 : A -ᵥ M = -(M -ᵥ A) := by simp
    rw [h, h2, sub_neg_eq_add, hMv, hBA]
    module
  have hKM : K -ᵥ M = α • (B -ᵥ M) + γ • (C -ᵥ M) := by
    have hβ : β = 1 - α - γ := by linarith
    have hsub : ∀ x y : Plane, x -ᵥ y = x - y := by intro x y; simp
    rw [hKdef, hβ]
    simp only [hsub]
    module
  have hkey : ∀ d : Plane,
      (∀ p : Plane, p ∈ ({A, B, C} : Set Plane) →
        p -ᵥ A ∈ Submodule.span ℝ ({d} : Set Plane)) →
      Collinear ℝ ({A, B, C} : Set Plane) := by
    intro d hA
    unfold Collinear vectorSpan
    refine le_trans (Submodule.rank_mono ?_) (hrank_singleton d)
    apply Submodule.span_le.mpr
    intro z hz
    rw [Set.mem_vsub] at hz
    obtain ⟨p, hp, q, hq, hpq⟩ := hz
    rw [← hpq]
    have hstep : p -ᵥ q = (p -ᵥ A) - (q -ᵥ A) := by simp
    rw [hstep]
    exact Submodule.sub_mem _ (hA p hp) (hA q hq)
  have hInd2 : ∀ x y : ℝ, x • (B -ᵥ M) + y • (C -ᵥ M) = 0 → x = 0 ∧ y = 0 := by
    intro x y hxy
    by_cases hx : x = 0
    · subst hx
      simp only [zero_smul, zero_add] at hxy
      by_cases hy : y = 0
      · exact ⟨rfl, hy⟩
      · exfalso
        have hCM0 : C -ᵥ M = 0 := (smul_eq_zero.mp hxy).resolve_left hy
        have hCA0 : C -ᵥ A = (1:ℝ) • (B -ᵥ M) := by
          rw [hCA_full, hCM0, zero_add, one_smul]
        apply hABC
        apply hkey (B -ᵥ M)
        intro p hp
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
        rcases hp with rfl | rfl | rfl
        · exact Submodule.mem_span_singleton.mpr ⟨0, by simp⟩
        · exact Submodule.mem_span_singleton.mpr ⟨2, hBA.symm⟩
        · exact Submodule.mem_span_singleton.mpr ⟨1, hCA0.symm⟩
    · exfalso
      have h1 : x • (B -ᵥ M) = -(y • (C -ᵥ M)) := by
        have h := congrArg (fun t : Plane => t - y • (C -ᵥ M)) hxy
        simpa using h
      have hBM_eq : B -ᵥ M = (-(x⁻¹ * y)) • (C -ᵥ M) := by
        have h2 := congrArg (fun t : Plane => x⁻¹ • t) h1
        simp only [smul_smul, inv_mul_cancel₀ hx, one_smul, smul_neg] at h2
        rw [h2, neg_smul]
      have hCAm : C -ᵥ A = (1 + -(x⁻¹ * y)) • (C -ᵥ M) := by
        rw [hCA_full, hBM_eq]
        module
      have hBAm : B -ᵥ A = (2 * (-(x⁻¹ * y))) • (C -ᵥ M) := by
        rw [hBA, hBM_eq, smul_smul]
      apply hABC
      apply hkey (C -ᵥ M)
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl
      · exact Submodule.mem_span_singleton.mpr ⟨0, by simp⟩
      · exact Submodule.mem_span_singleton.mpr ⟨2 * (-(x⁻¹ * y)), hBAm.symm⟩
      · exact Submodule.mem_span_singleton.mpr ⟨1 + -(x⁻¹ * y), hCAm.symm⟩
  have hdep : Collinear ℝ ({C, K, M} : Set Plane) →
      ∃ a b : ℝ, (a, b) ≠ (0, 0) ∧ a • (K -ᵥ M) + b • (C -ᵥ M) = 0 := by
    intro hc
    unfold Collinear vectorSpan at hc
    rw [rank_le_one_iff] at hc
    obtain ⟨v₀, hv₀⟩ := hc
    have hmemK : K -ᵥ M ∈ Submodule.span ℝ (({C, K, M} : Set Plane) -ᵥ ({C, K, M} : Set Plane)) :=
      Submodule.subset_span (Set.mem_vsub.mpr ⟨K, by simp, M, by simp, rfl⟩)
    have hmemC : C -ᵥ M ∈ Submodule.span ℝ (({C, K, M} : Set Plane) -ᵥ ({C, K, M} : Set Plane)) :=
      Submodule.subset_span (Set.mem_vsub.mpr ⟨C, by simp, M, by simp, rfl⟩)
    obtain ⟨r, hr⟩ := hv₀ ⟨K -ᵥ M, hmemK⟩
    obtain ⟨s, hs⟩ := hv₀ ⟨C -ᵥ M, hmemC⟩
    have hr' : r • (v₀ : Plane) = K -ᵥ M := by simpa using congrArg Subtype.val hr
    have hs' : s • (v₀ : Plane) = C -ᵥ M := by simpa using congrArg Subtype.val hs
    have hkey_eq : s • (K -ᵥ M) = r • (C -ᵥ M) := by
      rw [← hr', ← hs', smul_smul, smul_smul, mul_comm]
    by_cases hz : (s, -r) = (0, 0)
    · have hs0 : s = 0 := by simpa using congrArg Prod.fst hz
      have hr0 : r = 0 := by simpa using congrArg Prod.snd hz
      refine ⟨1, 0, by simp, ?_⟩
      rw [← hr', hr0]
      simp
    · refine ⟨s, -r, fun h => hz h, ?_⟩
      rw [neg_smul, ← sub_eq_add_neg, hkey_eq, sub_self]
  rintro hc
  obtain ⟨a, b, hab, hrel⟩ := hdep hc
  have hcomb : (a * α) • (B -ᵥ M) + (a * γ + b) • (C -ᵥ M) = 0 := by
    have h1 : a • (K -ᵥ M) + b • (C -ᵥ M)
        = (a * α) • (B -ᵥ M) + (a * γ + b) • (C -ᵥ M) := by
      rw [hKM]
      module
    rw [← h1]
    exact hrel
  obtain ⟨hx, hy⟩ := hInd2 (a * α) (a * γ + b) hcomb
  have hαne : α ≠ 0 := ne_of_gt hα
  have ha : a = 0 := (mul_eq_zero.mp hx).resolve_right hαne
  have hb : b = 0 := by
    rw [ha, zero_mul] at hy
    simpa using hy
  exact hab (by simp [ha, hb])
  /- @proof-region region.target-node.session.b7e3e3914850be8a end -/
