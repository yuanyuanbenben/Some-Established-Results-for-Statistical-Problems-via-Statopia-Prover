import ProverJobs.real_main_theorem_e7f39350f194.Vocabulary
import ProverJobs.real_main_theorem_e7f39350f194.Base

open EuclideanGeometry

open EuclideanGeometry

set_option autoImplicit false in
theorem statopia_math_node_3516123686_7891845d : ∀ (A B C K L O : Plane)
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set Plane))
    (M N : Plane) (hM : M = midpoint ℝ A B) (hN : N = midpoint ℝ A C)
    (hK : InsideTriangle B M C K)
    (hL : InsideTriangle B N C L)
    (hKangle : InsideAngle L B A K)
    (hO : IsCircumcentre A K L O),
    ¬ Collinear ℝ ({A, K, L} : Set Plane) := by
  /- @proof-region region.target-node.session.52ee51795496ac76 begin -/
  intro A B C K L O hABC M N hM hN hK hL hKangle hO
  obtain ⟨α, β, γ, hα, hβ, hγ, hsum, hKeq⟩ := hK
  obtain ⟨α', β', γ', hα', hβ', hγ', hsum', hLeq⟩ := hL
  obtain ⟨s, t, hs, ht, hang⟩ := hKangle
  obtain ⟨hOA, hOK⟩ := hO
  have hmid1 : M = (1 / 2 : ℝ) • A + (1 / 2 : ℝ) • B := by
    rw [hM, midpoint_eq_smul_add, smul_add]
    norm_num
  have hAK : A ≠ K := by
    intro hAKeq
    apply hABC
    have hAeq : A = α • B + β • M + γ • C := hAKeq.trans hKeq
    have hAexp : A = (β / 2) • A + (α + β / 2) • B + γ • C := by
      nth_rewrite 1 [hAeq]
      rw [hmid1]
      module
    have hgam : γ = 1 - α - β := by linarith
    have hsub : (1 - β / 2) • (A - C) - (α + β / 2) • (B - C) = 0 := by
      have heq : (1 - β / 2) • (A - C) - (α + β / 2) • (B - C)
          = A - ((β / 2) • A + (α + β / 2) • B + γ • C) := by
        rw [hgam]
        module
      have htmp : A - ((β / 2) • A + (α + β / 2) • B + γ • C) = 0 :=
        sub_eq_zero.mpr hAexp
      rw [heq, htmp]
    have hrel : (1 - β / 2) • (A - C) = (α + β / 2) • (B - C) := sub_eq_zero.mp hsub
    have hne : (1 - β / 2) ≠ 0 := ne_of_gt (by linarith)
    have hAC : A - C = ((1 - β / 2)⁻¹ * (α + β / 2)) • (B - C) := by
      have h2 : ((1 - β / 2)⁻¹ * (1 - β / 2)) • (A - C)
          = ((1 - β / 2)⁻¹ * (α + β / 2)) • (B - C) := by
        rw [← smul_smul, hrel, smul_smul]
      rw [inv_mul_cancel₀ hne, one_smul] at h2
      exact h2
    rw [collinear_iff_exists_forall_eq_smul_vadd]
    refine ⟨C, B - C, ?_⟩
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with hpa | hpb | hpc
    · rw [hpa]
      refine ⟨(α + β / 2) / (1 - β / 2), ?_⟩
      have hX : A - C = ((α + β / 2) / (1 - β / 2)) • (B - C) := by
        rw [div_eq_inv_mul]
        exact hAC
      rw [vadd_eq_add, ← hX, sub_add_cancel]
    · rw [hpb]
      refine ⟨1, ?_⟩
      rw [one_smul, vadd_eq_add, sub_add_cancel]
    · rw [hpc]
      refine ⟨0, ?_⟩
      rw [zero_smul]
      simp
  have hAL : A ≠ L := by
    intro hALeq
    apply hABC
    have hmid2 : N = (1 / 2 : ℝ) • A + (1 / 2 : ℝ) • C := by
      rw [hN, midpoint_eq_smul_add, smul_add]
      norm_num
    have hAeq : A = α' • B + β' • N + γ' • C := hALeq.trans hLeq
    have hAexp : A = (β' / 2) • A + α' • B + (β' / 2 + γ') • C := by
      nth_rewrite 1 [hAeq]
      rw [hmid2]
      module
    have hgam' : γ' = 1 - α' - β' := by linarith
    have hsub : (1 - β' / 2) • (A - C) - α' • (B - C) = 0 := by
      have heq : (1 - β' / 2) • (A - C) - α' • (B - C)
          = A - ((β' / 2) • A + α' • B + (β' / 2 + γ') • C) := by
        rw [hgam']
        module
      have htmp : A - ((β' / 2) • A + α' • B + (β' / 2 + γ') • C) = 0 :=
        sub_eq_zero.mpr hAexp
      rw [heq, htmp]
    have hrel : (1 - β' / 2) • (A - C) = α' • (B - C) := sub_eq_zero.mp hsub
    have hne : (1 - β' / 2) ≠ 0 := ne_of_gt (by linarith)
    have hAC : A - C = ((1 - β' / 2)⁻¹ * α') • (B - C) := by
      have h2 : ((1 - β' / 2)⁻¹ * (1 - β' / 2)) • (A - C)
          = ((1 - β' / 2)⁻¹ * α') • (B - C) := by
        rw [← smul_smul, hrel, smul_smul]
      rw [inv_mul_cancel₀ hne, one_smul] at h2
      exact h2
    rw [collinear_iff_exists_forall_eq_smul_vadd]
    refine ⟨C, B - C, ?_⟩
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with hpa | hpb | hpc
    · rw [hpa]
      refine ⟨α' / (1 - β' / 2), ?_⟩
      have hX : A - C = (α' / (1 - β' / 2)) • (B - C) := by
        rw [div_eq_inv_mul]
        exact hAC
      rw [vadd_eq_add, ← hX, sub_add_cancel]
    · rw [hpb]
      refine ⟨1, ?_⟩
      rw [one_smul, vadd_eq_add, sub_add_cancel]
    · rw [hpc]
      refine ⟨0, ?_⟩
      rw [zero_smul]
      simp
  have hKL : K ≠ L := by
    intro hKLeq
    apply hABC
    have hkb : K - B = (β / 2) • (A - B) + γ • (C - B) := by
      have hg : γ = 1 - α - β := by linarith
      rw [hKeq, hmid1, hg]
      module
    have h1 : (1 - s) • (K - B) = t • (A - B) := by
      have h := hang
      rw [← hKLeq] at h
      have htmp : (K - B) - s • (K - B) = t • (A - B) := by
        nth_rewrite 1 [h]
        abel
      have heq : (1 - s) • (K - B) = (K - B) - s • (K - B) := by module
      rw [heq]
      exact htmp
    have hsum0 : (1 - s) • ((β / 2) • (A - B) + γ • (C - B)) - t • (A - B) = 0 := by
      have h := h1
      rw [hkb] at h
      rw [h, sub_self]
    by_cases hs1 : s = 1
    · have h0 : t • (A - B) = 0 := by
        have h := h1
        rw [hs1, sub_self, zero_smul] at h
        exact h.symm
      have hAB : A = B := by
        have h := congrArg (fun x : Plane => t⁻¹ • x) h0
        simp only [smul_zero, smul_smul, inv_mul_cancel₀ (ne_of_gt ht), one_smul] at h
        exact sub_eq_zero.mp h
      rw [collinear_iff_exists_forall_eq_smul_vadd]
      refine ⟨B, C - B, ?_⟩
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with hpa | hpb | hpc
      · rw [hpa, hAB]
        refine ⟨0, ?_⟩
        rw [zero_smul]
        simp
      · rw [hpb]
        refine ⟨0, ?_⟩
        rw [zero_smul]
        simp
      · rw [hpc]
        refine ⟨1, ?_⟩
        rw [one_smul, vadd_eq_add, sub_add_cancel]
    · have ha : γ * (1 - s) ≠ 0 :=
        mul_ne_zero (ne_of_gt hγ) (sub_ne_zero.mpr (Ne.symm hs1))
      have hCrel : (γ * (1 - s)) • (C - B) = (t - (1 - s) * (β / 2)) • (A - B) := by
        have heq : (1 - s) • ((β / 2) • (A - B) + γ • (C - B)) - t • (A - B)
            = (γ * (1 - s)) • (C - B) - (t - (1 - s) * (β / 2)) • (A - B) := by module
        rw [heq] at hsum0
        exact sub_eq_zero.mp hsum0
      have hCrel2 : C - B = ((t - (1 - s) * (β / 2)) / (γ * (1 - s))) • (A - B) := by
        have h2 : ((γ * (1 - s))⁻¹ * (γ * (1 - s))) • (C - B)
            = ((γ * (1 - s))⁻¹ * (t - (1 - s) * (β / 2))) • (A - B) := by
          rw [← smul_smul, hCrel, smul_smul]
        rw [inv_mul_cancel₀ ha, one_smul] at h2
        rw [div_eq_inv_mul]
        exact h2
      rw [collinear_iff_exists_forall_eq_smul_vadd]
      refine ⟨B, A - B, ?_⟩
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with hpa | hpb | hpc
      · rw [hpa]
        refine ⟨1, ?_⟩
        rw [one_smul, vadd_eq_add, sub_add_cancel]
      · rw [hpb]
        refine ⟨0, ?_⟩
        rw [zero_smul]
        simp
      · rw [hpc]
        refine ⟨(t - (1 - s) * (β / 2)) / (γ * (1 - s)), ?_⟩
        rw [vadd_eq_add, ← hCrel2, sub_add_cancel]
  intro hcol
  rw [collinear_iff_exists_forall_eq_smul_vadd] at hcol
  obtain ⟨p₀, v, hw⟩ := hcol
  have hA' := hw A (by simp)
  have hK'' := hw K (by simp)
  have hL'' := hw L (by simp)
  obtain ⟨rA, hA⟩ := hA'
  obtain ⟨rK, hK'⟩ := hK''
  obtain ⟨rL, hL'⟩ := hL''
  set u : Plane := O - A with hu
  have hAKm : A - K = (rA - rK) • v := by
    rw [hA, hK', vadd_eq_add, vadd_eq_add, sub_smul]
    abel
  have hALm : A - L = (rA - rL) • v := by
    rw [hA, hL', vadd_eq_add, vadd_eq_add, sub_smul]
    abel
  have hKA : O - K = u + (rA - rK) • v := by
    rw [hu, ← hAKm]
    abel
  have hLA : O - L = u + (rA - rL) • v := by
    rw [hu, ← hALm]
    abel
  have hNAK : ‖O - A‖ = ‖O - K‖ := by
    rw [dist_eq_norm] at hOA
    exact hOA
  have hNAL : ‖O - A‖ = ‖O - L‖ := by
    rw [dist_eq_norm] at hOK
    exact hOK
  have hnormK : ‖u + (rA - rK) • v‖ = ‖u‖ := by
    rw [← hKA, hu]
    exact hNAK.symm
  have hnormL : ‖u + (rA - rL) • v‖ = ‖u‖ := by
    rw [← hLA, hu]
    exact hNAL.symm
  have hsqK : ‖u + (rA - rK) • v‖ ^ 2 = ‖u‖ ^ 2 := by rw [hnormK]
  have hsqL : ‖u + (rA - rL) • v‖ ^ 2 = ‖u‖ ^ 2 := by rw [hnormL]
  have hexpK := norm_add_sq_real u ((rA - rK) • v)
  have hexpL := norm_add_sq_real u ((rA - rL) • v)
  have hCK : 2 * inner ℝ u ((rA - rK) • v) + ‖(rA - rK) • v‖ ^ 2 = 0 := by
    linarith [hexpK, hsqK]
  have hCL : 2 * inner ℝ u ((rA - rL) • v) + ‖(rA - rL) • v‖ ^ 2 = 0 := by
    linarith [hexpL, hsqL]
  have hrAK : rA - rK ≠ 0 := by
    intro h
    apply hAK
    have he : rA = rK := sub_eq_zero.mp h
    rw [hA, hK', he]
  have hrAL : rA - rL ≠ 0 := by
    intro h
    apply hAL
    have he : rA = rL := sub_eq_zero.mp h
    rw [hA, hL', he]
  have hfacK : (rA - rK) * (2 * inner ℝ u v + (rA - rK) * ‖v‖ ^ 2) = 0 := by
    have h := hCK
    rw [real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at h
    have hring : (rA - rK) * (2 * inner ℝ u v + (rA - rK) * ‖v‖ ^ 2)
        = 2 * ((rA - rK) * inner ℝ u v) + (rA - rK) ^ 2 * ‖v‖ ^ 2 := by ring
    rw [hring]
    exact h
  have hfacL : (rA - rL) * (2 * inner ℝ u v + (rA - rL) * ‖v‖ ^ 2) = 0 := by
    have h := hCL
    rw [real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at h
    have hring : (rA - rL) * (2 * inner ℝ u v + (rA - rL) * ‖v‖ ^ 2)
        = 2 * ((rA - rL) * inner ℝ u v) + (rA - rL) ^ 2 * ‖v‖ ^ 2 := by ring
    rw [hring]
    exact h
  have hXK : 2 * inner ℝ u v + (rA - rK) * ‖v‖ ^ 2 = 0 := by
    rcases mul_eq_zero.mp hfacK with h | h
    · exact absurd h hrAK
    · exact h
  have hXL : 2 * inner ℝ u v + (rA - rL) * ‖v‖ ^ 2 = 0 := by
    rcases mul_eq_zero.mp hfacL with h | h
    · exact absurd h hrAL
    · exact h
  have hD : (rK - rL) * ‖v‖ ^ 2 = 0 := by
    have hsub : (rA - rK) * ‖v‖ ^ 2 - (rA - rL) * ‖v‖ ^ 2 = 0 := by
      linarith [hXK, hXL]
    have hring : (rA - rK) * ‖v‖ ^ 2 - (rA - rL) * ‖v‖ ^ 2
        = -((rK - rL) * ‖v‖ ^ 2) := by ring
    rw [hring] at hsub
    linarith [hsub]
  rcases mul_eq_zero.mp hD with h | h
  · apply hKL
    have he : rK = rL := sub_eq_zero.mp h
    rw [hK', hL', he]
  · apply hAK
    have hv0 : ‖v‖ = 0 := sq_eq_zero_iff.mp h
    have hv : v = 0 := norm_eq_zero.mp hv0
    rw [hA, hK', hv]
    simp
  /- @proof-region region.target-node.session.52ee51795496ac76 end -/
