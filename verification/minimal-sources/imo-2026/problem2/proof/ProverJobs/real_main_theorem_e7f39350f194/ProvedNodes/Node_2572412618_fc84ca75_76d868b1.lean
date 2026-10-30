import ProverJobs.real_main_theorem_e7f39350f194.Vocabulary
import ProverJobs.real_main_theorem_e7f39350f194.Base

open EuclideanGeometry

open EuclideanGeometry

set_option autoImplicit false in
theorem statopia_math_node_2572412618_fc84ca75 : ∀ (A B C K L : Plane)
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set Plane))
    (M N : Plane) (hM : M = midpoint ℝ A B) (hN : N = midpoint ℝ A C)
    (hK : InsideTriangle B M C K)
    (hL : InsideTriangle B N C L),
    ∃ s t u v : ℝ,
      0 < s ∧ s < 1 ∧ 0 < t ∧ t < 1 ∧ 0 < u ∧ u < 1 ∧ 0 < v ∧ v < 1 ∧
        (let Y : Plane := A + s • (C - A)
         let X : Plane := A + t • (B - A)
         Sbtw ℝ A X B ∧ Sbtw ℝ A Y C ∧
           K = B + u • (Y - B) ∧ L = C + v • (X - C) ∧ X ≠ Y) := by
  /- @proof-region region.target-node.session.0d80d17b4e792b07 begin -/
  intro A B C K L hABC M N hM hN hK hL
  obtain ⟨α, β, γ, hα, hβ, hγ, hsum, hKeq⟩ := hK
  obtain ⟨α', β', γ', hα', hβ', hγ', hsum', hLeq⟩ := hL
  set s : ℝ := γ / (β / 2 + γ) with hs
  set t : ℝ := α' / (α' + β' / 2) with ht
  set u : ℝ := β / 2 + γ with hu
  set v : ℝ := α' + β' / 2 with hv
  refine ⟨s, t, u, v, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hs]; exact div_pos hγ (by linarith)
  · rw [hs]; exact (div_lt_one (by linarith)).mpr (by linarith)
  · rw [ht]; exact div_pos hα' (by linarith)
  · rw [ht]; exact (div_lt_one (by linarith)).mpr (by linarith)
  · rw [hu]; linarith
  · rw [hu]; linarith
  · rw [hv]; linarith
  · rw [hv]; linarith
  · have hs0 : 0 < s := by rw [hs]; exact div_pos hγ (by linarith)
    have hs1 : s < 1 := by rw [hs]; exact (div_lt_one (by linarith)).mpr (by linarith)
    have ht0 : 0 < t := by rw [ht]; exact div_pos hα' (by linarith)
    have ht1 : t < 1 := by rw [ht]; exact (div_lt_one (by linarith)).mpr (by linarith)
    have hABne : A ≠ B := by
      intro hAB
      apply hABC
      have hset : ({A, B, C} : Set Plane) = {A, C} := by
        ext x; rw [hAB]; simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
          Set.mem_empty_iff_false, or_false] <;> tauto
      rw [hset]; exact collinear_pair ℝ A C
    have hACne : A ≠ C := by
      intro hAC
      apply hABC
      have hset : ({A, B, C} : Set Plane) = {A, B} := by
        ext x; rw [hAC]; simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
          Set.mem_empty_iff_false, or_false] <;> tauto
      rw [hset]; exact collinear_pair ℝ A B
    have hBA0 : B - A ≠ 0 := sub_ne_zero.mpr (Ne.symm hABne)
    have hCA0 : C - A ≠ 0 := sub_ne_zero.mpr (Ne.symm hACne)
    have hsub : (A + t • (B - A)) - A = t • (B - A) := by abel
    have hsub' : (A + s • (C - A)) - A = s • (C - A) := by abel
    have hXa : A + t • (B - A) ≠ A := by
      intro hv
      have h1 : t • (B - A) = 0 := by
        have hc := congrArg (fun p : Plane => p - A) hv
        simpa [hsub] using hc
      rcases smul_eq_zero.mp h1 with h | h
      · linarith
      · exact hBA0 h
    have hYa : A + s • (C - A) ≠ A := by
      intro hv
      have h1 : s • (C - A) = 0 := by
        have hc := congrArg (fun p : Plane => p - A) hv
        simpa [hsub'] using hc
      rcases smul_eq_zero.mp h1 with h | h
      · linarith
      · exact hCA0 h
    have hXb : A + t • (B - A) ≠ B := by
      intro hv
      have h1 : t • (B - A) = B - A := by
        have hc := congrArg (fun p : Plane => p - A) hv
        simpa [hsub] using hc
      have h2 : (t - 1) • (B - A) = 0 := by rw [sub_smul, h1, one_smul, sub_self]
      rcases smul_eq_zero.mp h2 with h | h
      · linarith
      · exact hBA0 h
    have hYc : A + s • (C - A) ≠ C := by
      intro hv
      have h1 : s • (C - A) = C - A := by
        have hc := congrArg (fun p : Plane => p - A) hv
        simpa [hsub'] using hc
      have h2 : (s - 1) • (C - A) = 0 := by rw [sub_smul, h1, one_smul, sub_self]
      rcases smul_eq_zero.mp h2 with h | h
      · linarith
      · exact hCA0 h
    have hSbX : Sbtw ℝ A (A + t • (B - A)) B := by
      unfold Sbtw Wbtw
      refine ⟨?_, hXa, hXb⟩
      refine ⟨t, ⟨by linarith, by linarith⟩, ?_⟩
      simp [AffineMap.lineMap, add_comm]
    have hSbY : Sbtw ℝ A (A + s • (C - A)) C := by
      unfold Sbtw Wbtw
      refine ⟨?_, hYa, hYc⟩
      refine ⟨s, ⟨by linarith, by linarith⟩, ?_⟩
      simp [AffineMap.lineMap, add_comm]
    have hu0 : u ≠ 0 := by rw [hu]; linarith
    have hug0 : β / 2 + γ ≠ 0 := by linarith
    have hus : u * s = γ := by rw [hs]; field_simp
    have hsβ : u * (1 - s) = β / 2 := by rw [mul_sub, mul_one, hus, hu]; ring
    have husum : (1 : ℝ) - u = 1 - β / 2 - γ := by rw [hu]; ring
    have hMv : β • M = (β / 2) • A + (β / 2) • B := by
      rw [hM, midpoint, AffineMap.lineMap_apply]
      show β • ((2 : ℝ)⁻¹ • (B - A) + A) = (β * 2⁻¹) • A + (β * 2⁻¹) • B
      rw [smul_add, smul_smul, smul_sub]
      have hβA : β • A = (β * 2⁻¹) • A + (β * 2⁻¹) • A := by
        have hc : β = β * 2⁻¹ + β * 2⁻¹ := by field_simp <;> ring
        rw [← add_smul]
        exact congrArg (fun r : ℝ => r • A) hc
      rw [hβA]
      abel
    have hKa : K = (β / 2) • A + (α + β / 2) • B + γ • C := by
      rw [hKeq, hMv, add_smul]
      abel
    have hKcoef : α + β / 2 = 1 - β / 2 - γ := by linarith
    have hKb : (β / 2) • A + (α + β / 2) • B + γ • C
        = (β / 2) • A + (1 - β / 2 - γ) • B + γ • C := by
      rw [hKcoef]
    have hKc : B + u • ((A + s • (C - A)) - B)
        = (β / 2) • A + (1 - β / 2 - γ) • B + γ • C := by
      have harg : (A + s • (C - A)) - B = (A - B) + s • (C - A) := by abel
      have h3 : u * (1 - s) = u - u * s := by rw [mul_sub, mul_one]
      have h1 : B + u • ((A + s • (C - A)) - B)
          = (u * (1 - s)) • A + (1 - u) • B + (u * s) • C := by
        simp only [h3, harg, smul_add, smul_smul, smul_sub, sub_smul, one_smul] <;> abel
      have h2 : (u * (1 - s)) • A + (1 - u) • B + (u * s) • C
          = (β / 2) • A + (1 - β / 2 - γ) • B + γ • C := by rw [hsβ, husum, hus]
      exact h1.trans h2
    have hNv : β' • N = (β' / 2) • A + (β' / 2) • C := by
      rw [hN, midpoint, AffineMap.lineMap_apply]
      show β' • ((2 : ℝ)⁻¹ • (C - A) + A) = (β' * 2⁻¹) • A + (β' * 2⁻¹) • C
      rw [smul_add, smul_smul, smul_sub]
      have hβA' : β' • A = (β' * 2⁻¹) • A + (β' * 2⁻¹) • A := by
        have hc : β' = β' * 2⁻¹ + β' * 2⁻¹ := by field_simp <;> ring
        rw [← add_smul]
        exact congrArg (fun r : ℝ => r • A) hc
      rw [hβA']
      abel
    have hLa : L = (β' / 2) • A + α' • B + (β' / 2 + γ') • C := by
      rw [hLeq, hNv, add_smul]
      abel
    have hLcoef : β' / 2 + γ' = 1 - α' - β' / 2 := by linarith
    have hLb : (β' / 2) • A + α' • B + (β' / 2 + γ') • C
        = (β' / 2) • A + α' • B + (1 - α' - β' / 2) • C := by
      rw [hLcoef]
    have hv0 : v ≠ 0 := by rw [hv]; linarith
    have hvt : v * t = α' := by rw [ht]; field_simp
    have hvsβ : v * (1 - t) = β' / 2 := by rw [mul_sub, mul_one, hvt, hv]; ring
    have hvsum : (1 : ℝ) - v = 1 - α' - β' / 2 := by rw [hv]; ring
    have hLc : C + v • ((A + t • (B - A)) - C)
        = (β' / 2) • A + α' • B + (1 - α' - β' / 2) • C := by
      have harg2 : (A + t • (B - A)) - C = (A - C) + t • (B - A) := by abel
      have h3' : v * (1 - t) = v - v * t := by rw [mul_sub, mul_one]
      have h1' : C + v • ((A + t • (B - A)) - C)
          = (v * (1 - t)) • A + (v * t) • B + (1 - v) • C := by
        simp only [h3', harg2, smul_add, smul_smul, smul_sub, sub_smul, one_smul] <;> abel
      have h2' : (v * (1 - t)) • A + (v * t) • B + (1 - v) • C
          = (β' / 2) • A + α' • B + (1 - α' - β' / 2) • C := by rw [hvsβ, hvt, hvsum]
      exact h1'.trans h2'
    have hXneY : A + t • (B - A) ≠ A + s • (C - A) := by
      intro hXY
      have hrel : t • (B - A) = s • (C - A) := by
        have hc := congrArg (fun p : Plane => p - A) hXY
        simpa [hsub, hsub'] using hc
      have htne : t ≠ 0 := ne_of_gt ht0
      have hBA : B - A = (s / t) • (C - A) := by
        have h2 : (s * t⁻¹) • (C - A) = B - A := by
          rw [mul_comm, ← smul_smul, ← hrel, inv_smul_smul₀ htne]
        rw [div_eq_mul_inv, h2]
      have hcol : Collinear ℝ ({A, B, C} : Set Plane) := by
        unfold Collinear vectorSpan
        have hACcol : Module.rank ℝ ↥(Submodule.span ℝ (({A, C} : Set Plane) -ᵥ ({A, C} : Set Plane))) ≤ 1 := by
          have h := collinear_pair ℝ A C
          unfold Collinear vectorSpan at h
          exact h
        have hB' : B = A + (s / t) • (C - A) := by rw [← hBA]; abel
        have hCAgen : (C - A) ∈ (({A, C} : Set Plane) -ᵥ ({A, C} : Set Plane)) :=
          ⟨C, by simp, A, by simp, rfl⟩
        have hCAspan : (C - A) ∈ Submodule.span ℝ (({A, C} : Set Plane) -ᵥ ({A, C} : Set Plane)) :=
          Submodule.subset_span hCAgen
        have hex : ∀ p ∈ ({A, B, C} : Set Plane), ∃ c : ℝ, p = A + c • (C - A) := by
          intro p hp
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
          rcases hp with rfl | rfl | rfl
          · exact ⟨0, by rw [zero_smul, add_zero]⟩
          · exact ⟨s / t, hB'⟩
          · exact ⟨1, by rw [one_smul]; abel⟩
        have hgen : ∀ p q : Plane, p ∈ ({A, B, C} : Set Plane) → q ∈ ({A, B, C} : Set Plane) →
            p -ᵥ q ∈ Submodule.span ℝ (({A, C} : Set Plane) -ᵥ ({A, C} : Set Plane)) := by
          intro p q hp hq
          obtain ⟨cp, hcp⟩ := hex p hp
          obtain ⟨cq, hcq⟩ := hex q hq
          have hval : p -ᵥ q = (cp - cq) • (C - A) := by
            show p - q = (cp - cq) • (C - A)
            rw [hcp, hcq]
            module
          rw [hval]
          exact Submodule.smul_mem _ _ hCAspan
        have hle1 : Submodule.span ℝ (({A, B, C} : Set Plane) -ᵥ ({A, B, C} : Set Plane)) ≤
            Submodule.span ℝ (({A, C} : Set Plane) -ᵥ ({A, C} : Set Plane)) := by
          rw [Submodule.span_le]
          rintro x ⟨p, hp, q, hq, rfl⟩
          exact hgen p q hp hq
        have hle2 : Submodule.span ℝ (({A, C} : Set Plane) -ᵥ ({A, C} : Set Plane)) ≤
            Submodule.span ℝ (({A, B, C} : Set Plane) -ᵥ ({A, B, C} : Set Plane)) :=
          Submodule.span_mono (by
            rintro x ⟨p, hp, q, hq, rfl⟩
            refine ⟨p, ?_, q, ?_, rfl⟩
            · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp ⊢
              tauto
            · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq ⊢
              tauto)
        have heq := le_antisymm hle1 hle2
        rw [heq]
        exact hACcol
      exact hABC hcol
    exact ⟨hSbX, hSbY, hKa.trans (hKb.trans hKc.symm),
      hLa.trans (hLb.trans hLc.symm), hXneY⟩
  /- @proof-region region.target-node.session.0d80d17b4e792b07 end -/
