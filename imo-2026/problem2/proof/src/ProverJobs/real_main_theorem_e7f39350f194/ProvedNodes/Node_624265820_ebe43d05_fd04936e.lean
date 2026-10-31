import ProverJobs.real_main_theorem_e7f39350f194.Vocabulary
import ProverJobs.real_main_theorem_e7f39350f194.Base

open EuclideanGeometry

open EuclideanGeometry

set_option autoImplicit false in
theorem statopia_math_node_624265820_ebe43d05 : ∀ (P Q R : Plane),
    ¬ Collinear ℝ ({P, Q, R} : Set Plane) ↔ LinearIndependent ℝ ![Q - P, R - P] := by
  /- @proof-region region.target-node.session.7e7904a29f833bc2 begin -/
  intro P Q R
  rw [collinear_iff_rank_le_one]
  have hspan : vectorSpan ℝ ({P, Q, R} : Set Plane) = Submodule.span ℝ ({Q - P, R - P} : Set Plane) := by
    rw [vectorSpan_eq_span_vsub_set_right (k := ℝ) (by simp : P ∈ ({P, Q, R} : Set Plane))]
    have himg : (fun x : Plane => x -ᵥ P) '' ({P, Q, R} : Set Plane) = ({0, Q - P, R - P} : Set Plane) := by
      rw [Set.image_insert_eq, Set.image_insert_eq]
      ext x
      simp [vsub_eq_sub]
    rw [himg, Submodule.span_insert_zero]
  rw [hspan, LinearIndependent.pair_iff]
  have hrank_v : ∀ s t : ℝ, s ≠ 0 → s • (Q - P) + t • (R - P) = 0 →
      Module.rank ℝ ↥(Submodule.span ℝ ({Q - P, R - P} : Set Plane)) ≤ 1 := by
    intro s t hs hst
    have h1 : s • (Q - P) = -(t • (R - P)) := eq_neg_iff_add_eq_zero.mpr hst
    have hu : Q - P = (-(s⁻¹ * t)) • (R - P) := by
      calc Q - P = s⁻¹ • (s • (Q - P)) := by rw [smul_smul, inv_mul_cancel₀ hs, one_smul]
        _ = s⁻¹ • (-(t • (R - P))) := by rw [h1]
        _ = (-(s⁻¹ * t)) • (R - P) := by rw [smul_neg, smul_smul, neg_smul]
    rw [rank_le_one_iff]
    refine ⟨⟨R - P, Submodule.subset_span (by simp)⟩, fun w => ?_⟩
    obtain ⟨x, hx⟩ := w
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hx
    refine ⟨a * (-(s⁻¹ * t)) + b, ?_⟩
    apply Subtype.ext
    show (a * (-(s⁻¹ * t)) + b) • (R - P) = x
    rw [← hab, hu, smul_smul, add_smul]
  have hrank_u : ∀ s t : ℝ, t ≠ 0 → s • (Q - P) + t • (R - P) = 0 →
      Module.rank ℝ ↥(Submodule.span ℝ ({Q - P, R - P} : Set Plane)) ≤ 1 := by
    intro s t ht hst
    have h2 : t • (R - P) = -(s • (Q - P)) := eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact hst)
    have hv : R - P = (-(t⁻¹ * s)) • (Q - P) := by
      calc R - P = t⁻¹ • (t • (R - P)) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
        _ = t⁻¹ • (-(s • (Q - P))) := by rw [h2]
        _ = (-(t⁻¹ * s)) • (Q - P) := by rw [smul_neg, smul_smul, neg_smul]
    rw [rank_le_one_iff]
    refine ⟨⟨Q - P, Submodule.subset_span (by simp)⟩, fun w => ?_⟩
    obtain ⟨x, hx⟩ := w
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hx
    refine ⟨b * (-(t⁻¹ * s)) + a, ?_⟩
    apply Subtype.ext
    show (b * (-(t⁻¹ * s)) + a) • (Q - P) = x
    rw [← hab, hv, smul_smul, add_smul, add_comm]
  constructor
  · intro hn s t hst
    refine ⟨?_, ?_⟩
    · by_contra hs
      exact hn (hrank_v s t hs hst)
    · by_contra ht
      exact hn (hrank_u s t ht hst)
  · intro hli hle
    rw [rank_le_one_iff] at hle
    obtain ⟨v₀, hv₀⟩ := hle
    obtain ⟨a, ha'⟩ := hv₀ ⟨Q - P, Submodule.subset_span (by simp)⟩
    obtain ⟨b, hb'⟩ := hv₀ ⟨R - P, Submodule.subset_span (by simp)⟩
    have ha : a • (v₀ : Plane) = Q - P := by simpa using congrArg Subtype.val ha'
    have hb : b • (v₀ : Plane) = R - P := by simpa using congrArg Subtype.val hb'
    have h0 : b • (Q - P) + (-a) • (R - P) = 0 := by
      have e1 : b • (a • (v₀ : Plane)) = b • (Q - P) := congrArg (fun z : Plane => b • z) ha
      have e2 : (-a) • (b • (v₀ : Plane)) = (-a) • (R - P) := congrArg (fun z : Plane => (-a) • z) hb
      rw [← e1, ← e2, smul_comm, ← add_smul, add_neg_cancel, zero_smul]
    have h1 := hli b (-a) h0
    have ha0 : a = 0 := neg_eq_zero.mp h1.2
    have hb0 : b = 0 := h1.1
    have hu0 : Q - P = 0 := by rw [← ha, ha0, zero_smul]
    have hv0 : R - P = 0 := by rw [← hb, hb0, zero_smul]
    have h2 := hli 1 0 (by rw [hu0, hv0, smul_zero, smul_zero, add_zero])
    exact one_ne_zero h2.1
  /- @proof-region region.target-node.session.7e7904a29f833bc2 end -/
