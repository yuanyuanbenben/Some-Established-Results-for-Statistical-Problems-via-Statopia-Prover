import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q14.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q14.Base

open MeasureTheory Matrix

open MeasureTheory Matrix

set_option autoImplicit false in
theorem statopia_math_node_1730365501_588c10f1 : ∀ (d : ℕ) (u : Fin d → Fin d → ℝ)
    (horth : ∀ j k : Fin d, dotProduct (u j) (u k) = if j = k then (1 : ℝ) else 0)
    (s : Finset (Fin d)),
    Module.finrank ℝ (Submodule.span ℝ {v : Fin d → ℝ | ∃ j ∈ s, v = u j}) = s.card := by
  /- @proof-region region.target-node.session.d0b16a6a142fc846 begin -/
  intro d u horth s
  have horth' : ∀ a b : Fin d, (∑ x : Fin d, u a x * u b x) = if a = b then (1 : ℝ) else 0 := by
    intro a b
    simpa [dotProduct] using horth a b
  have hli : LinearIndependent ℝ (fun i : ↥s => u (i : Fin d)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg k
    have hkey : (∑ i : ↥s, g i • u (i : Fin d)) ⬝ᵥ u (k : Fin d)
        = ∑ i : ↥s, g i * (if (i : Fin d) = (k : Fin d) then (1 : ℝ) else 0) := by
      simp only [dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      calc ∑ x : Fin d, (∑ i : ↥s, g i * u (i : Fin d) x) * u (k : Fin d) x
          = ∑ x : Fin d, ∑ i : ↥s, (g i * u (i : Fin d) x) * u (k : Fin d) x := by
            simp [Finset.sum_mul]
        _ = ∑ i : ↥s, ∑ x : Fin d, (g i * u (i : Fin d) x) * u (k : Fin d) x := by
            rw [Finset.sum_comm]
        _ = ∑ i : ↥s, g i * ∑ x : Fin d, u (i : Fin d) x * u (k : Fin d) x := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun x _ => by ring)
        _ = ∑ i : ↥s, g i * (if (i : Fin d) = (k : Fin d) then (1 : ℝ) else 0) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [horth']
    have h0 : (∑ i : ↥s, g i • u (i : Fin d)) ⬝ᵥ u (k : Fin d) = 0 := by
      rw [hg]
      simp [dotProduct]
    have h1 : ∑ i : ↥s, g i * (if (i : Fin d) = (k : Fin d) then (1 : ℝ) else 0) = g k := by
      rw [Finset.sum_eq_single k]
      · simp
      · intro i _ hik
        have hne : (i : Fin d) ≠ (k : Fin d) := fun h => hik (Subtype.ext h)
        simp [hne]
      · intro hk
        exact absurd (Finset.mem_univ k) hk
    rw [hkey, h1] at h0
    exact h0
  have hrange : Set.range (fun i : ↥s => u (i : Fin d)) = {v : Fin d → ℝ | ∃ j ∈ s, v = u j} := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨(i : Fin d), i.2, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, hj⟩, rfl⟩
  rw [← hrange, finrank_span_eq_card hli, Fintype.card_coe]
  /- @proof-region region.target-node.session.d0b16a6a142fc846 end -/
