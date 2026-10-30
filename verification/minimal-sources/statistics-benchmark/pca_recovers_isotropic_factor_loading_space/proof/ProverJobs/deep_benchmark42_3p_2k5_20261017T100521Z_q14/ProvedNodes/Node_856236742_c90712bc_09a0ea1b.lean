import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q14.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q14.Base

open MeasureTheory Matrix

open MeasureTheory Matrix

set_option autoImplicit false in
theorem statopia_math_node_856236742_c90712bc : ∀ (d q : ℕ) (Lambda : Matrix (Fin d) (Fin q) ℝ)
    (lambda : Fin d → ℝ) (u : Fin d → Fin d → ℝ)
    (hspan : Submodule.span ℝ (Set.range u) = ⊤)
    (heig : ∀ j : Fin d, (Lambda * Lambdaᵀ) *ᵥ u j = lambda j • u j),
    ∀ x : Fin d → ℝ,
      (Lambda * Lambdaᵀ) *ᵥ x ∈
        Submodule.span ℝ {v : Fin d → ℝ | ∃ j : Fin d, lambda j ≠ 0 ∧ v = u j} := by
  /- @proof-region region.target-node.session.0f40a4017df7c57d begin -/
  intro d q Lambda lambda u hspan heig x
  set W : Submodule ℝ (Fin d → ℝ) :=
    Submodule.span ℝ {v : Fin d → ℝ | ∃ j : Fin d, lambda j ≠ 0 ∧ v = u j} with hW
  have hgen : ∀ j : Fin d, (Lambda * Lambdaᵀ) *ᵥ u j ∈ W := by
    intro j
    rw [heig j]
    by_cases hj : lambda j = 0
    · rw [hj, zero_smul]
      exact W.zero_mem
    · exact W.smul_mem (lambda j) (by
        rw [hW]
        exact Submodule.subset_span ⟨j, hj, rfl⟩)
  have htop : (⊤ : Submodule ℝ (Fin d → ℝ)) ≤
      { carrier := {y : Fin d → ℝ | (Lambda * Lambdaᵀ) *ᵥ y ∈ W}
        zero_mem' := by
          show (Lambda * Lambdaᵀ) *ᵥ (0 : Fin d → ℝ) ∈ W
          rw [Matrix.mulVec_zero]
          exact W.zero_mem
        add_mem' := by
          intro a b ha hb
          show (Lambda * Lambdaᵀ) *ᵥ (a + b) ∈ W
          rw [Matrix.mulVec_add]
          exact W.add_mem ha hb
        smul_mem' := by
          intro c a ha
          show (Lambda * Lambdaᵀ) *ᵥ (c • a) ∈ W
          rw [Matrix.mulVec_smul]
          exact W.smul_mem c ha } := by
    rw [← hspan]
    refine Submodule.span_le.mpr ?_
    rintro v ⟨j, rfl⟩
    exact hgen j
  exact htop Submodule.mem_top
  /- @proof-region region.target-node.session.0f40a4017df7c57d end -/
