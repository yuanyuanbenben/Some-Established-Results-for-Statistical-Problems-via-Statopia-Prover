import ProverJobs.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Base

namespace PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed

-- External DAG node: ext_model_1 (AXIOM)
example : Prop := (open MeasureTheory ProbabilityTheory in (open scoped ENNReal BigOperators in (∃ C : ℝ, 0 < C ∧
    ∀ (r n : ℕ), 1 ≤ r → ∀ (hn : 1 ≤ n),
    ∀ (Om : Type*) [MeasurableSpace Om] (P : Measure Om),
      IsProbabilityMeasure P →
    ∀ (X : Fin n → Om → Fin r → ℝ),
      (hXmeas : ∀ i, Measurable (X i)) →
      (hindep : iIndepFun (fun (i : Fin n) (om : Om) => X i om) P) →
      (hident : ∀ i i' : Fin n, IdentDistrib (X i) (X i') P P) →
      (hmean : ∀ j : Fin r, Integrable (fun om => X ⟨0, hn⟩ om j) P ∧
        ∫ om, X ⟨0, hn⟩ om j ∂P = 0) →
      (hcov : ∀ i j : Fin r,
        Integrable (fun om => X ⟨0, hn⟩ om i * X ⟨0, hn⟩ om j) P ∧
        ∫ om, X ⟨0, hn⟩ om i * X ⟨0, hn⟩ om j ∂P = if i = j then 1 else 0) →
      (hthird : Integrable (fun om => (∑ j : Fin r, (X ⟨0, hn⟩ om j) ^ 2) ^ ((3 : ℝ) / 2)) P) →
      ∀ (A : Set (Fin r → ℝ)), MeasurableSet A → Convex ℝ A →
        |(P (Set.preimage
            (fun om => (Real.sqrt (n : ℝ))⁻¹ • ∑ i : Fin n, X i om) A)).toReal -
          ((Measure.pi (fun _ : Fin r => gaussianReal 0 1)) A).toReal|
          ≤ C * (r : ℝ) ^ ((1 : ℝ) / 4) *
              (∫ om, (∑ j : Fin r, (X ⟨0, hn⟩ om j) ^ 2) ^ ((3 : ℝ) / 2) ∂P) *
              (n : ℝ) ^ (-(1 : ℝ) / 2))))
axiom ExternalRevision_bb11d988567af52975f2aee092d3dde32f3d1f221c6808fdb6d1bca0ad00547c.citation : (open MeasureTheory ProbabilityTheory in (open scoped ENNReal BigOperators in (∃ C : ℝ, 0 < C ∧
    ∀ (r n : ℕ), 1 ≤ r → ∀ (hn : 1 ≤ n),
    ∀ (Om : Type*) [MeasurableSpace Om] (P : Measure Om),
      IsProbabilityMeasure P →
    ∀ (X : Fin n → Om → Fin r → ℝ),
      (hXmeas : ∀ i, Measurable (X i)) →
      (hindep : iIndepFun (fun (i : Fin n) (om : Om) => X i om) P) →
      (hident : ∀ i i' : Fin n, IdentDistrib (X i) (X i') P P) →
      (hmean : ∀ j : Fin r, Integrable (fun om => X ⟨0, hn⟩ om j) P ∧
        ∫ om, X ⟨0, hn⟩ om j ∂P = 0) →
      (hcov : ∀ i j : Fin r,
        Integrable (fun om => X ⟨0, hn⟩ om i * X ⟨0, hn⟩ om j) P ∧
        ∫ om, X ⟨0, hn⟩ om i * X ⟨0, hn⟩ om j ∂P = if i = j then 1 else 0) →
      (hthird : Integrable (fun om => (∑ j : Fin r, (X ⟨0, hn⟩ om j) ^ 2) ^ ((3 : ℝ) / 2)) P) →
      ∀ (A : Set (Fin r → ℝ)), MeasurableSet A → Convex ℝ A →
        |(P (Set.preimage
            (fun om => (Real.sqrt (n : ℝ))⁻¹ • ∑ i : Fin n, X i om) A)).toReal -
          ((Measure.pi (fun _ : Fin r => gaussianReal 0 1)) A).toReal|
          ≤ C * (r : ℝ) ^ ((1 : ℝ) / 4) *
              (∫ om, (∑ j : Fin r, (X ⟨0, hn⟩ om j) ^ 2) ^ ((3 : ℝ) / 2) ∂P) *
              (n : ℝ) ^ (-(1 : ℝ) / 2))))

