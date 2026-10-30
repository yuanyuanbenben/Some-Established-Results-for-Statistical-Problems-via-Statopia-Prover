import ProverJobs.job_paper_df5fdc450bf24d85b08215e07b20fdad.Base

namespace PaperProofTasks.job_paper_df5fdc450bf24d85b08215e07b20fdad

-- External DAG node: ext_model_1 (AXIOM)
example : Prop := (open MeasureTheory ProbabilityTheory Filter in (open scoped ENNReal Topology BigOperators in (∃ c : ℝ, 0 < c ∧
      ∀ (r : ℝ) (m : ℕ) (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω),
        1 ≤ r → 1 ≤ m → IsProbabilityMeasure μ →
        ∀ (xi : Fin m → Ω → ℝ),
          (∀ j, Measurable (xi j)) →
          iIndepFun (fun j : Fin m => xi j) μ →
          (∀ j, Integrable (fun ω => |xi j ω| ^ r) μ) →
          (((∀ j, ∀ᵐ ω ∂μ, 0 ≤ xi j ω) →
              Statlib.Imported.LqNorm (fun ω => ∑ j : Fin m, xi j ω) r μ
                ≤ ENNReal.ofReal (c * (r / max (Real.log r) 1)) *
                    max (Statlib.Imported.LqNorm (fun ω => ∑ j : Fin m, xi j ω) 1 μ)
                      (Statlib.Imported.LqNorm
                        (fun ω => (∑ j : Fin m, |xi j ω| ^ r) ^ (1 / r)) r μ)) ∧
            ((2 < r ∧ (∀ j, ∫ ω, xi j ω ∂μ = 0)) →
              Statlib.Imported.LqNorm (fun ω => ∑ j : Fin m, xi j ω) r μ
                ≤ ENNReal.ofReal (c * (r / max (Real.log r) 1)) *
                    max (Statlib.Imported.LqNorm (fun ω => ∑ j : Fin m, xi j ω) 2 μ)
                      (Statlib.Imported.LqNorm
                        (fun ω => (∑ j : Fin m, |xi j ω| ^ r) ^ (1 / r)) r μ))))))
axiom ExternalRevision_b6071945cf90850933f075b907c86da3bc0900ed9d0e2c5e428f11284eee47a4.citation : (open MeasureTheory ProbabilityTheory Filter in (open scoped ENNReal Topology BigOperators in (∃ c : ℝ, 0 < c ∧
      ∀ (r : ℝ) (m : ℕ) (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω),
        1 ≤ r → 1 ≤ m → IsProbabilityMeasure μ →
        ∀ (xi : Fin m → Ω → ℝ),
          (∀ j, Measurable (xi j)) →
          iIndepFun (fun j : Fin m => xi j) μ →
          (∀ j, Integrable (fun ω => |xi j ω| ^ r) μ) →
          (((∀ j, ∀ᵐ ω ∂μ, 0 ≤ xi j ω) →
              Statlib.Imported.LqNorm (fun ω => ∑ j : Fin m, xi j ω) r μ
                ≤ ENNReal.ofReal (c * (r / max (Real.log r) 1)) *
                    max (Statlib.Imported.LqNorm (fun ω => ∑ j : Fin m, xi j ω) 1 μ)
                      (Statlib.Imported.LqNorm
                        (fun ω => (∑ j : Fin m, |xi j ω| ^ r) ^ (1 / r)) r μ)) ∧
            ((2 < r ∧ (∀ j, ∫ ω, xi j ω ∂μ = 0)) →
              Statlib.Imported.LqNorm (fun ω => ∑ j : Fin m, xi j ω) r μ
                ≤ ENNReal.ofReal (c * (r / max (Real.log r) 1)) *
                    max (Statlib.Imported.LqNorm (fun ω => ∑ j : Fin m, xi j ω) 2 μ)
                      (Statlib.Imported.LqNorm
                        (fun ω => (∑ j : Fin m, |xi j ω| ^ r) ^ (1 / r)) r μ))))))

