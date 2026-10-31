import ProverJobs.job_paper_df5fdc450bf24d85b08215e07b20fdad.Base

namespace PaperProofTasks.job_paper_df5fdc450bf24d85b08215e07b20fdad

-- External DAG node: ext_model_2 (AXIOM)
example : Prop := (open MeasureTheory ProbabilityTheory Filter in (open scoped ENNReal Topology BigOperators in (open Statlib.Imported in (∃ C : ℝ, 0 < C ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : Ω → ℝ) (hX : Measurable X),
        
        ((∀ t : ℝ, 0 ≤ t → μ {ω | t ≤ |X ω|} ≤ ENNReal.ofReal (2 * Real.exp (-t)))
          → ∃ K2 : ℝ, 0 < K2 ∧ K2 ≤ C ∧
              ∀ r : ℝ, 1 ≤ r → LqNorm X r μ ≤ ENNReal.ofReal (K2 * r)) ∧
        
        ((∃ K2 : ℝ, 1 ≤ K2 ∧
              ∀ r : ℝ, 1 ≤ r → LqNorm X r μ ≤ ENNReal.ofReal (K2 * r))
          → ∃ K1 : ℝ, 0 < K1 ∧ K1 ≤ C ∧
              ∀ t : ℝ, 0 ≤ t → μ {ω | t ≤ |X ω|} ≤ ENNReal.ofReal (2 * Real.exp (-t / K1))) ∧
        
        ((∀ t : ℝ, 0 ≤ t → μ {ω | t ≤ |X ω|} ≤ ENNReal.ofReal (2 * Real.exp (-t)))
          → ∃ K3 : ℝ, 0 < K3 ∧ K3 ≤ C ∧
              ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 / K3 →
                ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * |X ω|)) ∂μ ≤
                  ENNReal.ofReal (Real.exp (K3 * lam))) ∧
        
        ((∃ K3 : ℝ, 0 < K3 ∧
              ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 / K3 →
                ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * |X ω|)) ∂μ ≤
                  ENNReal.ofReal (Real.exp (K3 * lam)))
          → ∃ K1 : ℝ, 0 < K1 ∧ K1 ≤ C ∧
              ∀ t : ℝ, 0 ≤ t → μ {ω | t ≤ |X ω|} ≤ ENNReal.ofReal (2 * Real.exp (-t / K1))) ∧
        
        ((∀ t : ℝ, 0 ≤ t → μ {ω | t ≤ |X ω|} ≤ ENNReal.ofReal (2 * Real.exp (-t)))
          → ∃ K4 : ℝ, 0 < K4 ∧ K4 ≤ C ∧
              ∫⁻ ω, ENNReal.ofReal (Real.exp (|X ω| / K4)) ∂μ ≤ 2) ∧
        
        ((∃ K4 : ℝ, 0 < K4 ∧
              ∫⁻ ω, ENNReal.ofReal (Real.exp (|X ω| / K4)) ∂μ ≤ 2)
          → ∃ K1 : ℝ, 0 < K1 ∧ K1 ≤ C ∧
              ∀ t : ℝ, 0 ≤ t → μ {ω | t ≤ |X ω|} ≤ ENNReal.ofReal (2 * Real.exp (-t / K1))) ∧
        
        ((∃ K2 : ℝ, 1 ≤ K2 ∧
              ∀ r : ℝ, 1 ≤ r → LqNorm X r μ ≤ ENNReal.ofReal (K2 * r))
          → ∃ K3 : ℝ, 0 < K3 ∧ K3 ≤ C ∧
              ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 / K3 →
                ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * |X ω|)) ∂μ ≤
                  ENNReal.ofReal (Real.exp (K3 * lam))) ∧
        
        ((∃ K3 : ℝ, 0 < K3 ∧
              ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 / K3 →
                ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * |X ω|)) ∂μ ≤
                  ENNReal.ofReal (Real.exp (K3 * lam)))
          → ∃ K2 : ℝ, 1 ≤ K2 ∧ K2 ≤ C ∧
              ∀ r : ℝ, 1 ≤ r → LqNorm X r μ ≤ ENNReal.ofReal (K2 * r)) ∧
        
        ((∃ K2 : ℝ, 1 ≤ K2 ∧
              ∀ r : ℝ, 1 ≤ r → LqNorm X r μ ≤ ENNReal.ofReal (K2 * r))
          → ∃ K4 : ℝ, 0 < K4 ∧ K4 ≤ C ∧
              ∫⁻ ω, ENNReal.ofReal (Real.exp (|X ω| / K4)) ∂μ ≤ 2) ∧
        
        ((∃ K4 : ℝ, 0 < K4 ∧
              ∫⁻ ω, ENNReal.ofReal (Real.exp (|X ω| / K4)) ∂μ ≤ 2)
          → ∃ K2 : ℝ, 1 ≤ K2 ∧ K2 ≤ C ∧
              ∀ r : ℝ, 1 ≤ r → LqNorm X r μ ≤ ENNReal.ofReal (K2 * r)) ∧
        
        ((∃ K3 : ℝ, 0 < K3 ∧
              ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 / K3 →
                ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * |X ω|)) ∂μ ≤
                  ENNReal.ofReal (Real.exp (K3 * lam)))
          → ∃ K4 : ℝ, 0 < K4 ∧ K4 ≤ C ∧
              ∫⁻ ω, ENNReal.ofReal (Real.exp (|X ω| / K4)) ∂μ ≤ 2) ∧
        
        ((∃ K4 : ℝ, 0 < K4 ∧
              ∫⁻ ω, ENNReal.ofReal (Real.exp (|X ω| / K4)) ∂μ ≤ 2)
          → ∃ K3 : ℝ, 0 < K3 ∧ K3 ≤ C ∧
              ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 / K3 →
                ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * |X ω|)) ∂μ ≤
                  ENNReal.ofReal (Real.exp (K3 * lam))) ∧
        
        (∀ (_hmean : ∫ ω, X ω ∂μ = 0),
          ((∀ t : ℝ, 0 ≤ t → μ {ω | t ≤ |X ω|} ≤ ENNReal.ofReal (2 * Real.exp (-t)))
            → ∃ K5 : ℝ, 0 < K5 ∧ K5 ≤ C ∧
                ∀ lam : ℝ, |lam| ≤ 1 / K5 →
                  ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * X ω)) ∂μ ≤
                    ENNReal.ofReal (Real.exp (K5 ^ 2 * lam ^ 2))) ∧
          ((∃ K5 : ℝ, 0 < K5 ∧
                ∀ lam : ℝ, |lam| ≤ 1 / K5 →
                  ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * X ω)) ∂μ ≤
                    ENNReal.ofReal (Real.exp (K5 ^ 2 * lam ^ 2)))
            → ∃ K1 : ℝ, 0 < K1 ∧ K1 ≤ C ∧
                ∀ t : ℝ, 0 ≤ t → μ {ω | t ≤ |X ω|} ≤ ENNReal.ofReal (2 * Real.exp (-t / K1))))))))
axiom ext_model_2 : (open MeasureTheory ProbabilityTheory Filter in (open scoped ENNReal Topology BigOperators in (open Statlib.Imported in (∃ C : ℝ, 0 < C ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : Ω → ℝ) (hX : Measurable X),
        
        ((∀ t : ℝ, 0 ≤ t → μ {ω | t ≤ |X ω|} ≤ ENNReal.ofReal (2 * Real.exp (-t)))
          → ∃ K2 : ℝ, 0 < K2 ∧ K2 ≤ C ∧
              ∀ r : ℝ, 1 ≤ r → LqNorm X r μ ≤ ENNReal.ofReal (K2 * r)) ∧
        
        ((∃ K2 : ℝ, 1 ≤ K2 ∧
              ∀ r : ℝ, 1 ≤ r → LqNorm X r μ ≤ ENNReal.ofReal (K2 * r))
          → ∃ K1 : ℝ, 0 < K1 ∧ K1 ≤ C ∧
              ∀ t : ℝ, 0 ≤ t → μ {ω | t ≤ |X ω|} ≤ ENNReal.ofReal (2 * Real.exp (-t / K1))) ∧
        
        ((∀ t : ℝ, 0 ≤ t → μ {ω | t ≤ |X ω|} ≤ ENNReal.ofReal (2 * Real.exp (-t)))
          → ∃ K3 : ℝ, 0 < K3 ∧ K3 ≤ C ∧
              ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 / K3 →
                ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * |X ω|)) ∂μ ≤
                  ENNReal.ofReal (Real.exp (K3 * lam))) ∧
        
        ((∃ K3 : ℝ, 0 < K3 ∧
              ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 / K3 →
                ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * |X ω|)) ∂μ ≤
                  ENNReal.ofReal (Real.exp (K3 * lam)))
          → ∃ K1 : ℝ, 0 < K1 ∧ K1 ≤ C ∧
              ∀ t : ℝ, 0 ≤ t → μ {ω | t ≤ |X ω|} ≤ ENNReal.ofReal (2 * Real.exp (-t / K1))) ∧
        
        ((∀ t : ℝ, 0 ≤ t → μ {ω | t ≤ |X ω|} ≤ ENNReal.ofReal (2 * Real.exp (-t)))
          → ∃ K4 : ℝ, 0 < K4 ∧ K4 ≤ C ∧
              ∫⁻ ω, ENNReal.ofReal (Real.exp (|X ω| / K4)) ∂μ ≤ 2) ∧
        
        ((∃ K4 : ℝ, 0 < K4 ∧
              ∫⁻ ω, ENNReal.ofReal (Real.exp (|X ω| / K4)) ∂μ ≤ 2)
          → ∃ K1 : ℝ, 0 < K1 ∧ K1 ≤ C ∧
              ∀ t : ℝ, 0 ≤ t → μ {ω | t ≤ |X ω|} ≤ ENNReal.ofReal (2 * Real.exp (-t / K1))) ∧
        
        ((∃ K2 : ℝ, 1 ≤ K2 ∧
              ∀ r : ℝ, 1 ≤ r → LqNorm X r μ ≤ ENNReal.ofReal (K2 * r))
          → ∃ K3 : ℝ, 0 < K3 ∧ K3 ≤ C ∧
              ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 / K3 →
                ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * |X ω|)) ∂μ ≤
                  ENNReal.ofReal (Real.exp (K3 * lam))) ∧
        
        ((∃ K3 : ℝ, 0 < K3 ∧
              ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 / K3 →
                ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * |X ω|)) ∂μ ≤
                  ENNReal.ofReal (Real.exp (K3 * lam)))
          → ∃ K2 : ℝ, 1 ≤ K2 ∧ K2 ≤ C ∧
              ∀ r : ℝ, 1 ≤ r → LqNorm X r μ ≤ ENNReal.ofReal (K2 * r)) ∧
        
        ((∃ K2 : ℝ, 1 ≤ K2 ∧
              ∀ r : ℝ, 1 ≤ r → LqNorm X r μ ≤ ENNReal.ofReal (K2 * r))
          → ∃ K4 : ℝ, 0 < K4 ∧ K4 ≤ C ∧
              ∫⁻ ω, ENNReal.ofReal (Real.exp (|X ω| / K4)) ∂μ ≤ 2) ∧
        
        ((∃ K4 : ℝ, 0 < K4 ∧
              ∫⁻ ω, ENNReal.ofReal (Real.exp (|X ω| / K4)) ∂μ ≤ 2)
          → ∃ K2 : ℝ, 1 ≤ K2 ∧ K2 ≤ C ∧
              ∀ r : ℝ, 1 ≤ r → LqNorm X r μ ≤ ENNReal.ofReal (K2 * r)) ∧
        
        ((∃ K3 : ℝ, 0 < K3 ∧
              ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 / K3 →
                ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * |X ω|)) ∂μ ≤
                  ENNReal.ofReal (Real.exp (K3 * lam)))
          → ∃ K4 : ℝ, 0 < K4 ∧ K4 ≤ C ∧
              ∫⁻ ω, ENNReal.ofReal (Real.exp (|X ω| / K4)) ∂μ ≤ 2) ∧
        
        ((∃ K4 : ℝ, 0 < K4 ∧
              ∫⁻ ω, ENNReal.ofReal (Real.exp (|X ω| / K4)) ∂μ ≤ 2)
          → ∃ K3 : ℝ, 0 < K3 ∧ K3 ≤ C ∧
              ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 / K3 →
                ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * |X ω|)) ∂μ ≤
                  ENNReal.ofReal (Real.exp (K3 * lam))) ∧
        
        (∀ (_hmean : ∫ ω, X ω ∂μ = 0),
          ((∀ t : ℝ, 0 ≤ t → μ {ω | t ≤ |X ω|} ≤ ENNReal.ofReal (2 * Real.exp (-t)))
            → ∃ K5 : ℝ, 0 < K5 ∧ K5 ≤ C ∧
                ∀ lam : ℝ, |lam| ≤ 1 / K5 →
                  ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * X ω)) ∂μ ≤
                    ENNReal.ofReal (Real.exp (K5 ^ 2 * lam ^ 2))) ∧
          ((∃ K5 : ℝ, 0 < K5 ∧
                ∀ lam : ℝ, |lam| ≤ 1 / K5 →
                  ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * X ω)) ∂μ ≤
                    ENNReal.ofReal (Real.exp (K5 ^ 2 * lam ^ 2)))
            → ∃ K1 : ℝ, 0 < K1 ∧ K1 ≤ C ∧
                ∀ t : ℝ, 0 ≤ t → μ {ω | t ≤ |X ω|} ≤ ENNReal.ofReal (2 * Real.exp (-t / K1))))))))

