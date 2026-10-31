import Statlib.StatFoundation.Statistics.Asymptotic.ScoreCLT
import Statlib.StatFoundation.Convergence.Resampling.GaussianMaxComparison
import Statlib.StatFoundation.Convergence.AnalysisTools.GaussianMaxAnticoncentration
import Statlib.StatFoundation.Statistics.Asymptotic.LAN
import Statlib.StatFoundation.Convergence.AnalysisTools.SmoothMax
import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.Base

namespace PaperProofTasks.job_paper_de3065fb922748188f3a0354eba90ed9

-- External DAG node: ext_model_1 (AXIOM)
example : Prop := (open MeasureTheory ProbabilityTheory in (open scoped ENNReal BigOperators in (∀ {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℕ) (hp : 1 ≤ p)
    (W : Ω → Fin p → ℝ) (hW : Measurable W)
    (hGauss : ProbabilityTheory.IsGaussian (μ.map (fun ω => fun j : Fin p => W ω j)))
    (hMean : ∀ j : Fin p, Integrable (fun ω => W ω j) μ)
    (hVar : ∀ j : Fin p, ∫ ω, (W ω j) ^ 2 ∂μ - (∫ ω, W ω j ∂μ) ^ 2 = 1)
    (hCorr : ∀ j k : Fin p, j ≠ k →
      (∫ ω, (W ω j - ∫ ω, W ω j ∂μ) * (W ω k - ∫ ω, W ω k ∂μ) ∂μ) < 1)
    (κ : Fin p → ProbabilityTheory.Kernel ℝ (Fin p → ℝ))
    [∀ j : Fin p, ProbabilityTheory.IsMarkovKernel (κ j)]
    (hrcd : ∀ j : Fin p,
      MeasureTheory.Measure.map
          (fun q : ℝ × (Fin p → ℝ) => Function.update q.2 j q.1)
          (MeasureTheory.Measure.compProd (μ.map (fun ω => W ω j)) (κ j)) =
        (μ.map (fun ω => fun k : Fin p => W ω k))),
    (μ.map (fun ω => ⨆ j : Fin p, W ω j)) ≪ volume ∧
      ∃ (f : ℝ → ℝ),
        Measurable f ∧
          (∀ x : ℝ, f x =
            (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2) *
              ∑ j : Fin p,
                Real.exp ((∫ ω, W ω j ∂μ) * x - (∫ ω, W ω j ∂μ) ^ 2 / 2) *
                  (κ j x {z : Fin p → ℝ | ∀ k : Fin p, k ≠ j → z k ≤ x}).toReal) ∧
          (∀ (s : Set ℝ), (μ.map (fun ω => ⨆ j : Fin p, W ω j)) s =
            ∫⁻ x in s, ENNReal.ofReal (f x) ∂volume))))
axiom ext_model_1 : (open MeasureTheory ProbabilityTheory in (open scoped ENNReal BigOperators in (∀ {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℕ) (hp : 1 ≤ p)
    (W : Ω → Fin p → ℝ) (hW : Measurable W)
    (hGauss : ProbabilityTheory.IsGaussian (μ.map (fun ω => fun j : Fin p => W ω j)))
    (hMean : ∀ j : Fin p, Integrable (fun ω => W ω j) μ)
    (hVar : ∀ j : Fin p, ∫ ω, (W ω j) ^ 2 ∂μ - (∫ ω, W ω j ∂μ) ^ 2 = 1)
    (hCorr : ∀ j k : Fin p, j ≠ k →
      (∫ ω, (W ω j - ∫ ω, W ω j ∂μ) * (W ω k - ∫ ω, W ω k ∂μ) ∂μ) < 1)
    (κ : Fin p → ProbabilityTheory.Kernel ℝ (Fin p → ℝ))
    [∀ j : Fin p, ProbabilityTheory.IsMarkovKernel (κ j)]
    (hrcd : ∀ j : Fin p,
      MeasureTheory.Measure.map
          (fun q : ℝ × (Fin p → ℝ) => Function.update q.2 j q.1)
          (MeasureTheory.Measure.compProd (μ.map (fun ω => W ω j)) (κ j)) =
        (μ.map (fun ω => fun k : Fin p => W ω k))),
    (μ.map (fun ω => ⨆ j : Fin p, W ω j)) ≪ volume ∧
      ∃ (f : ℝ → ℝ),
        Measurable f ∧
          (∀ x : ℝ, f x =
            (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2) *
              ∑ j : Fin p,
                Real.exp ((∫ ω, W ω j ∂μ) * x - (∫ ω, W ω j ∂μ) ^ 2 / 2) *
                  (κ j x {z : Fin p → ℝ | ∀ k : Fin p, k ≠ j → z k ≤ x}).toReal) ∧
          (∀ (s : Set ℝ), (μ.map (fun ω => ⨆ j : Fin p, W ω j)) s =
            ∫⁻ x in s, ENNReal.ofReal (f x) ∂volume))))

