import Statlib.StatFoundation.Statistics.Asymptotic.ScoreCLT
import Statlib.StatFoundation.Convergence.Resampling.GaussianMaxComparison
import Statlib.StatFoundation.Convergence.AnalysisTools.GaussianMaxAnticoncentration
import Statlib.StatFoundation.Statistics.Asymptotic.LAN
import Statlib.StatFoundation.Convergence.AnalysisTools.SmoothMax
import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.Base

namespace PaperProofTasks.job_paper_de3065fb922748188f3a0354eba90ed9

-- External DAG node: ext_model_2 (AXIOM)
example : Prop := (open MeasureTheory ProbabilityTheory in (open scoped ENNReal BigOperators in (∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℕ)
    (W : Ω → Fin (p + 1) → ℝ)
    (hWmeas : ∀ j : Fin (p + 1), Measurable (fun ω => W ω j))
    (hgauss : ∃ (m : Fin (p + 1) → ℝ) (S : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ),
      Measure.map W μ = Statlib.Imported.gaussianVecMeasure m S)
    (hVar : ∀ j : Fin (p + 1), ∫ ω, (W ω j - ∫ ω', W ω' j ∂μ) ^ 2 ∂μ = 1)
    (hMean0 : 0 ≤ ∫ ω, W ω 0 ∂μ),
      Monotone (fun z : ℝ =>
        Real.exp ((∫ ω, W ω 0 ∂μ) * z - (∫ ω, W ω 0 ∂μ) ^ 2 / 2) *
          ((Measure.map (fun ω : Ω => (W ω 0, fun j : Fin p => W ω (Fin.succ j))) μ).condKernel z
            {y : Fin p → ℝ | ∀ j : Fin p, y j ≤ z}).toReal))))
axiom ExternalRevision_58f8b9f8d26309be8849b0e8c1d4cafebaef77ff60fcf2fda372bf76bd1fc229.citation : (open MeasureTheory ProbabilityTheory in (open scoped ENNReal BigOperators in (∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℕ)
    (W : Ω → Fin (p + 1) → ℝ)
    (hWmeas : ∀ j : Fin (p + 1), Measurable (fun ω => W ω j))
    (hgauss : ∃ (m : Fin (p + 1) → ℝ) (S : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ),
      Measure.map W μ = Statlib.Imported.gaussianVecMeasure m S)
    (hVar : ∀ j : Fin (p + 1), ∫ ω, (W ω j - ∫ ω', W ω' j ∂μ) ^ 2 ∂μ = 1)
    (hMean0 : 0 ≤ ∫ ω, W ω 0 ∂μ),
      Monotone (fun z : ℝ =>
        Real.exp ((∫ ω, W ω 0 ∂μ) * z - (∫ ω, W ω 0 ∂μ) ^ 2 / 2) *
          ((Measure.map (fun ω : Ω => (W ω 0, fun j : Fin p => W ω (Fin.succ j))) μ).condKernel z
            {y : Fin p → ℝ | ∀ j : Fin p, y j ≤ z}).toReal))))

