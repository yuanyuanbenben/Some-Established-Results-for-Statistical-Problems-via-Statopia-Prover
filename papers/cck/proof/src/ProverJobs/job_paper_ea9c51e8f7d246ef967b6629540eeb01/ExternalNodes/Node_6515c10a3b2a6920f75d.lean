import Statlib.StatFoundation.Statistics.Asymptotic.ScoreCLT
import Statlib.StatFoundation.Convergence.Resampling.GaussianMaxComparison
import Statlib.StatFoundation.Convergence.AnalysisTools.GaussianMaxAnticoncentration
import Statlib.StatFoundation.Statistics.Asymptotic.LAN
import Statlib.StatFoundation.Convergence.AnalysisTools.SmoothMax
import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import ProverJobs.job_paper_ea9c51e8f7d246ef967b6629540eeb01.Base

namespace PaperProofTasks.job_paper_ea9c51e8f7d246ef967b6629540eeb01

-- External DAG node: ext_model_1 (AXIOM)
example : Prop := (open MeasureTheory ProbabilityTheory in (∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℕ) (hp : 0 < p)
    (W : Ω → Fin p → ℝ)
    (SigmaW : Matrix (Fin p) (Fin p) ℝ)
    (hW : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector μ W SigmaW)
    (f : (Fin p → ℝ) → ℝ)
    (hf : ContDiff ℝ 1 (fun z : EuclideanSpace ℝ (Fin p) => f (WithLp.ofLp z)))
    (hint : ∀ j : Fin p,
      Integrable (fun ω => |deriv (fun t : ℝ => f (Function.update (W ω) j t)) (W ω j)|) μ),
    ∀ j : Fin p,
      ∫ ω, W ω j * f (W ω) ∂μ =
        ∑ k : Fin p, (∫ ω, W ω j * W ω k ∂μ)
          * ∫ ω, deriv (fun t : ℝ => f (Function.update (W ω) k t)) (W ω k) ∂μ))
axiom ext_model_1 : (open MeasureTheory ProbabilityTheory in (∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℕ) (hp : 0 < p)
    (W : Ω → Fin p → ℝ)
    (SigmaW : Matrix (Fin p) (Fin p) ℝ)
    (hW : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector μ W SigmaW)
    (f : (Fin p → ℝ) → ℝ)
    (hf : ContDiff ℝ 1 (fun z : EuclideanSpace ℝ (Fin p) => f (WithLp.ofLp z)))
    (hint : ∀ j : Fin p,
      Integrable (fun ω => |deriv (fun t : ℝ => f (Function.update (W ω) j t)) (W ω j)|) μ),
    ∀ j : Fin p,
      ∫ ω, W ω j * f (W ω) ∂μ =
        ∑ k : Fin p, (∫ ω, W ω j * W ω k ∂μ)
          * ∫ ω, deriv (fun t : ℝ => f (Function.update (W ω) k t)) (W ω k) ∂μ))

