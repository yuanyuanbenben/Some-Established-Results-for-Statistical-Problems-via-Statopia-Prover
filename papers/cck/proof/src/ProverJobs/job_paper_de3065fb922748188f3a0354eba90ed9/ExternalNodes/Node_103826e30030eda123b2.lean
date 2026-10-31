import Statlib.StatFoundation.Statistics.Asymptotic.ScoreCLT
import Statlib.StatFoundation.Convergence.Resampling.GaussianMaxComparison
import Statlib.StatFoundation.Convergence.AnalysisTools.GaussianMaxAnticoncentration
import Statlib.StatFoundation.Statistics.Asymptotic.LAN
import Statlib.StatFoundation.Convergence.AnalysisTools.SmoothMax
import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.Base

namespace PaperProofTasks.job_paper_de3065fb922748188f3a0354eba90ed9

-- External DAG node: ext_model_4 (AXIOM)
example : Prop := (open MeasureTheory in (∀ (z : ℝ) (hz : 0 < z),
    z ≤ ProbabilityTheory.gaussianPDFReal 0 1 z / (1 - ∫ u in Set.Iic z, ProbabilityTheory.gaussianPDFReal 0 1 u)
      ∧ ProbabilityTheory.gaussianPDFReal 0 1 z / (1 - ∫ u in Set.Iic z, ProbabilityTheory.gaussianPDFReal 0 1 u)
          ≤ z * ((1 + z ^ 2) / z ^ 2)))
axiom ext_model_4 : (open MeasureTheory in (∀ (z : ℝ) (hz : 0 < z),
    z ≤ ProbabilityTheory.gaussianPDFReal 0 1 z / (1 - ∫ u in Set.Iic z, ProbabilityTheory.gaussianPDFReal 0 1 u)
      ∧ ProbabilityTheory.gaussianPDFReal 0 1 z / (1 - ∫ u in Set.Iic z, ProbabilityTheory.gaussianPDFReal 0 1 u)
          ≤ z * ((1 + z ^ 2) / z ^ 2)))

