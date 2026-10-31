import Statlib.StatFoundation.Statistics.Asymptotic.ScoreCLT
import Statlib.StatFoundation.Convergence.Resampling.GaussianMaxComparison
import Statlib.StatFoundation.Convergence.AnalysisTools.GaussianMaxAnticoncentration
import Statlib.StatFoundation.Statistics.Asymptotic.LAN
import Statlib.StatFoundation.Convergence.AnalysisTools.SmoothMax
import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import ProverJobs.job_paper_6f9d0d7c54164bfb958847cd7fbf89dc.Vocabulary
import ProverJobs.job_paper_6f9d0d7c54164bfb958847cd7fbf89dc.ProvedNodes
import ProverJobs.job_paper_6f9d0d7c54164bfb958847cd7fbf89dc.Base

namespace PaperProofTasks.job_paper_6f9d0d7c54164bfb958847cd7fbf89dc

namespace Statlib.Imported


theorem paper_6f9d0d7c54164bfb958847cd7fbf89dc
    (p : ℕ) (hp : 0 < p) (z : EuclideanSpace ℝ (Fin p)) (β : ℝ) (hβ : 0 < β) :
    0 ≤ Statlib.StatFoundation.Convergence.smoothMax β z -
          Statlib.StatFoundation.Vocabulary.maxCoord z ∧
      Statlib.StatFoundation.Convergence.smoothMax β z -
          Statlib.StatFoundation.Vocabulary.maxCoord z ≤ β⁻¹ * Real.log (p : ℝ)
:= by
  /- @proof-region region.root.9f04c026e740 begin -/
  have h_low : Statlib.StatFoundation.Vocabulary.maxCoord z ≤
      Statlib.StatFoundation.Convergence.smoothMax β z :=
    statopia_math_node_4090184099_87c7e763 p hp z β hβ
  have h_up : Statlib.StatFoundation.Convergence.smoothMax β z ≤
      Statlib.StatFoundation.Vocabulary.maxCoord z + β⁻¹ * Real.log (p : ℝ) :=
    statopia_math_node_4107823288_c0f7e6f7 p hp z β hβ
  constructor <;> linarith
  /- @proof-region region.root.9f04c026e740 end -/

end Statlib.Imported

