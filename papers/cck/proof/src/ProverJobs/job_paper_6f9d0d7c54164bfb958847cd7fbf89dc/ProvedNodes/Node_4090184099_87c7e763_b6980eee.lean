import Statlib.StatFoundation.Statistics.Asymptotic.ScoreCLT
import Statlib.StatFoundation.Convergence.Resampling.GaussianMaxComparison
import Statlib.StatFoundation.Convergence.AnalysisTools.GaussianMaxAnticoncentration
import Statlib.StatFoundation.Statistics.Asymptotic.LAN
import Statlib.StatFoundation.Convergence.AnalysisTools.SmoothMax
import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import ProverJobs.job_paper_6f9d0d7c54164bfb958847cd7fbf89dc.Vocabulary
import ProverJobs.job_paper_6f9d0d7c54164bfb958847cd7fbf89dc.Base

namespace PaperProofTasks.job_paper_6f9d0d7c54164bfb958847cd7fbf89dc

open _root_.PaperProofTasks.job_paper_6f9d0d7c54164bfb958847cd7fbf89dc.Statlib.Imported

namespace Statlib.Imported


set_option autoImplicit false in
theorem statopia_math_node_4090184099_87c7e763 : ∀ (p : ℕ) (hp : 0 < p) (z : EuclideanSpace ℝ (Fin p)) (β : ℝ) (hβ : 0 < β),
    Statlib.StatFoundation.Vocabulary.maxCoord z ≤
      Statlib.StatFoundation.Convergence.smoothMax β z := by
  /- @proof-region region.target-node.session.dcb560c58160ee89 begin -/
  intro p hp z β hβ
  exact (Statlib.StatFoundation.Convergence.smoothMax_bounds_max_log_card p hp β hβ z).1
  /- @proof-region region.target-node.session.dcb560c58160ee89 end -/

end Statlib.Imported

