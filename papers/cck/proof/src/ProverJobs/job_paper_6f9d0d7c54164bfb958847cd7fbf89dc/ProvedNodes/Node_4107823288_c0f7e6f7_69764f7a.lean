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
theorem statopia_math_node_4107823288_c0f7e6f7 : ∀ (p : ℕ) (hp : 0 < p) (z : EuclideanSpace ℝ (Fin p)) (β : ℝ) (hβ : 0 < β),
    Statlib.StatFoundation.Convergence.smoothMax β z ≤
      Statlib.StatFoundation.Vocabulary.maxCoord z + β⁻¹ * Real.log (p : ℝ) := by
  /- @proof-region region.target-node.session.4cbddffc19cc3bb8 begin -/
  intro p hp z β hβ
  have h := (Statlib.StatFoundation.Convergence.smoothMax_bounds_max_log_card p hp β hβ z).2
  simpa [div_eq_mul_inv, mul_comm] using h
  /- @proof-region region.target-node.session.4cbddffc19cc3bb8 end -/

end Statlib.Imported

