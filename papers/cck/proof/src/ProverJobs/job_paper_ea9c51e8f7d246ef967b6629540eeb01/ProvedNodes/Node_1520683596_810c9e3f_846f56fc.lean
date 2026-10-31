import Statlib.StatFoundation.Statistics.Asymptotic.ScoreCLT
import Statlib.StatFoundation.Convergence.Resampling.GaussianMaxComparison
import Statlib.StatFoundation.Convergence.AnalysisTools.GaussianMaxAnticoncentration
import Statlib.StatFoundation.Statistics.Asymptotic.LAN
import Statlib.StatFoundation.Convergence.AnalysisTools.SmoothMax
import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import ProverJobs.job_paper_ea9c51e8f7d246ef967b6629540eeb01.Vocabulary
import ProverJobs.job_paper_ea9c51e8f7d246ef967b6629540eeb01.Base
import ProverJobs.job_paper_ea9c51e8f7d246ef967b6629540eeb01.ProvedNodes.Node_3051679456_55e9e66b_5acd53a6
import ProverJobs.job_paper_ea9c51e8f7d246ef967b6629540eeb01.ProvedNodes.Node_3490004778_d4b29b90_fa84c02f
import ProverJobs.job_paper_ea9c51e8f7d246ef967b6629540eeb01.ExternalNodes.Node_2f43420c7b66475da0e6

namespace PaperProofTasks.job_paper_ea9c51e8f7d246ef967b6629540eeb01

open _root_.PaperProofTasks.job_paper_ea9c51e8f7d246ef967b6629540eeb01.Statlib.Imported
open MeasureTheory ProbabilityTheory

namespace Statlib.Imported

open MeasureTheory ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_1520683596_810c9e3f : ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℕ) (hp : 0 < p)
    (X Y : Ω → Fin p → ℝ)
    (hX : Measurable X) (hY : Measurable Y)
    (hXint : ∀ j : Fin p, Integrable (fun ω => X ω j) μ)
    (hYint : ∀ j : Fin p, Integrable (fun ω => Y ω j) μ)
    (β : ℝ) (hβ : 0 < β)
    (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g)
    (hg_bdd : BddAbove (Set.range fun z : ℝ => |deriv g z|)),
    (∀ t ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt
        (fun s : ℝ =>
          ∫ ω, g (Statlib.StatFoundation.Convergence.smoothMax β
              (WithLp.toLp 2 (fun j : Fin p =>
                Real.sqrt s * X ω j + Real.sqrt (1 - s) * Y ω j))) ∂μ)
        ((1/2 : ℝ) * ∑ j : Fin p,
          ∫ ω, (fderiv ℝ (fun z : Fin p → ℝ =>
                g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 z)))
              (fun j : Fin p => Real.sqrt t * X ω j + Real.sqrt (1 - t) * Y ω j))
            (Pi.single j (1 : ℝ)) *
            (t ^ (-(1/2) : ℝ) * X ω j - (1 - t) ^ (-(1/2) : ℝ) * Y ω j) ∂μ)
        t) ∧
    (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ j : Fin p,
      Integrable
        (fun ω => (fderiv ℝ (fun z : Fin p → ℝ =>
              g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 z)))
            (fun j : Fin p => Real.sqrt t * X ω j + Real.sqrt (1 - t) * Y ω j))
          (Pi.single j (1 : ℝ)) *
          (t ^ (-(1/2) : ℝ) * X ω j - (1 - t) ^ (-(1/2) : ℝ) * Y ω j)) μ) := by
  /- @proof-region region.target-node.session.703709bb289f1561 begin -/
  intro Ω _ μ _ p hp X Y hX hY hXint hYint β hβ g hg hg_bdd
  refine ⟨?_, ?_⟩
  · intro t ht
    exact statopia_math_node_3051679456_55e9e66b μ p hp X Y hX hY hXint hYint β hβ g hg hg_bdd t ht
  · intro t ht j
    exact statopia_math_node_3490004778_d4b29b90 μ p hp X Y hX hY hXint hYint β hβ g hg hg_bdd t ht j
  /- @proof-region region.target-node.session.703709bb289f1561 end -/

end Statlib.Imported

