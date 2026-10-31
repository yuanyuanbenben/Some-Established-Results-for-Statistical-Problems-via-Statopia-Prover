import Statlib.StatFoundation.Statistics.Asymptotic.ScoreCLT
import Statlib.StatFoundation.Convergence.Resampling.GaussianMaxComparison
import Statlib.StatFoundation.Convergence.AnalysisTools.GaussianMaxAnticoncentration
import Statlib.StatFoundation.Statistics.Asymptotic.LAN
import Statlib.StatFoundation.Convergence.AnalysisTools.SmoothMax
import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import ProverJobs.paper_fresh_20261030t163458307499z_cck_comparison.ExternalNodes.Node_435326d2a13e42d4b5b1
import ProverJobs.paper_fresh_20261030t163458307499z_cck_comparison.Vocabulary
import ProverJobs.paper_fresh_20261030t163458307499z_cck_comparison.ProvedNodes
import ProverJobs.paper_fresh_20261030t163458307499z_cck_comparison.Base

namespace PaperProofTasks.paper_fresh_20261030t163458307499z_cck_comparison

open _root_.PaperProofTasks.paper_fresh_20261030t163458307499z_cck_comparison.Statlib.Imported
open MeasureTheory
open Statlib.StatFoundation.Convergence
namespace Statlib.Imported


theorem Theorem_2_Comparison_of_distributions_second_conclusion_covariance_only_Kolmogorov_bound_Cprime_Delta_1_3_max_1_log_p_De :
    ∃ Cprime : ℝ → ℝ → ℝ,
      (∀ a b : ℝ, 0 < a → 0 < Cprime a b) ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (p : ℕ) (hp : 2 ≤ p)
        (SigmaY : Matrix (Fin p) (Fin p) ℝ) (Y : Ω → Fin p → ℝ),
          Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector μ Y SigmaY →
          SigmaY.IsSymm →
          (∀ j : Fin p, 0 < SigmaY j j) →
          ∀ (SigmaX : Matrix (Fin p) (Fin p) ℝ) (X : Ω → Fin p → ℝ),
            Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector μ X SigmaX →
            SigmaX.IsSymm →
            ∀ x : ℝ,
              |(μ {ω | ∀ j : Fin p, X ω j ≤ x}).toReal
                  - (μ {ω | ∀ j : Fin p, Y ω j ≤ x}).toReal| ≤
                Cprime (covDiagMin SigmaY) (covDiagMax SigmaY) *
                  (if covEntryMaxDiff SigmaX SigmaY = 0 then 0
                   else (covEntryMaxDiff SigmaX SigmaY) ^ ((1 : ℝ) / 3) *
                     (max 1 (Real.log ((p : ℝ) / covEntryMaxDiff SigmaX SigmaY))) ^
                                             ((2 : ℝ) / 3))
:= by
  /- @proof-region region.root.f2c2461304f6 begin -/ exact cck_covariance_comparison_uniform /- @proof-region region.root.f2c2461304f6 end -/

end Statlib.Imported

-- Paper root revision 169eb676-0a8c-4e43-998e-1928f8a3cb31

