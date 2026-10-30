import Statlib.StatFoundation.Convergence.AnalysisTools.LevyContinuity
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q05.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q05.Base

open MeasureTheory ProbabilityTheory Filter
open Msc62GroundTruth

open MeasureTheory ProbabilityTheory Filter
namespace Msc62GroundTruth

set_option autoImplicit false in
theorem statopia_math_node_3978580173_87945a3a : ∀ (μ ν : ProbabilityMeasure ℝ)
    (h : ∀ t : ℝ, charFun (μ : Measure ℝ) t = charFun (ν : Measure ℝ) t),
    μ = ν := by
  /- @proof-region region.target-node.session.c4157d9e4469221a begin -/
  intro μ ν h
  exact Statlib.StatFoundation.Convergence.probMeasure_eq_of_charFun_eq h
  /- @proof-region region.target-node.session.c4157d9e4469221a end -/

end Msc62GroundTruth
