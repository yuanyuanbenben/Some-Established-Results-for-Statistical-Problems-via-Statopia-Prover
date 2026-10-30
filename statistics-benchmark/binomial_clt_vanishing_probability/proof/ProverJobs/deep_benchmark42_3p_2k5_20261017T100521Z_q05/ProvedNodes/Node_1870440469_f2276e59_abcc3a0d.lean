import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q05.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q05.Base

open MeasureTheory ProbabilityTheory Filter
open Msc62GroundTruth

open MeasureTheory ProbabilityTheory Filter
namespace Msc62GroundTruth

set_option autoImplicit false in
theorem statopia_math_node_1870440469_f2276e59 : ∀ (t : ℝ),
    charFun (gaussianReal 0 1) t = Complex.exp ((-(t ^ 2) / 2 : ℝ) : ℂ) := by
  /- @proof-region region.target-node.session.3c718d96e970436a begin -/
  intro t
  rw [Statlib.StatFoundation.Convergence.BerryEsseen.charFun_gaussianReal_standard t]
  congr 1
  push_cast
  ring
  /- @proof-region region.target-node.session.3c718d96e970436a end -/

end Msc62GroundTruth
