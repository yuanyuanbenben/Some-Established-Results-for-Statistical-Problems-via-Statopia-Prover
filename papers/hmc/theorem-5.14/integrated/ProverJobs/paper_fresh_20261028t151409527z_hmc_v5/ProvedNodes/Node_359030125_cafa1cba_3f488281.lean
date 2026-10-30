import ProverJobs.paper_fresh_20261028t151409527z_hmc_v5.Vocabulary
import ProverJobs.paper_fresh_20261028t151409527z_hmc_v5.Base

namespace PaperProofTasks.paper_fresh_20261028t151409527z_hmc_v5

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal
open _root_.PaperProofTasks.paper_fresh_20261028t151409527z_hmc_v5.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal
namespace Statlib.Imported
open _root_.Statlib

set_option autoImplicit false in
theorem statopia_math_node_359030125_cafa1cba : ∀ (d : ℕ)
    (U : EuclideanSpace ℝ (Fin d) → ℝ) (hU : Differentiable ℝ U),
    Measurable (gradient U) := by
  /- @proof-region region.target-node.session.4477d707fc0b0354 begin -/
  intro d U hU
  have h : Measurable
      (fun x : EuclideanSpace ℝ (Fin d) =>
        (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm (fderiv ℝ U x)) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm.continuous.measurable.comp
      (measurable_fderiv (𝕜 := ℝ) U)
  simpa only [gradient] using h
  /- @proof-region region.target-node.session.4477d707fc0b0354 end -/

end Statlib.Imported
end

