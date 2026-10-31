import ProverJobs.job_paper_53e951f48c854f4db91e6ecda697ee2b.Vocabulary
import ProverJobs.job_paper_53e951f48c854f4db91e6ecda697ee2b.Base

namespace PaperProofTasks.job_paper_53e951f48c854f4db91e6ecda697ee2b

open Filter Topology MeasureTheory
open scoped Topology ENNReal
open _root_.PaperProofTasks.job_paper_53e951f48c854f4db91e6ecda697ee2b.Statlib.Imported

noncomputable section
open Filter Topology MeasureTheory
open scoped Topology ENNReal
namespace Statlib.Imported


set_option autoImplicit false in
theorem statopia_math_node_1841802883_50746d93 : ∀ (d : ℕ) (U : HMCState d → ℝ) (ε : ℝ) (L : ℕ)
    (x0 p0 : HMCState d),
    hmcAcceptance U ε L x0 p0 =
      min 1
        (Real.exp (U x0 - U (leapfrogPosition U ε L x0 p0) + (1 / 2) * ‖p0‖ ^ 2 -
          (1 / 2) * ‖leapfrogMomentum U ε L x0 p0‖ ^ 2)) ∧
      0 ≤ hmcAcceptance U ε L x0 p0 ∧ hmcAcceptance U ε L x0 p0 ≤ 1 := by
  /- @proof-region region.target-node.session.7da414251fbfbfc9 begin -/
  intro d U ε L x0 p0
  have harg :
      (hmcDensity U (leapfrogPosition U ε L x0 p0) / hmcDensity U x0) *
          Real.exp (kineticEnergy p0 - kineticEnergy (leapfrogMomentum U ε L x0 p0)) =
        Real.exp
          (U x0 - U (leapfrogPosition U ε L x0 p0) + (1 / 2) * ‖p0‖ ^ 2 -
            (1 / 2) * ‖leapfrogMomentum U ε L x0 p0‖ ^ 2) := by
    unfold hmcDensity kineticEnergy
    rw [← Real.exp_sub, ← Real.exp_add]
    congr 1
    ring
  have hmain :
      hmcAcceptance U ε L x0 p0 =
        min 1
          (Real.exp
            (U x0 - U (leapfrogPosition U ε L x0 p0) + (1 / 2) * ‖p0‖ ^ 2 -
              (1 / 2) * ‖leapfrogMomentum U ε L x0 p0‖ ^ 2)) := by
    unfold hmcAcceptance
    rw [harg]
  refine ⟨hmain, ?_, ?_⟩
  · rw [hmain]
    exact le_min zero_le_one (Real.exp_pos _).le
  · rw [hmain]
    exact min_le_left _ _
  /- @proof-region region.target-node.session.7da414251fbfbfc9 end -/

end Statlib.Imported
end

