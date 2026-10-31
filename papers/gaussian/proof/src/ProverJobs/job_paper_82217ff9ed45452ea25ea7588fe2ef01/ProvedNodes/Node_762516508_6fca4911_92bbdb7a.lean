import ProverJobs.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Vocabulary
import ProverJobs.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Base

namespace PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators
open _root_.PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Statlib.Imported
open _root_.PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Statlib.Imported.Model

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators
namespace Statlib.Imported

noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_762516508_6fca4911 : ∀ (a c0 alpha cvar ccirc eps0 Ccor : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (M : Model Ω μ a) (hM : Model.Assumptions M c0 alpha cvar ccirc eps0 Ccor)
    (n : ℕ) (hn : M.p n ≤ M.kIdx n),
    M.In n = 0 ∧ M.IIIn n = 0 := by
  /- @proof-region region.target-node.session.e8c6bfc43091a868 begin -/
  intro _ _ _ _ _ _ _ _ _ _ _ M _ n hn
  have dK_self : ∀ P : Measure ℝ, dK P P = 0 := by
    intro P
    unfold dK
    have hfun : (fun t : ℝ => |(P (Set.Iic t)).toReal - (P (Set.Iic t)).toReal|)
        = (fun _ : ℝ => (0 : ℝ)) := by
      funext t
      simp
    rw [hfun, sSup_range]
    simpa using Real.iSup_const_zero
  have hk_le : M.kIdx n ≤ M.p n := by
    unfold kIdx
    exact Nat.ceil_le.mpr (min_le_right _ _)
  have hk : M.kIdx n = M.p n := le_antisymm hk_le hn
  constructor
  · unfold In
    rw [hk]
    exact dK_self _
  · unfold IIIn
    rw [hk]
    exact dK_self _
  /- @proof-region region.target-node.session.e8c6bfc43091a868 end -/

end
end Statlib.Imported

