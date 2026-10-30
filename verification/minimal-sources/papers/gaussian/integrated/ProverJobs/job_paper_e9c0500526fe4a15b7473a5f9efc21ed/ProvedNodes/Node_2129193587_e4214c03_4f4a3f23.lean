import ProverJobs.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Vocabulary
import ProverJobs.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Base

namespace PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed

open _root_.PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
universe u₀ u₁

set_option autoImplicit false in
theorem statopia_math_node_2129193587_e4214c03 : ∀ (pn : ℕ) (S : Matrix (Fin pn) (Fin pn) ℝ)
    (hS : S.PosSemidef),
    Matrix.transpose (Matrix.PosSemidef.sqrt hS) = Matrix.PosSemidef.sqrt hS := by
  /- @proof-region region.target-node.session.a72ea9d80db238b8 begin -/
  intro pn S hS
  have hstar : ∀ M : Matrix (Fin pn) (Fin pn) ℝ, star M = M.transpose :=
    fun M => (Matrix.star_eq_conjTranspose M).trans (Matrix.conjTranspose_eq_transpose_of_trivial M)
  unfold Matrix.PosSemidef.sqrt
  simp only [hstar, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc,
    Matrix.diagonal_transpose]
  /- @proof-region region.target-node.session.a72ea9d80db238b8 end -/

end
end Statlib.Imported

