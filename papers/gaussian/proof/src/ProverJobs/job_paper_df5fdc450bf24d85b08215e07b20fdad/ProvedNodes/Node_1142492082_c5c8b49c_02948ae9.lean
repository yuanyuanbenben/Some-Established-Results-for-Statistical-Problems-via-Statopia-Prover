import ProverJobs.job_paper_df5fdc450bf24d85b08215e07b20fdad.Vocabulary
import ProverJobs.job_paper_df5fdc450bf24d85b08215e07b20fdad.Base

namespace PaperProofTasks.job_paper_df5fdc450bf24d85b08215e07b20fdad

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology BigOperators
open _root_.PaperProofTasks.job_paper_df5fdc450bf24d85b08215e07b20fdad.Statlib.Imported

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology BigOperators
namespace Statlib.Imported


set_option autoImplicit false in
theorem statopia_math_node_1142492082_c5c8b49c : ∀ (n : Type) [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) (hA : A.PosSemidef),
    (Matrix.PosSemidef.sqrt hA).IsHermitian ∧
      Matrix.PosSemidef.sqrt hA * Matrix.PosSemidef.sqrt hA = A := by
  /- @proof-region region.target-node.session.81193901c298c536 begin -/
  intro n _ _ A hA
  have hofReal : ∀ r : ℝ, RCLike.ofReal r = r := fun r => by simp
  set u : Matrix.unitaryGroup n ℝ := hA.isHermitian.eigenvectorUnitary with hu
  set lam : n → ℝ := hA.isHermitian.eigenvalues with hlam
  set D : Matrix n n ℝ := Matrix.diagonal (fun i => RCLike.ofReal (Real.sqrt (lam i))) with hD
  have hsqrt : Matrix.PosSemidef.sqrt hA
      = (u : Matrix n n ℝ) * Matrix.diagonal (fun i => RCLike.ofReal (Real.sqrt (lam i))) * star (u : Matrix n n ℝ) := by
    simp only [Matrix.PosSemidef.sqrt, ← hu, ← hlam]
    rfl
  rw [hsqrt, ← hD]
  refine ⟨?_, ?_⟩
  · have hb : star (u : Matrix n n ℝ) = (u : Matrix n n ℝ).conjTranspose := rfl
    rw [hb]
    exact Matrix.isHermitian_mul_mul_conjTranspose (B := (u : Matrix n n ℝ)) (by
      rw [hD]
      exact Matrix.isHermitian_diagonal _)
  · have hmm : ((u : Matrix n n ℝ) * D * star (u : Matrix n n ℝ)) * ((u : Matrix n n ℝ) * D * star (u : Matrix n n ℝ))
        = (u : Matrix n n ℝ) * (D * D) * star (u : Matrix n n ℝ) := by
      calc ((u : Matrix n n ℝ) * D * star (u : Matrix n n ℝ)) * ((u : Matrix n n ℝ) * D * star (u : Matrix n n ℝ))
          = (u : Matrix n n ℝ) * D * (star (u : Matrix n n ℝ) * (u : Matrix n n ℝ)) * D * star (u : Matrix n n ℝ) := by noncomm_ring
        _ = (u : Matrix n n ℝ) * D * 1 * D * star (u : Matrix n n ℝ) := by rw [Matrix.UnitaryGroup.star_mul_self u]
        _ = (u : Matrix n n ℝ) * (D * D) * star (u : Matrix n n ℝ) := by noncomm_ring
    have hDD : D * D = Matrix.diagonal (fun i => RCLike.ofReal (lam i)) := by
      rw [hD, Matrix.diagonal_mul_diagonal]
      congr 1 with i
      have hnn : 0 ≤ lam i := by simpa only [hlam] using hA.eigenvalues_nonneg i
      simp only [hofReal, Real.mul_self_sqrt hnn]
    have hspec : A = (u : Matrix n n ℝ) * Matrix.diagonal (fun i => RCLike.ofReal (lam i)) * star (u : Matrix n n ℝ) := by
      have h := Matrix.IsHermitian.spectral_theorem hA.isHermitian
      rw [← hu, ← hlam, Unitary.conjStarAlgAut_apply] at h
      simpa only [Function.comp] using h
    rw [hmm, hDD]
    exact hspec.symm
  /- @proof-region region.target-node.session.81193901c298c536 end -/

end Statlib.Imported

