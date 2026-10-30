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
theorem statopia_math_node_2405363399_2b807e30 : ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℝ)
    (hA : A.PosSemidef),
    Matrix.PosSemidef.sqrt hA * (Matrix.PosSemidef.sqrt hA).transpose = A := by
  /- @proof-region region.target-node.session.ad660f277cb496c8 begin -/
  intro m A hA
  set u := hA.isHermitian.eigenvectorUnitary with hu
  set φ := Unitary.conjStarAlgAut ℝ (Matrix (Fin m) (Fin m) ℝ) u with hφ
  set D : Matrix (Fin m) (Fin m) ℝ :=
    Matrix.diagonal (RCLike.ofReal ∘ (fun x => Real.sqrt x) ∘ hA.isHermitian.eigenvalues) with hD
  set Lam : Matrix (Fin m) (Fin m) ℝ :=
    Matrix.diagonal (RCLike.ofReal ∘ hA.isHermitian.eigenvalues) with hLam
  have hsqrt : Matrix.PosSemidef.sqrt hA = φ D := by
    unfold Matrix.PosSemidef.sqrt
    rw [show Matrix.PosSemidef.sqrt._proof_1 hA = hA.isHermitian from Subsingleton.elim _ _]
    rw [hφ, Unitary.conjStarAlgAut_apply, ← hu, ← hD]
  have hA_spec : A = φ Lam := by
    rw [hφ, hLam, hu]
    exact Matrix.IsHermitian.spectral_theorem hA.isHermitian
  have hDD : D * D = Lam := by
    rw [hD, hLam, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [Function.comp_apply, ← RCLike.ofReal_mul,
      Real.mul_self_sqrt (Matrix.PosSemidef.eigenvalues_nonneg hA i)]
  have hstarD : star D = D := by
    rw [hD, Matrix.star_eq_conjTranspose]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.diagonal]
    · simp [Matrix.diagonal, hij, Ne.symm hij]
  have hdt : (φ D).transpose = φ D := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial, ← Matrix.star_eq_conjTranspose,
      ← map_star, hstarD]
  calc Matrix.PosSemidef.sqrt hA * (Matrix.PosSemidef.sqrt hA).transpose
      = φ D * (φ D).transpose := by rw [hsqrt]
    _ = φ D * φ D := by rw [hdt]
    _ = φ (D * D) := by rw [← map_mul]
    _ = φ Lam := by rw [hDD]
    _ = A := by rw [← hA_spec]
  /- @proof-region region.target-node.session.ad660f277cb496c8 end -/

end
end Statlib.Imported

