import ProverJobs.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.Vocabulary
import ProverJobs.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.Base

namespace PaperProofTasks.job_paper_cb04ce35a04d48a9bf96750470ca0eb0

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal
open _root_.PaperProofTasks.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.Statlib.Imported

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal
namespace Statlib.Imported
open _root_.Statlib
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_3740261163_f3714e7b : ∀ (pn : ℕ) (S : Matrix (Fin pn) (Fin pn) ℝ) (hS : S.PosSemidef) (j : Fin pn),
    ∑ k : Fin pn,
      (Matrix.PosSemidef.sqrt hS) j k * (Matrix.PosSemidef.sqrt hS) j k = S j j := by
  /- @proof-region region.target-node.session.0362e94b035c181b begin -/
  intro pn S hS j
  have hA : Matrix.PosSemidef.sqrt hS
      = (hS.isHermitian.eigenvectorUnitary : Matrix (Fin pn) (Fin pn) ℝ) *
        Matrix.diagonal (Real.sqrt ∘ hS.isHermitian.eigenvalues) *
        star (hS.isHermitian.eigenvectorUnitary : Matrix (Fin pn) (Fin pn) ℝ) := by
    rw [Matrix.PosSemidef.sqrt]
    rfl
  let U : Matrix (Fin pn) (Fin pn) ℝ := (hS.isHermitian.eigenvectorUnitary : Matrix (Fin pn) (Fin pn) ℝ)
  let D : Matrix (Fin pn) (Fin pn) ℝ := Matrix.diagonal (Real.sqrt ∘ hS.isHermitian.eigenvalues)
  have hA' : Matrix.PosSemidef.sqrt hS = U * D * star U := hA
  have hUU : star U * U = 1 := by
    show star (hS.isHermitian.eigenvectorUnitary : Matrix (Fin pn) (Fin pn) ℝ) *
        (hS.isHermitian.eigenvectorUnitary : Matrix (Fin pn) (Fin pn) ℝ) = 1
    exact Matrix.UnitaryGroup.star_mul_self hS.isHermitian.eigenvectorUnitary
  have hUtr : star U = U.transpose := by
    show star (hS.isHermitian.eigenvectorUnitary : Matrix (Fin pn) (Fin pn) ℝ) =
      (hS.isHermitian.eigenvectorUnitary : Matrix (Fin pn) (Fin pn) ℝ).transpose
    exact Matrix.conjTranspose_eq_transpose_of_trivial _
  have hDD : D * D = Matrix.diagonal hS.isHermitian.eigenvalues := by
    show Matrix.diagonal (Real.sqrt ∘ hS.isHermitian.eigenvalues) *
        Matrix.diagonal (Real.sqrt ∘ hS.isHermitian.eigenvalues) =
      Matrix.diagonal hS.isHermitian.eigenvalues
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact Real.mul_self_sqrt (Matrix.PosSemidef.eigenvalues_nonneg hS i)
  have hofReal : RCLike.ofReal ∘ hS.isHermitian.eigenvalues = hS.isHermitian.eigenvalues := by
    funext i
    simp
  have hSspec : S = U * Matrix.diagonal hS.isHermitian.eigenvalues * star U := by
    have hspec := Matrix.IsHermitian.spectral_theorem hS.isHermitian
    rw [Unitary.conjStarAlgAut_apply] at hspec
    rw [hofReal] at hspec
    simpa using hspec
  have hAA : Matrix.PosSemidef.sqrt hS * Matrix.PosSemidef.sqrt hS = S := by
    rw [hA', hSspec]
    calc (U * D * star U) * (U * D * star U)
        = U * D * (star U * U) * D * star U := by noncomm_ring
      _ = U * D * 1 * D * star U := by rw [hUU]
      _ = U * (D * D) * star U := by noncomm_ring
      _ = U * Matrix.diagonal hS.isHermitian.eigenvalues * star U := by rw [hDD]
  have hsym : (Matrix.PosSemidef.sqrt hS).transpose = Matrix.PosSemidef.sqrt hS := by
    rw [hA', hUtr]
    show (U * Matrix.diagonal (Real.sqrt ∘ hS.isHermitian.eigenvalues) * U.transpose).transpose =
      U * Matrix.diagonal (Real.sqrt ∘ hS.isHermitian.eigenvalues) * U.transpose
    simp only [Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.transpose_transpose]
    noncomm_ring
  have hmain : ∑ k : Fin pn, (Matrix.PosSemidef.sqrt hS) j k * (Matrix.PosSemidef.sqrt hS) j k
      = (Matrix.PosSemidef.sqrt hS * Matrix.PosSemidef.sqrt hS) j j := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have hkj : (Matrix.PosSemidef.sqrt hS) k j = (Matrix.PosSemidef.sqrt hS) j k := by
      have h := congrFun (congrFun hsym k) j
      simpa using h.symm
    rw [hkj]
  rw [hmain, hAA]
  /- @proof-region region.target-node.session.0362e94b035c181b end -/

end

end Statlib.Imported

