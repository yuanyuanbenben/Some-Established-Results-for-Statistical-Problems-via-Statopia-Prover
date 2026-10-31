import ProverJobs.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Vocabulary
import ProverJobs.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Base
import ProverJobs.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.ProvedNodes.Node_1579722022_edb26e47_2858fd27
import ProverJobs.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.ProvedNodes.Node_4186663729_4077ebd0_92a0968d

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
theorem statopia_math_node_176343912_26262eb8 : ∀ (p k : ℕ) (hp : 1 ≤ p) (hk : 1 ≤ k) (hkp : k ≤ p)
    (S : Matrix (Fin p) (Fin p) ℝ) (hS : S.PosSemidef)
    (hspos : ∀ j : Fin p, 0 < sdOf S j)
    (tau : ℝ) (htau0 : 0 ≤ tau) (htau1 : tau < 1)
    (perm : Equiv.Perm (Fin p)),
    let D : Matrix (Fin k) (Fin k) ℝ :=
      Matrix.diagonal (fun l => sdOf S (perm (posIn hkp l)))
    let Pi : Matrix (Fin k) (Fin p) ℝ :=
      Matrix.of (fun (l : Fin k) (m : Fin p) =>
        if m = perm (posIn hkp l) then (1 : ℝ) else 0)
    let Dpow : Matrix (Fin k) (Fin k) ℝ :=
      Matrix.diagonal (fun l => D l l ^ (-tau))
    let Cmat : Matrix (Fin p) (Fin k) ℝ :=
      sqrtCovMat hS * Matrix.transpose Pi * Dpow
    let W : Submodule ℝ (Fin p → ℝ) :=
      Submodule.span ℝ (Set.range (fun l => (fun m => Cmat m l)))
    let r : ℕ := Module.finrank ℝ W
    ∀ (Q : Matrix (Fin p) (Fin r) ℝ),
      Matrix.transpose Q * Q = 1 →
        Submodule.span ℝ (Set.range (fun j => (fun m => Q m j))) = W →
          1 ≤ r ∧ r ≤ k ∧
            Matrix.transpose Q * Q = 1 ∧
              Cmat = Q * (Matrix.transpose Q * Cmat) ∧
                Matrix.transpose Cmat =
                    Matrix.transpose (Matrix.transpose Q * Cmat) * Matrix.transpose Q ∧
                  (∀ v : Fin p → ℝ,
                      (Matrix.transpose Cmat).mulVec v =
                        (Matrix.transpose (Matrix.transpose Q * Cmat)).mulVec
                          ((Matrix.transpose Q).mulVec v)) ∧
                    Cmat ≠ 0 := by
  /- @proof-region region.target-node.session.69fcf6591424c8fd begin -/
  intro p k hp hk hkp S hS hspos tau htau0 htau1 perm D Pi Dpow Cmat W r Q hQ hspan
  have hQR : Cmat = Q * (Matrix.transpose Q * Cmat) :=
    statopia_math_node_1579722022_edb26e47 p k hp hk hkp S hS hspos tau htau0 htau1 perm
      Q hQ hspan
  have hsupp : 1 ≤ r ∧ r ≤ k ∧ Cmat ≠ 0 :=
    statopia_math_node_4186663729_4077ebd0 p k hp hk hkp S hS hspos tau htau0 htau1 perm
  obtain ⟨h1r, hrk, hne⟩ := hsupp
  have h5 : Cmat.transpose = (Matrix.transpose Q * Cmat).transpose * Q.transpose := by
    conv_lhs => rw [hQR]
    exact Matrix.transpose_mul Q (Matrix.transpose Q * Cmat)
  refine ⟨h1r, hrk, hQ, hQR, h5, ?_, hne⟩
  · intro v
    rw [h5, Matrix.mulVec_mulVec]
  /- @proof-region region.target-node.session.69fcf6591424c8fd end -/

end
end Statlib.Imported

