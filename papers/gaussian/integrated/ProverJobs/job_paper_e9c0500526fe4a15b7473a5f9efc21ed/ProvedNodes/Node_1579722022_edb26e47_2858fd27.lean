import ProverJobs.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Vocabulary
import ProverJobs.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Base

namespace PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed

open _root_.PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Statlib.Imported
open _root_.Statlib
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
universe u₀ u₁

set_option autoImplicit false in
theorem statopia_math_node_1579722022_edb26e47 : ∀ (p k : ℕ) (hp : 1 ≤ p) (hk : 1 ≤ k) (hkp : k ≤ p)
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
          Cmat = Q * (Matrix.transpose Q * Cmat) := by
  /- @proof-region region.target-node.session.5436a8eeb6522641 begin -/
  intro p k hp hk hkp S hS hspos tau htau0 htau1 perm
  intro D Pim Dpow Cmat W r
  intro Q hQ hspan
  have hmv_single : ∀ (M : Matrix (Fin p) (Fin r) ℝ) (j : Fin r),
      M.mulVec (Pi.single j (1 : ℝ)) = fun i => M i j := by
    intro M j
    rw [Matrix.mulVec_single_one]
    ext i
    exact rfl
  have hPW : ∀ x : Fin p → ℝ, x ∈ W → Q.mulVec (Q.transpose.mulVec x) = x := by
    intro x hx
    rw [← hspan] at hx
    refine Submodule.span_induction (p := fun z _ => Q.mulVec (Q.transpose.mulVec z) = z)
      ?_ ?_ ?_ ?_ hx
    · rintro y ⟨j, rfl⟩
      show Q.mulVec (Q.transpose.mulVec (fun m => Q m j)) = (fun m => Q m j)
      rw [← hmv_single Q j]
      have hinner : Q.transpose.mulVec (Q.mulVec (Pi.single j (1:ℝ))) = Pi.single j (1:ℝ) := by
        rw [Matrix.mulVec_mulVec, hQ, Matrix.one_mulVec]
      rw [hinner]
    · simp
    · intro x y _ _ hx' hy'
      simp [Matrix.mulVec_add, hx', hy']
    · intro a x _ hx'
      simp [Matrix.mulVec_smul, hx']
  ext m l
  have hcol : Q.mulVec (Q.transpose.mulVec (fun m => Cmat m l)) = (fun m => Cmat m l) :=
    hPW _ (Submodule.subset_span (Set.mem_range_self l))
  have hval : (Q.mulVec (Q.transpose.mulVec (fun m => Cmat m l))) m = Cmat m l :=
    congrFun hcol m
  have hM : (Q * (Q.transpose * Cmat)).mulVec (Pi.single l (1:ℝ)) m
      = (Q * (Q.transpose * Cmat)) m l :=
    congrFun (Matrix.mulVec_single_one (Q * (Q.transpose * Cmat)) l) m
  have hC : Cmat.mulVec (Pi.single l (1:ℝ)) = (fun m => Cmat m l) := by
    rw [Matrix.mulVec_single_one]
    ext i
    rfl
  rw [← hval, ← hM, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hC]
  /- @proof-region region.target-node.session.5436a8eeb6522641 end -/

end
end Statlib.Imported

