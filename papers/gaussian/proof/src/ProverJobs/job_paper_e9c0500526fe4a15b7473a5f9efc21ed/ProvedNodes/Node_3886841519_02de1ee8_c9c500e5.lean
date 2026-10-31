import ProverJobs.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Vocabulary
import ProverJobs.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Base
import ProverJobs.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.ProvedNodes.Node_176343912_26262eb8_a68f9353
import ProverJobs.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.ProvedNodes.Node_2129193587_e4214c03_4f4a3f23

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
theorem statopia_math_node_3886841519_02de1ee8 : ∀ (p k : ℕ) (hp : 1 ≤ p) (hk : 1 ≤ k) (hkp : k ≤ p)
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
          (∀ w : Fin p → ℝ,
              maxOverJ perm k (sdOf S) tau ((sqrtCovMat hS).mulVec w) =
                Finset.univ.sup'
                  (⟨⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hk⟩, Finset.mem_univ _⟩ :
                    (Finset.univ : Finset (Fin k)).Nonempty)
                  (fun l : Fin k =>
                    ((Matrix.transpose (Matrix.transpose Q * Cmat)).mulVec
                      ((Matrix.transpose Q).mulVec w)) l)) ∧
            (∀ (w : Fin p → ℝ) (t : ℝ),
              maxOverJ perm k (sdOf S) tau ((sqrtCovMat hS).mulVec w) ≤ t ↔
                ((Matrix.transpose Q).mulVec w) ∈
                  {x : Fin r → ℝ | ∀ l : Fin k,
                    ((Matrix.transpose (Matrix.transpose Q * Cmat)).mulVec x) l ≤ t}) := by
  /- @proof-region region.target-node.session.a855fce64497fe5a begin -/
  intro p k hp hk hkp S hS hspos tau htau0 htau1 perm
  intro D Pi Dpow Cmat W r Q hQ hspan
  set R : Matrix (Fin r) (Fin k) ℝ := Matrix.transpose Q * Cmat with hR
  obtain ⟨hr1, hrk, hQQ, hCmatQR, hCmatT, hiv, hCne⟩ :=
    statopia_math_node_176343912_26262eb8 p k hp hk hkp S hS hspos tau htau0 htau1 perm Q hQ hspan
  have key : ∀ w : Fin p → ℝ,
      maxOverJ perm k (sdOf S) tau (Matrix.mulVec (sqrtCovMat hS) w)
        = Finset.univ.sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩
            (fun l : Fin k =>
              Matrix.mulVec (Matrix.transpose R) (Matrix.mulVec (Matrix.transpose Q) w) l) := by
    intro w
    have hAsym : Matrix.transpose (sqrtCovMat hS) = sqrtCovMat hS := by
      simpa only [sqrtCovMat] using statopia_math_node_2129193587_e4214c03 p S hS
    have hMax : ∀ u : Fin p → ℝ,
        maxOverJ perm k (sdOf S) tau u
          = Finset.univ.sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩
              (fun l : Fin k => u (perm (posIn hkp l)) / (sdOf S (perm (posIn hkp l))) ^ tau) := by
      intro u
      have hJpos : Jpos (pn := p) k = Finset.univ.image (posIn hkp) := by
        ext i
        simp only [Jpos, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
        constructor
        · intro h
          exact ⟨⟨i.1, h⟩, Fin.ext rfl⟩
        · rintro ⟨a, rfl⟩
          exact a.2
      have himg : (Jset perm k).image (fun j => u j / (sdOf S j) ^ tau)
          = Finset.univ.image
              (fun l : Fin k => u (perm (posIn hkp l)) / (sdOf S (perm (posIn hkp l))) ^ tau) := by
        simp only [Jset, hJpos, Finset.image_image]
        rfl
      have hss : sSup ((Finset.univ.image
              (fun l : Fin k => u (perm (posIn hkp l)) / (sdOf S (perm (posIn hkp l))) ^ tau)) : Set ℝ)
          = Finset.univ.sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩
              (fun l : Fin k => u (perm (posIn hkp l)) / (sdOf S (perm (posIn hkp l))) ^ tau) := by
        set L : Fin k → ℝ := fun l => u (perm (posIn hkp l)) / (sdOf S (perm (posIn hkp l))) ^ tau with hL
        have hne : ((Finset.univ.image L) : Set ℝ).Nonempty :=
          ⟨L ⟨0, hk⟩, Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨⟨0, hk⟩, Finset.mem_univ _, rfl⟩)⟩
        have hbd : BddAbove ((Finset.univ.image L) : Set ℝ) :=
          (Finset.univ.image L).finite_toSet.bddAbove
        apply le_antisymm
        · refine csSup_le hne ?_
          intro b hb
          rw [Finset.mem_coe] at hb
          obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hb
          exact Finset.le_sup' L (Finset.mem_univ l)
        · rw [Finset.sup'_le_iff]
          intro b _
          exact le_csSup hbd (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩))
      simp only [maxOverJ]; rw [himg, hss]
    have hCt : ∀ (u : Fin p → ℝ) (l : Fin k),
        Matrix.mulVec (Matrix.transpose Cmat) u l
          = (sdOf S (perm (posIn hkp l))) ^ (-tau)
              * Matrix.mulVec (Matrix.transpose (sqrtCovMat hS)) u (perm (posIn hkp l)) := by
      intro u l
      have hDrw : Dpow = Matrix.diagonal (fun l => (sdOf S (perm (posIn hkp l))) ^ (-tau)) := by
        rw [show Dpow = Matrix.diagonal (fun l => (D l l) ^ (-tau)) from rfl]
        congr 1
        funext l
        rw [show D l l = sdOf S (perm (posIn hkp l)) from by
          rw [show D = Matrix.diagonal (fun l => sdOf S (perm (posIn hkp l))) from rfl]
          exact Matrix.diagonal_apply_eq _ _]
      have hDpowT : Matrix.transpose Dpow = Dpow := by
        rw [hDrw, Matrix.diagonal_transpose]
      have hDpow : ∀ (y : Fin k → ℝ) (i : Fin k),
          Dpow.mulVec y i = (sdOf S (perm (posIn hkp i))) ^ (-tau) * y i := by
        intro y i
        rw [hDrw]
        simp only [Matrix.mulVec, dotProduct, Matrix.diagonal_apply, ite_mul, zero_mul]
        rw [Finset.sum_ite_eq]
        simp only [Finset.mem_univ, if_true]
      have hPirw : Pi = Matrix.of (fun (l : Fin k) (m : Fin p) =>
          if m = perm (posIn hkp l) then (1 : ℝ) else 0) := rfl
      have hPi : ∀ (z : Fin p → ℝ) (i : Fin k), Pi.mulVec z i = z (perm (posIn hkp i)) := by
        intro z i
        rw [hPirw]
        simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, ite_mul, one_mul, zero_mul]
        rw [Finset.sum_ite_eq']
        simp only [Finset.mem_univ, if_true]
      rw [show Cmat = sqrtCovMat hS * Matrix.transpose Pi * Dpow from rfl]
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hDpowT]
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      rw [hDpow (Pi.mulVec (Matrix.mulVec (Matrix.transpose (sqrtCovMat hS)) u)) l]
      rw [hPi (Matrix.mulVec (Matrix.transpose (sqrtCovMat hS)) u) l]
    have h2 : Matrix.mulVec (Matrix.transpose Cmat) w
        = Matrix.mulVec (Matrix.transpose R) (Matrix.mulVec (Matrix.transpose Q) w) := hiv w
    have hfun : (fun l : Fin k =>
          Matrix.mulVec (sqrtCovMat hS) w (perm (posIn hkp l)) / (sdOf S (perm (posIn hkp l))) ^ tau)
        = (fun l : Fin k => Matrix.mulVec (Matrix.transpose Cmat) w l) := by
      funext l
      rw [hCt w l, hAsym, Real.rpow_neg (le_of_lt (hspos (perm (posIn hkp l)))), inv_mul_eq_div]
    rw [hMax (Matrix.mulVec (sqrtCovMat hS) w), hfun, h2]
  constructor
  · exact key
  · intro w t
    rw [key w]
    simp only [Set.mem_setOf_eq, Finset.sup'_le_iff, Finset.mem_univ, true_imp_iff]
  /- @proof-region region.target-node.session.a855fce64497fe5a end -/

end
end Statlib.Imported

