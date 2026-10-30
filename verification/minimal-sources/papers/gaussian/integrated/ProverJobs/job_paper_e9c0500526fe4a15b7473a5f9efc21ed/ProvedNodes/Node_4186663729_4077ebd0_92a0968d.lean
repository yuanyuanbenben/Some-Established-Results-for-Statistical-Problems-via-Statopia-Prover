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
theorem statopia_math_node_4186663729_4077ebd0 : ∀ (p k : ℕ) (hp : 1 ≤ p) (hk : 1 ≤ k)
    (hkp : k ≤ p) (S : Matrix (Fin p) (Fin p) ℝ) (hS : S.PosSemidef)
    (hspos : ∀ j : Fin p, 0 < sdOf S j) (tau : ℝ) (htau0 : 0 ≤ tau) (htau1 : tau < 1)
    (perm : Equiv.Perm (Fin p)),
    let D : Matrix (Fin k) (Fin k) ℝ :=
      Matrix.diagonal (fun (l : Fin k) => sdOf S (perm (posIn hkp l)))
    let Pi : Matrix (Fin k) (Fin p) ℝ :=
      Matrix.of (fun (l : Fin k) (m : Fin p) => if m = perm (posIn hkp l) then (1 : ℝ) else 0)
    let Dpow : Matrix (Fin k) (Fin k) ℝ :=
      Matrix.diagonal (fun (l : Fin k) => D l l ^ (-tau))
    let Cmat : Matrix (Fin p) (Fin k) ℝ :=
      sqrtCovMat hS * Matrix.transpose Pi * Dpow
    let W : Submodule ℝ (Fin p → ℝ) :=
      Submodule.span ℝ (Set.range (fun (l : Fin k) => (fun (m : Fin p) => Cmat m l)))
    let r : ℕ := Module.finrank ℝ W
    1 ≤ r ∧ r ≤ k ∧ Cmat ≠ 0 := by
  /- @proof-region region.target-node.session.48db74e886d3d414 begin -/
  intro p k hp hk hkp S hS hspos tau htau0 htau1 perm
  let D : Matrix (Fin k) (Fin k) ℝ := Matrix.diagonal (fun l => sdOf S (perm (posIn hkp l)))
  let Pi : Matrix (Fin k) (Fin p) ℝ :=
    Matrix.of (fun (l : Fin k) (m : Fin p) => if m = perm (posIn hkp l) then (1 : ℝ) else 0)
  let Dpow : Matrix (Fin k) (Fin k) ℝ := Matrix.diagonal (fun l => D l l ^ (-tau))
  let Cmat : Matrix (Fin p) (Fin k) ℝ := sqrtCovMat hS * Matrix.transpose Pi * Dpow
  let W : Submodule ℝ (Fin p → ℝ) :=
    Submodule.span ℝ (Set.range (fun l => (fun m => Cmat m l)))
  change 1 ≤ Module.finrank ℝ W ∧ Module.finrank ℝ W ≤ k ∧ Cmat ≠ 0
  have hMM : sqrtCovMat hS * sqrtCovMat hS = S := by
    have hddsq :
        Matrix.diagonal ((RCLike.ofReal : ℝ → ℝ) ∘ (fun x : ℝ => Real.sqrt x)
            ∘ hS.isHermitian.eigenvalues)
            * Matrix.diagonal ((RCLike.ofReal : ℝ → ℝ) ∘ (fun x : ℝ => Real.sqrt x)
              ∘ hS.isHermitian.eigenvalues)
          = Matrix.diagonal ((RCLike.ofReal : ℝ → ℝ) ∘ hS.isHermitian.eigenvalues) := by
      rw [Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      show RCLike.ofReal (Real.sqrt (hS.isHermitian.eigenvalues i))
            * RCLike.ofReal (Real.sqrt (hS.isHermitian.eigenvalues i))
          = RCLike.ofReal (hS.isHermitian.eigenvalues i)
      rw [← RCLike.ofReal_mul, ← pow_two,
        Real.sq_sqrt (Matrix.PosSemidef.eigenvalues_nonneg hS i)]
    have hspec :
        S = (Unitary.conjStarAlgAut ℝ (Matrix (Fin p) (Fin p) ℝ)) hS.isHermitian.eigenvectorUnitary
            (Matrix.diagonal ((RCLike.ofReal : ℝ → ℝ) ∘ hS.isHermitian.eigenvalues)) :=
      Matrix.IsHermitian.spectral_theorem hS.isHermitian
    unfold sqrtCovMat Matrix.PosSemidef.sqrt
    trans (Unitary.conjStarAlgAut ℝ (Matrix (Fin p) (Fin p) ℝ)) hS.isHermitian.eigenvectorUnitary
        (Matrix.diagonal ((RCLike.ofReal : ℝ → ℝ) ∘ hS.isHermitian.eigenvalues))
    · rw [← Unitary.conjStarAlgAut_apply (S := ℝ) (R := Matrix (Fin p) (Fin p) ℝ)
        (hS.isHermitian.eigenvectorUnitary)
        (Matrix.diagonal ((RCLike.ofReal : ℝ → ℝ) ∘ (fun x : ℝ => Real.sqrt x)
          ∘ hS.isHermitian.eigenvalues))]
      rw [← map_mul]
      rw [hddsq]
    · exact hspec.symm
  have hMcol : ∀ (i : Fin p) (l : Fin k),
      (sqrtCovMat hS * Matrix.transpose Pi) i l = sqrtCovMat hS i (perm (posIn hkp l)) := by
    intro i l
    rw [Matrix.mul_apply]
    have hsum : ∑ m : Fin p, sqrtCovMat hS i m * (Matrix.transpose Pi) m l
        = sqrtCovMat hS i (perm (posIn hkp l)) * (Matrix.transpose Pi) (perm (posIn hkp l)) l :=
      Finset.sum_eq_single (perm (posIn hkp l))
        (fun b _ hb => by
          have hz : (Matrix.transpose Pi) b l = 0 := by
            rw [Matrix.transpose_apply]
            show (Matrix.of (fun (l : Fin k) (m : Fin p) =>
              if m = perm (posIn hkp l) then (1 : ℝ) else 0)) l b = 0
            rw [Matrix.of_apply, if_neg hb]
          rw [hz, mul_zero])
        (fun h => absurd (Finset.mem_univ (perm (posIn hkp l))) h)
    rw [hsum, Matrix.transpose_apply]
    show sqrtCovMat hS i (perm (posIn hkp l)) *
      (Matrix.of (fun (l : Fin k) (m : Fin p) =>
        if m = perm (posIn hkp l) then (1 : ℝ) else 0)) l (perm (posIn hkp l))
      = sqrtCovMat hS i (perm (posIn hkp l))
    rw [Matrix.of_apply, if_pos rfl, mul_one]
  have hDpw : ∀ l : Fin k, Dpow l l = (sdOf S (perm (posIn hkp l))) ^ (-tau) := by
    intro l
    have hD : D l l = sdOf S (perm (posIn hkp l)) := by
      show Matrix.diagonal (fun l : Fin k => sdOf S (perm (posIn hkp l))) l l
        = sdOf S (perm (posIn hkp l))
      rw [Matrix.diagonal_apply_eq]
    show Matrix.diagonal (fun l : Fin k => D l l ^ (-tau)) l l
      = (sdOf S (perm (posIn hkp l))) ^ (-tau)
    rw [Matrix.diagonal_apply_eq, hD]
  have hexp : ∀ (i : Fin p) (l : Fin k),
      Cmat i l = sqrtCovMat hS i (perm (posIn hkp l)) * (sdOf S (perm (posIn hkp l))) ^ (-tau) := by
    intro i l
    show ((sqrtCovMat hS * Matrix.transpose Pi) * Dpow) i l
      = sqrtCovMat hS i (perm (posIn hkp l)) * (sdOf S (perm (posIn hkp l))) ^ (-tau)
    rw [Matrix.mul_apply]
    have hsum : ∑ m : Fin k, (sqrtCovMat hS * Matrix.transpose Pi) i m * Dpow m l
        = (sqrtCovMat hS * Matrix.transpose Pi) i l * Dpow l l :=
      Finset.sum_eq_single l
        (fun b _ hb => by
          have hz : Dpow b l = 0 := by
            show Matrix.diagonal (fun l : Fin k => D l l ^ (-tau)) b l = 0
            rw [Matrix.diagonal_apply, if_neg hb]
          rw [hz, mul_zero])
        (fun h => absurd (Finset.mem_univ l) h)
    rw [hsum, hMcol i l, hDpw l]
  have hcolne : ∀ l : Fin k, (fun i : Fin p => sqrtCovMat hS i (perm (posIn hkp l))) ≠ 0 := by
    intro l hzero
    have hSjj : 0 < S (perm (posIn hkp l)) (perm (posIn hkp l)) :=
      Real.sqrt_pos.mp (hspos (perm (posIn hkp l)))
    have hsum0 : S (perm (posIn hkp l)) (perm (posIn hkp l)) = 0 := by
      rw [← hMM, Matrix.mul_apply]
      refine Finset.sum_eq_zero (fun m _ => ?_)
      have hm : sqrtCovMat hS m (perm (posIn hkp l)) = 0 := by
        have := congrFun hzero m
        simpa using this
      rw [hm, mul_zero]
    exact absurd hsum0 (ne_of_gt hSjj)
  have hk0 : 0 < k := by omega
  let l0 : Fin k := ⟨0, hk0⟩
  have hd : (sdOf S (perm (posIn hkp l0))) ^ (-tau) ≠ 0 := by
    have hpos : 0 < sdOf S (perm (posIn hkp l0)) := hspos _
    positivity
  have hCne : ∃ i : Fin p, Cmat i l0 ≠ 0 := by
    have hcol : (fun i : Fin p => sqrtCovMat hS i (perm (posIn hkp l0))) ≠ 0 := hcolne l0
    by_contra h
    apply hcol
    funext i
    by_contra hi
    exact h ⟨i, by rw [hexp i l0]; exact mul_ne_zero hi hd⟩
  have hwne : (fun m : Fin p => Cmat m l0) ≠ 0 := by
    obtain ⟨i, hi⟩ := hCne
    intro hh
    exact hi (by simpa using congrFun hh i)
  have hwW : (fun m : Fin p => Cmat m l0) ∈ W := by
    show (fun m : Fin p => Cmat m l0) ∈ Submodule.span ℝ (Set.range (fun l => (fun m => Cmat m l)))
    exact Submodule.subset_span ⟨l0, rfl⟩
  have hnt : Nontrivial W :=
    ⟨⟨fun m : Fin p => Cmat m l0, hwW⟩, 0,
      fun hh => hwne (by simpa using congrArg (fun x : W => x.1) hh)⟩
  have hne : Cmat ≠ 0 := by
    obtain ⟨i, hi⟩ := hCne
    intro h
    exact hi (by simp [h])
  have h1r : 1 ≤ Module.finrank ℝ W := by
    have hpos : 0 < Module.finrank ℝ W := Module.finrank_pos_iff.mpr hnt
    omega
  have hdim : Module.finrank ℝ (Fin k → ℝ) = k := by simp
  have hle : Module.finrank ℝ W ≤ k := by
    have hWrange : W = (Matrix.mulVecLin Cmat).range := by
      rw [Matrix.range_mulVecLin]
      rfl
    rw [hWrange]
    calc Module.finrank ℝ (Matrix.mulVecLin Cmat).range
        ≤ Module.finrank ℝ (Fin k → ℝ) := LinearMap.finrank_range_le _
      _ = k := hdim
  refine ⟨h1r, hle, hne⟩
  /- @proof-region region.target-node.session.48db74e886d3d414 end -/

end
end Statlib.Imported

