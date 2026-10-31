import Statlib.StatFoundation.Statistics.Asymptotic.ScoreCLT
import Statlib.StatFoundation.Convergence.Resampling.GaussianMaxComparison
import Statlib.StatFoundation.Convergence.AnalysisTools.GaussianMaxAnticoncentration
import Statlib.StatFoundation.Statistics.Asymptotic.LAN
import Statlib.StatFoundation.Convergence.AnalysisTools.SmoothMax
import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import ProverJobs.job_paper_68f77b4042a84f6999315e1f7b578de2.Vocabulary
import ProverJobs.job_paper_68f77b4042a84f6999315e1f7b578de2.Base

namespace PaperProofTasks.job_paper_68f77b4042a84f6999315e1f7b578de2

open _root_.PaperProofTasks.job_paper_68f77b4042a84f6999315e1f7b578de2.Statlib.Imported
open scoped BigOperators

namespace Statlib.Imported

open scoped BigOperators

set_option autoImplicit false in
theorem statopia_math_node_3150113155_06872c0c : ∀ (p : ℕ) (hp : 0 < p) (β : ℝ) (hβ : 0 < β),
    ∀ z : Fin p → ℝ,
      let D : (Fin p → ℝ) →L[ℝ] ℝ :=
        ∑ m : Fin p,
          (β * Real.exp (β * z m)) •
            (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin p => ℝ) m)
      HasFDerivAt (fun v : Fin p → ℝ => ∑ m : Fin p, Real.exp (β * v m)) D z ∧
        ∀ j : Fin p, D (Pi.single j 1) = β * Real.exp (β * z j) := by
  /- @proof-region region.target-node.session.6860f2b29a0fffc6 begin -/
  intro p hp β hβ z
  dsimp only
  constructor
  · have hterm : ∀ m : Fin p,
        HasFDerivAt (fun v : Fin p → ℝ => Real.exp (β * v m))
          (Real.exp (β * z m) •
            ((β : ℝ) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin p => ℝ) m)) z := by
      intro m
      have hlin : HasFDerivAt (fun v : Fin p → ℝ => β * v m)
          ((β : ℝ) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin p => ℝ) m) z := by
        have h := ContinuousLinearMap.hasFDerivAt
          ((β : ℝ) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin p => ℝ) m) (x := z)
        simpa [ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul] using h
      have hc := HasDerivAt.comp_hasFDerivAt z (Real.hasDerivAt_exp (β * z m)) hlin
      simpa using hc
    have hfun : (∑ m : Fin p, (fun v : Fin p → ℝ => Real.exp (β * v m)))
        = fun v : Fin p → ℝ => ∑ m : Fin p, Real.exp (β * v m) := by
      funext v
      simp [Finset.sum_apply]
    have hsum : HasFDerivAt (∑ m : Fin p, (fun v : Fin p → ℝ => Real.exp (β * v m)))
        (∑ m : Fin p, Real.exp (β * z m) •
          ((β : ℝ) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin p => ℝ) m)) z := by
      apply HasFDerivAt.sum
      intro m _
      exact hterm m
    rw [hfun] at hsum
    have hD : (∑ m : Fin p, Real.exp (β * z m) •
          ((β : ℝ) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin p => ℝ) m))
        = ∑ m : Fin p, (β * Real.exp (β * z m)) •
          ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin p => ℝ) m := by
      refine Finset.sum_congr rfl ?_
      intro m _
      have hc : Real.exp (β * z m) * β = β * Real.exp (β * z m) := by ring
      rw [smul_smul, hc]
    rw [hD] at hsum
    exact hsum
  · intro j
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply]
    rw [Finset.sum_eq_single (a := j)
      (fun b _ hbj => by rw [Pi.single_eq_of_ne hbj 1, smul_zero])
      (fun hj => by exact absurd (Finset.mem_univ j) hj)]
    simp [Pi.single_eq_same, smul_eq_mul]
  /- @proof-region region.target-node.session.6860f2b29a0fffc6 end -/

end Statlib.Imported

