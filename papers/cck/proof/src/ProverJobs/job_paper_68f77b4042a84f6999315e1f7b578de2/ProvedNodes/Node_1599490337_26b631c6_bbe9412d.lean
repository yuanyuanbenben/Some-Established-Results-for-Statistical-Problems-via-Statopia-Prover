import Statlib.StatFoundation.Statistics.Asymptotic.ScoreCLT
import Statlib.StatFoundation.Convergence.Resampling.GaussianMaxComparison
import Statlib.StatFoundation.Convergence.AnalysisTools.GaussianMaxAnticoncentration
import Statlib.StatFoundation.Statistics.Asymptotic.LAN
import Statlib.StatFoundation.Convergence.AnalysisTools.SmoothMax
import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import ProverJobs.job_paper_68f77b4042a84f6999315e1f7b578de2.Vocabulary
import ProverJobs.job_paper_68f77b4042a84f6999315e1f7b578de2.Base
import ProverJobs.job_paper_68f77b4042a84f6999315e1f7b578de2.ProvedNodes.Node_1852335189_c4ea2480_2e9cbbf1
import ProverJobs.job_paper_68f77b4042a84f6999315e1f7b578de2.ProvedNodes.Node_3150113155_06872c0c_496d4291

namespace PaperProofTasks.job_paper_68f77b4042a84f6999315e1f7b578de2


open _root_.PaperProofTasks.job_paper_68f77b4042a84f6999315e1f7b578de2.Statlib.Imported
open scoped BigOperators

namespace Statlib.Imported

open scoped BigOperators

set_option autoImplicit false in
theorem statopia_math_node_1599490337_26b631c6 : ∀ (p : ℕ) (hp : 0 < p) (β : ℝ) (hβ : 0 < β),
    (∀ z : Fin p → ℝ, ∀ j : Fin p, coordPartial (smoothMaxFn β) j z = softmaxWt β z j) ∧
      (∀ k : Fin p,
        (fun w : Fin p → ℝ => coordPartial (smoothMaxFn β) k w) =
          fun w : Fin p → ℝ => softmaxWt β w k) := by
  /- @proof-region region.target-node.session.7c3f443c5129b710 begin -/
  intro p hp β hβ
  have hpoint : ∀ z : Fin p → ℝ, ∀ j : Fin p,
      coordPartial (smoothMaxFn β) j z = softmaxWt β z j := by
    intro z j
    obtain ⟨hD, hDeval⟩ := statopia_math_node_3150113155_06872c0c p hp β hβ z
    obtain ⟨hSpos, -, -⟩ := statopia_math_node_1852335189_c4ea2480 p hp β hβ z
    have hS : (∑ m : Fin p, Real.exp (β * z m)) ≠ 0 := ne_of_gt hSpos
    have hlog : HasFDerivAt (fun v : Fin p → ℝ => Real.log (∑ m : Fin p, Real.exp (β * v m)))
        ((∑ m : Fin p, Real.exp (β * z m))⁻¹ •
          (∑ m : Fin p, (β * Real.exp (β * z m)) •
            ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin p => ℝ) m)) z := by
      simpa [Function.comp] using (Real.hasDerivAt_log hS).comp_hasFDerivAt z hD
    have hmul : HasDerivAt (fun y : ℝ => β⁻¹ * y) β⁻¹
        (Real.log (∑ m : Fin p, Real.exp (β * z m))) := by
      simpa using (hasDerivAt_id (Real.log (∑ m : Fin p, Real.exp (β * z m)))).const_mul β⁻¹
    have hdiff : HasFDerivAt (fun v : Fin p → ℝ => β⁻¹ * Real.log (∑ m : Fin p, Real.exp (β * v m)))
        (β⁻¹ • ((∑ m : Fin p, Real.exp (β * z m))⁻¹ •
          (∑ m : Fin p, (β * Real.exp (β * z m)) •
            ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin p => ℝ) m))) z := by
      simpa [Function.comp] using hmul.comp_hasFDerivAt z hlog
    have hsmul : ∀ (c : ℝ) (L : (Fin p → ℝ) →L[ℝ] ℝ) (x : Fin p → ℝ),
        (c • L) x = c • L x := fun c L x => rfl
    have hLapply :
        (β⁻¹ • ((∑ m : Fin p, Real.exp (β * z m))⁻¹ •
          (∑ m : Fin p, (β * Real.exp (β * z m)) •
            ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin p => ℝ) m))) (Pi.single j 1)
        = β⁻¹ * ((∑ m : Fin p, Real.exp (β * z m))⁻¹ * (β * Real.exp (β * z j))) := by
      rw [hsmul, hsmul, hDeval j]
      simp only [smul_eq_mul]
    show fderiv ℝ (fun v : Fin p → ℝ => β⁻¹ * Real.log (∑ m : Fin p, Real.exp (β * v m))) z (Pi.single j 1) = softmaxWt β z j
    rw [hdiff.fderiv, hLapply]
    unfold softmaxWt
    rw [div_eq_mul_inv]
    calc β⁻¹ * ((∑ m : Fin p, Real.exp (β * z m))⁻¹ * (β * Real.exp (β * z j)))
        = (β⁻¹ * β) * ((∑ m : Fin p, Real.exp (β * z m))⁻¹ * Real.exp (β * z j)) := by ring
      _ = 1 * ((∑ m : Fin p, Real.exp (β * z m))⁻¹ * Real.exp (β * z j)) := by
            rw [inv_mul_cancel₀ (ne_of_gt hβ)]
      _ = Real.exp (β * z j) * (∑ m : Fin p, Real.exp (β * z m))⁻¹ := by ring
  refine ⟨hpoint, ?_⟩
  intro k
  funext w
  exact hpoint w k
  /- @proof-region region.target-node.session.7c3f443c5129b710 end -/

end Statlib.Imported

