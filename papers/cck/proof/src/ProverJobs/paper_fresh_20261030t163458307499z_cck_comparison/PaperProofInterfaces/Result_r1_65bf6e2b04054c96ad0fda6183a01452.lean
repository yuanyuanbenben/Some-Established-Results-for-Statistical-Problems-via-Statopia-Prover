import Statlib.StatFoundation.Statistics.Asymptotic.ScoreCLT
import Statlib.StatFoundation.Convergence.Resampling.GaussianMaxComparison
import Statlib.StatFoundation.Convergence.AnalysisTools.GaussianMaxAnticoncentration
import Statlib.StatFoundation.Statistics.Asymptotic.LAN
import Statlib.StatFoundation.Convergence.AnalysisTools.SmoothMax
import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import ProverJobs.job_paper_68f77b4042a84f6999315e1f7b578de2.Vocabulary
import ProverJobs.job_paper_68f77b4042a84f6999315e1f7b578de2.ProvedNodes
import ProverJobs.job_paper_68f77b4042a84f6999315e1f7b578de2.Base

namespace PaperProofTasks.job_paper_68f77b4042a84f6999315e1f7b578de2

namespace Statlib.Imported

open scoped BigOperators

theorem paper_68f77b4042a84f6999315e1f7b578de2
    (p : ℕ) (hp : 0 < p) (β : ℝ) (hβ : 0 < β) :
    (∀ z : Fin p → ℝ, ∀ j k : Fin p,
        coordPartial (smoothMaxFn β) j z = softmaxWt β z j ∧
        mixedCoordPartial (smoothMaxFn β) j k z = β * wMatEntry β z j k) ∧
      (∀ z : Fin p → ℝ, ∀ j : Fin p, 0 ≤ softmaxWt β z j) ∧
      (∀ z : Fin p → ℝ, (∑ j : Fin p, softmaxWt β z j) = 1) ∧
      (∀ z : Fin p → ℝ, (∑ a : Fin p, ∑ b : Fin p, |wMatEntry β z a b|) ≤ 2)
:= by
  /- @proof-region region.root.ab6fbb66d713 begin -/
  have hSpos : ∀ z : Fin p → ℝ, 0 < ∑ m : Fin p, Real.exp (β * z m) := by
    intro z
    exact Finset.sum_pos (fun m _ => Real.exp_pos _) ⟨⟨0, hp⟩, Finset.mem_univ _⟩
  have hnonneg : ∀ z : Fin p → ℝ, ∀ j : Fin p, 0 ≤ softmaxWt β z j := by
    intro z j
    simp only [softmaxWt]
    exact div_nonneg (Real.exp_pos _).le (hSpos z).le
  have hsum : ∀ z : Fin p → ℝ, (∑ j : Fin p, softmaxWt β z j) = 1 := by
    intro z
    have hSne : (∑ m : Fin p, Real.exp (β * z m)) ≠ 0 := ne_of_gt (hSpos z)
    simp only [softmaxWt]
    rw [← Finset.sum_div]
    exact div_self hSne
  have hcoord : ∀ z : Fin p → ℝ, ∀ j k : Fin p,
      coordPartial (smoothMaxFn β) j z = softmaxWt β z j ∧
      mixedCoordPartial (smoothMaxFn β) j k z = β * wMatEntry β z j k := by
    intro z j k
    refine ⟨(statopia_math_node_1599490337_26b631c6 p hp β hβ).1 z j, ?_⟩
    have hfun : (fun w : Fin p → ℝ => coordPartial (smoothMaxFn β) k w) =
        fun w : Fin p → ℝ => softmaxWt β w k :=
      (statopia_math_node_1599490337_26b631c6 p hp β hβ).2 k
    have hderiv := statopia_math_node_1897111600_7bb83d4b p hp β hβ z k
    have hfd := hderiv.1.fderiv
    have heval : (fderiv ℝ (fun v : Fin p → ℝ => softmaxWt β v k) z) (Pi.single j 1) =
        β * wMatEntry β z j k := by
      rw [hfd]
      exact hderiv.2.2 j
    calc mixedCoordPartial (smoothMaxFn β) j k z
        = (fderiv ℝ (fun w : Fin p → ℝ => coordPartial (smoothMaxFn β) k w) z) (Pi.single j 1) := rfl
      _ = (fderiv ℝ (fun v : Fin p → ℝ => softmaxWt β v k) z) (Pi.single j 1) := by rw [hfun]
      _ = β * wMatEntry β z j k := heval
  exact ⟨hcoord, hnonneg, hsum, fun z => statopia_math_node_494615018_5f6206ad p hp β hβ z⟩
  /- @proof-region region.root.ab6fbb66d713 end -/

end Statlib.Imported

