import Statlib.StatFoundation.Statistics.Asymptotic.ScoreCLT
import Statlib.StatFoundation.Convergence.Resampling.GaussianMaxComparison
import Statlib.StatFoundation.Convergence.AnalysisTools.GaussianMaxAnticoncentration
import Statlib.StatFoundation.Statistics.Asymptotic.LAN
import Statlib.StatFoundation.Convergence.AnalysisTools.SmoothMax
import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import ProverJobs.job_paper_a86aea8c92ff4120874a0fdca6db77c5.Vocabulary
import ProverJobs.job_paper_a86aea8c92ff4120874a0fdca6db77c5.ProvedNodes
import ProverJobs.job_paper_a86aea8c92ff4120874a0fdca6db77c5.Base

namespace PaperProofTasks.job_paper_a86aea8c92ff4120874a0fdca6db77c5

noncomputable section
open scoped BigOperators
namespace Statlib.Imported


theorem paper_a86aea8c92ff4120874a0fdca6db77c5
    (p : ℕ) (hp : 0 < p) (β : ℝ) (hβ : 0 < β) (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g)
    (z : Fin p → ℝ) (j k : Fin p) :
    coordPartial j (coordPartial k (compSmoothMax (p := p) g β)) z
      = deriv (deriv g) (smoothMaxFun β z) * softmaxWt β z j * softmaxWt β z k
        + β * deriv g (smoothMaxFun β z) * softmaxPair β z j k
:= by
  /- @proof-region region.root.e7c0317e1da4 begin -/
  have hg_diff : Differentiable ℝ g :=
    ContDiff.differentiable_iteratedDeriv 0 hg (by norm_num)
  have hg'_diff : Differentiable ℝ (deriv g) := by
    simpa only [iteratedDeriv_one] using
      ContDiff.differentiable_iteratedDeriv 1 hg (by norm_num)
  have hstep1 : ∀ (u : Fin p → ℝ) (c : Fin p),
      coordPartial c (compSmoothMax (p := p) g β) u
        = deriv g (smoothMaxFun β u) * softmaxWt β u c := by
    intro u c
    have houter : HasDerivAt g (deriv g (smoothMaxFun β u)) (smoothMaxFun β u) :=
      (hg_diff (smoothMaxFun β u)).hasDerivAt
    have houter' : HasDerivAt g
        (deriv g (smoothMaxFun β (Function.update u c (u c))))
        (smoothMaxFun β (Function.update u c (u c))) := by
      simpa [Function.update_eq_self] using houter
    have hinner : HasDerivAt (fun t : ℝ => smoothMaxFun β (Function.update u c t))
        (softmaxWt β u c) (u c) :=
      statopia_math_node_2036766001_3e3c9c29 p hp β hβ u c
    have hcomp := HasDerivAt.comp (u c) houter' hinner
    show deriv (fun t : ℝ => g (smoothMaxFun β (Function.update u c t))) (u c)
      = deriv g (smoothMaxFun β u) * softmaxWt β u c
    simpa [Function.comp, Function.update_eq_self] using hcomp.deriv
  have hstep2a : HasDerivAt
      (fun s : ℝ => deriv g (smoothMaxFun β (Function.update z j s)))
      (deriv (deriv g) (smoothMaxFun β z) * softmaxWt β z j) (z j) := by
    have houter : HasDerivAt (deriv g) (deriv (deriv g) (smoothMaxFun β z)) (smoothMaxFun β z) :=
      (hg'_diff (smoothMaxFun β z)).hasDerivAt
    have houter' : HasDerivAt (deriv g)
        (deriv (deriv g) (smoothMaxFun β (Function.update z j (z j))))
        (smoothMaxFun β (Function.update z j (z j))) := by
      simpa [Function.update_eq_self] using houter
    have hinner : HasDerivAt (fun s : ℝ => smoothMaxFun β (Function.update z j s))
        (softmaxWt β z j) (z j) :=
      statopia_math_node_2036766001_3e3c9c29 p hp β hβ z j
    have hcomp := HasDerivAt.comp (z j) houter' hinner
    simpa [Function.comp, Function.update_eq_self] using hcomp
  have hstep2b : HasDerivAt (fun s : ℝ => softmaxWt β (Function.update z j s) k)
      (β * softmaxPair β z j k) (z j) :=
    statopia_math_node_739905703_1f8e5acd p hp β hβ z j k
  have hprod : HasDerivAt
      (fun s : ℝ => deriv g (smoothMaxFun β (Function.update z j s)) * softmaxWt β (Function.update z j s) k)
      ((deriv (deriv g) (smoothMaxFun β z) * softmaxWt β z j) * softmaxWt β z k
        + deriv g (smoothMaxFun β z) * (β * softmaxPair β z j k)) (z j) := by
    have hmul := hstep2a.mul hstep2b
    simpa [Function.update_eq_self] using hmul
  have hfun : (fun t : ℝ => coordPartial k (compSmoothMax (p := p) g β) (Function.update z j t))
      = fun s : ℝ => deriv g (smoothMaxFun β (Function.update z j s)) * softmaxWt β (Function.update z j s) k := by
    funext s
    exact hstep1 (Function.update z j s) k
  show deriv (fun t : ℝ => coordPartial k (compSmoothMax (p := p) g β) (Function.update z j t)) (z j)
    = deriv (deriv g) (smoothMaxFun β z) * softmaxWt β z j * softmaxWt β z k
      + β * deriv g (smoothMaxFun β z) * softmaxPair β z j k
  rw [hfun, hprod.deriv]
  ring
  /- @proof-region region.root.e7c0317e1da4 end -/

end Statlib.Imported

