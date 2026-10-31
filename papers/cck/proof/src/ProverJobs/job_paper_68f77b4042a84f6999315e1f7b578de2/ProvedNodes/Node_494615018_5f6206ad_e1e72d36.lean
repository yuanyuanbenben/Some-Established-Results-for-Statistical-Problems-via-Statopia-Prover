import Statlib.StatFoundation.Statistics.Asymptotic.ScoreCLT
import Statlib.StatFoundation.Convergence.Resampling.GaussianMaxComparison
import Statlib.StatFoundation.Convergence.AnalysisTools.GaussianMaxAnticoncentration
import Statlib.StatFoundation.Statistics.Asymptotic.LAN
import Statlib.StatFoundation.Convergence.AnalysisTools.SmoothMax
import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import ProverJobs.job_paper_68f77b4042a84f6999315e1f7b578de2.Vocabulary
import ProverJobs.job_paper_68f77b4042a84f6999315e1f7b578de2.Base
import ProverJobs.job_paper_68f77b4042a84f6999315e1f7b578de2.ProvedNodes.Node_1852335189_c4ea2480_2e9cbbf1

namespace PaperProofTasks.job_paper_68f77b4042a84f6999315e1f7b578de2

open _root_.PaperProofTasks.job_paper_68f77b4042a84f6999315e1f7b578de2.Statlib.Imported
open scoped BigOperators

namespace Statlib.Imported

open scoped BigOperators

set_option autoImplicit false in
theorem statopia_math_node_494615018_5f6206ad : ∀ (p : ℕ) (hp : 0 < p) (β : ℝ) (hβ : 0 < β)
    (z : Fin p → ℝ),
    (∑ a : Fin p, ∑ b : Fin p, |wMatEntry β z a b|) ≤ 2 := by
  /- @proof-region region.target-node.session.56395f111f1bde25 begin -/
  intro p hp β hβ z
  obtain ⟨hSpos, hbounds, hsum⟩ := statopia_math_node_1852335189_c4ea2480 p hp β hβ z
  have hstep : ∀ a b : Fin p,
      |wMatEntry β z a b| ≤ softmaxWt β z a * softmaxWt β z b +
        (if a = b then softmaxWt β z a else 0) := by
    intro a b
    by_cases hab : a = b
    · have hb1 : 0 ≤ softmaxWt β z b := (hbounds b).1
      have hb2 : softmaxWt β z b ≤ 1 := (hbounds b).2
      have hsq : 0 ≤ softmaxWt β z b * softmaxWt β z b := mul_nonneg hb1 hb1
      have e1 : (if a = b then (1 : ℝ) else 0) = 1 := if_pos hab
      have e2 : (if a = b then softmaxWt β z a else 0) = softmaxWt β z a := if_pos hab
      unfold wMatEntry
      rw [e1, e2, one_mul, hab]
      have hnn : (0 : ℝ) ≤ softmaxWt β z b - softmaxWt β z b * softmaxWt β z b := by
        nlinarith
      rw [abs_of_nonneg hnn]
      linarith
    · have ha1 : 0 ≤ softmaxWt β z a := (hbounds a).1
      have hb1 : 0 ≤ softmaxWt β z b := (hbounds b).1
      have hnn : 0 ≤ softmaxWt β z a * softmaxWt β z b := mul_nonneg ha1 hb1
      have e1 : (if a = b then (1 : ℝ) else 0) = 0 := if_neg hab
      have e2 : (if a = b then softmaxWt β z a else 0) = 0 := if_neg hab
      have hval : wMatEntry β z a b = -(softmaxWt β z a * softmaxWt β z b) := by
        unfold wMatEntry
        rw [e1, zero_mul, zero_sub]
      rw [hval, e2, abs_neg, abs_of_nonneg hnn]
      linarith
  have hsplit : (∑ a : Fin p, ∑ b : Fin p,
        (softmaxWt β z a * softmaxWt β z b + (if a = b then softmaxWt β z a else 0))) =
      (∑ a : Fin p, softmaxWt β z a) * (∑ b : Fin p, softmaxWt β z b) +
        ∑ a : Fin p, softmaxWt β z a := by
    have hinner : ∀ a : Fin p, ∑ b : Fin p,
        (softmaxWt β z a * softmaxWt β z b + (if a = b then softmaxWt β z a else 0)) =
        softmaxWt β z a * (∑ b : Fin p, softmaxWt β z b) + softmaxWt β z a := by
      intro a
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp
    simp only [hinner, Finset.sum_add_distrib, Finset.sum_mul]
  calc ∑ a : Fin p, ∑ b : Fin p, |wMatEntry β z a b|
      ≤ ∑ a : Fin p, ∑ b : Fin p,
          (softmaxWt β z a * softmaxWt β z b + (if a = b then softmaxWt β z a else 0)) :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hstep a b
    _ = (∑ a : Fin p, softmaxWt β z a) * (∑ b : Fin p, softmaxWt β z b) +
          ∑ a : Fin p, softmaxWt β z a := hsplit
    _ = 2 := by
        rw [hsum]
        norm_num
  /- @proof-region region.target-node.session.56395f111f1bde25 end -/

end Statlib.Imported

