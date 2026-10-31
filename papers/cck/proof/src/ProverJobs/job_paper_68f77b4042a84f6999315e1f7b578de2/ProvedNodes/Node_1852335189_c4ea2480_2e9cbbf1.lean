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
theorem statopia_math_node_1852335189_c4ea2480 : ∀ (p : ℕ) (hp : 0 < p) (β : ℝ) (hβ : 0 < β) (z : Fin p → ℝ),
    (0 < ∑ m : Fin p, Real.exp (β * z m)) ∧
      (∀ j : Fin p, 0 ≤ softmaxWt β z j ∧ softmaxWt β z j ≤ 1) ∧
      (∑ j : Fin p, softmaxWt β z j) = 1 := by
  /- @proof-region region.target-node.session.e6829c22d168add6 begin -/
  intro p hp β hβ z
  have hterm : ∀ m : Fin p, 0 < Real.exp (β * z m) := fun m => Real.exp_pos _
  have hSpos : 0 < ∑ m : Fin p, Real.exp (β * z m) := by
    have hne : (Finset.univ : Finset (Fin p)).Nonempty := ⟨⟨0, hp⟩, Finset.mem_univ _⟩
    have hpos : ∀ m ∈ (Finset.univ : Finset (Fin p)), 0 < Real.exp (β * z m) :=
      fun m _ => hterm m
    first
      | exact Finset.sum_pos (s := Finset.univ) (f := fun m : Fin p => Real.exp (β * z m)) hne hpos
      | exact Finset.sum_pos (s := Finset.univ) (f := fun m : Fin p => Real.exp (β * z m)) hpos hne
  have hSne : (∑ m : Fin p, Real.exp (β * z m)) ≠ 0 := ne_of_gt hSpos
  have hsum1 : (∑ j : Fin p, softmaxWt β z j) = 1 := by
    simp only [softmaxWt]
    rw [← Finset.sum_div]
    exact div_self hSne
  have hnonneg : ∀ m ∈ (Finset.univ : Finset (Fin p)), (0 : ℝ) ≤ softmaxWt β z m := by
    intro m _
    exact div_nonneg (le_of_lt (hterm m)) (le_of_lt hSpos)
  refine ⟨hSpos, ?_, hsum1⟩
  intro j
  refine ⟨div_nonneg (le_of_lt (hterm j)) (le_of_lt hSpos), ?_⟩
  have hle : softmaxWt β z j ≤ ∑ m : Fin p, softmaxWt β z m := by
    first
      | exact Finset.single_le_sum (s := Finset.univ) (f := fun m : Fin p => softmaxWt β z m) hnonneg (Finset.mem_univ j)
      | exact Finset.single_le_sum (s := Finset.univ) (f := fun m : Fin p => softmaxWt β z m) (Finset.mem_univ j) hnonneg
  rw [← hsum1]
  exact hle
  /- @proof-region region.target-node.session.e6829c22d168add6 end -/

end Statlib.Imported

