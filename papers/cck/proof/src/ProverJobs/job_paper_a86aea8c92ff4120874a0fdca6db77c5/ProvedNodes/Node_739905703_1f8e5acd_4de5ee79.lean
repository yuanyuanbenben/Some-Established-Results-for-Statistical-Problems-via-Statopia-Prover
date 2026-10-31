import Statlib.StatFoundation.Statistics.Asymptotic.ScoreCLT
import Statlib.StatFoundation.Convergence.Resampling.GaussianMaxComparison
import Statlib.StatFoundation.Convergence.AnalysisTools.GaussianMaxAnticoncentration
import Statlib.StatFoundation.Statistics.Asymptotic.LAN
import Statlib.StatFoundation.Convergence.AnalysisTools.SmoothMax
import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import ProverJobs.job_paper_a86aea8c92ff4120874a0fdca6db77c5.Vocabulary
import ProverJobs.job_paper_a86aea8c92ff4120874a0fdca6db77c5.Base
import ProverJobs.job_paper_a86aea8c92ff4120874a0fdca6db77c5.ExternalNodes.Node_74989c98448a49bdaf2d
import ProverJobs.job_paper_a86aea8c92ff4120874a0fdca6db77c5.ExternalNodes.Node_649e143f66c04d0caa9a

namespace PaperProofTasks.job_paper_a86aea8c92ff4120874a0fdca6db77c5


open scoped BigOperators
open _root_.PaperProofTasks.job_paper_a86aea8c92ff4120874a0fdca6db77c5.Statlib.Imported

noncomputable section
open scoped BigOperators
namespace Statlib.Imported


set_option autoImplicit false in
theorem statopia_math_node_739905703_1f8e5acd : ∀ (p : ℕ) (hp : 0 < p) (β : ℝ) (hβ : 0 < β) (u : Fin p → ℝ) (j k : Fin p),
    HasDerivAt (fun s : ℝ => softmaxWt β (Function.update u j s) k)
      (β * softmaxPair β u j k) (u j) := by
  /- @proof-region region.target-node.session.8abe0b7b4d4f7a77 begin -/
  intro p hp β hβ u j k
  show HasDerivAt
      (fun s : ℝ => Real.exp (β * (Function.update u j s) k) /
        ∑ l : Fin p, Real.exp (β * (Function.update u j s) l))
      (β * softmaxPair β u j k) (u j)
  have hZne : (∑ l : Fin p, Real.exp (β * u l)) ≠ 0 := by
    haveI : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
    exact ne_of_gt (Finset.sum_pos (fun l _ => Real.exp_pos (β * u l)) Finset.univ_nonempty)
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (β * s)) (Real.exp (β * u j) * β) (u j) := by
    have hlin : HasDerivAt (fun s : ℝ => β * s) β (u j) := by
      simpa using (hasDerivAt_const (u j) β).mul (hasDerivAt_id (u j))
    exact (Real.hasDerivAt_exp (β * u j)).comp (u j) hlin
  have hsum : ∀ s : ℝ, (∑ l : Fin p, Real.exp (β * (Function.update u j s) l))
      = (∑ l : Fin p, Real.exp (β * u l)) + (Real.exp (β * s) - Real.exp (β * u j)) := by
    intro s
    have hkey : ∑ l : Fin p, (Real.exp (β * (Function.update u j s) l) - Real.exp (β * u l))
        = Real.exp (β * s) - Real.exp (β * u j) := by
      have h0 : ∀ b ∈ Finset.univ, b ≠ j → (Real.exp (β * (Function.update u j s) b) - Real.exp (β * u b)) = 0 := by
        intro b _ hb
        rw [Function.update_apply u j s b, if_neg hb]
        ring
      have h1 : j ∉ Finset.univ → (Real.exp (β * (Function.update u j s) j) - Real.exp (β * u j)) = 0 := by
        intro hmem
        exact absurd (Finset.mem_univ j) hmem
      rw [Finset.sum_eq_single j h0 h1, Function.update_self j s u]
    rw [← hkey, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro l _
    ring
  have hden : HasDerivAt (fun s : ℝ => (∑ l : Fin p, Real.exp (β * u l)) + (Real.exp (β * s) - Real.exp (β * u j))) (Real.exp (β * u j) * β) (u j) := by
    have hb : HasDerivAt (fun s : ℝ => (∑ l : Fin p, Real.exp (β * u l)) + (Real.exp (β * s) - Real.exp (β * u j))) (0 + (Real.exp (β * u j) * β - 0)) (u j) :=
      (hasDerivAt_const (u j) (∑ l : Fin p, Real.exp (β * u l))).add (hexp.sub (hasDerivAt_const (u j) (Real.exp (β * u j))))
    have hd : 0 + (Real.exp (β * u j) * β - 0) = Real.exp (β * u j) * β := by ring
    exact hb.congr_deriv hd
  by_cases hk : k = j
  · have hA : (fun s : ℝ => Real.exp (β * (Function.update u j s) k) / ∑ l : Fin p, Real.exp (β * (Function.update u j s) l))
        = fun s : ℝ => Real.exp (β * s) / ((∑ l : Fin p, Real.exp (β * u l)) + (Real.exp (β * s) - Real.exp (β * u j))) := by
      funext s
      rw [hsum s, Function.update_apply u j s k, if_pos hk]
    rw [hA]
    refine (hexp.fun_div hden ?_).congr_deriv ?_
    · simp only [sub_self, add_zero]
      exact hZne
    · unfold softmaxPair softmaxWt
      rw [hk]
      rw [if_pos rfl]
      simp only [sub_self, add_zero]
      field_simp [hZne] <;> ring
  · have hB : (fun s : ℝ => Real.exp (β * (Function.update u j s) k) / ∑ l : Fin p, Real.exp (β * (Function.update u j s) l))
        = fun s : ℝ => Real.exp (β * u k) / ((∑ l : Fin p, Real.exp (β * u l)) + (Real.exp (β * s) - Real.exp (β * u j))) := by
      funext s
      rw [hsum s, Function.update_apply u j s k, if_neg hk]
    rw [hB]
    refine ((hasDerivAt_const (u j) (Real.exp (β * u k))).fun_div hden ?_).congr_deriv ?_
    · simp only [sub_self, add_zero]
      exact hZne
    · unfold softmaxPair softmaxWt
      rw [if_neg (Ne.symm hk)]
      simp only [sub_self, add_zero]
      field_simp [hZne] <;> ring
  /- @proof-region region.target-node.session.8abe0b7b4d4f7a77 end -/

end Statlib.Imported
end

