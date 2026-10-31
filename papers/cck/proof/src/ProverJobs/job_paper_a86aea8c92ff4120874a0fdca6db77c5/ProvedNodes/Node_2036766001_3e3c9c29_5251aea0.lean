import Statlib.StatFoundation.Statistics.Asymptotic.ScoreCLT
import Statlib.StatFoundation.Convergence.Resampling.GaussianMaxComparison
import Statlib.StatFoundation.Convergence.AnalysisTools.GaussianMaxAnticoncentration
import Statlib.StatFoundation.Statistics.Asymptotic.LAN
import Statlib.StatFoundation.Convergence.AnalysisTools.SmoothMax
import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import ProverJobs.job_paper_a86aea8c92ff4120874a0fdca6db77c5.Vocabulary
import ProverJobs.job_paper_a86aea8c92ff4120874a0fdca6db77c5.Base
import ProverJobs.job_paper_a86aea8c92ff4120874a0fdca6db77c5.ExternalNodes.Node_649e143f66c04d0caa9a

namespace PaperProofTasks.job_paper_a86aea8c92ff4120874a0fdca6db77c5

open scoped BigOperators
open _root_.PaperProofTasks.job_paper_a86aea8c92ff4120874a0fdca6db77c5.Statlib.Imported

noncomputable section
open scoped BigOperators
namespace Statlib.Imported


set_option autoImplicit false in
theorem statopia_math_node_2036766001_3e3c9c29 : ∀ (p : ℕ) (hp : 0 < p) (β : ℝ) (hβ : 0 < β) (u : Fin p → ℝ) (k : Fin p),
    HasDerivAt (fun t : ℝ => smoothMaxFun β (Function.update u k t))
      (softmaxWt β u k) (u k) := by
  /- @proof-region region.target-node.session.6bb802bcff1b6fd0 begin -/
  intro p hp β hβ u k
  set A : ℝ := ∑ l ∈ Finset.univ.erase k, Real.exp (β * u l) with hA
  have hA_nonneg : 0 ≤ A := by
    rw [hA]
    exact Finset.sum_nonneg (fun l _ => (Real.exp_pos _).le)
  have hupd : Function.update u k (u k) = u := Function.update_eq_self k u
  have hsum : ∀ t : ℝ, (∑ l : Fin p, Real.exp (β * Function.update u k t l))
      = Real.exp (β * t) + A := by
    intro t
    rw [← Finset.insert_erase (Finset.mem_univ k), Finset.sum_insert (by simp)]
    rw [hA, Function.update_self]
    congr 1
    apply Finset.sum_congr rfl
    intro l hl
    rw [Finset.mem_erase] at hl
    rw [Function.update_apply, if_neg hl.1]
  have hS : (∑ l : Fin p, Real.exp (β * u l)) = Real.exp (β * u k) + A := by
    have h := hsum (u k)
    rwa [hupd] at h
  have hslice : (fun t : ℝ => smoothMaxFun β (Function.update u k t))
      = fun t : ℝ => β⁻¹ * Real.log (Real.exp (β * t) + A) := by
    funext t
    show β⁻¹ * Real.log (∑ l : Fin p, Real.exp (β * Function.update u k t l))
      = β⁻¹ * Real.log (Real.exp (β * t) + A)
    rw [hsum t]
  have hpos : 0 < Real.exp (β * u k) + A := by
    have h1 : 0 < Real.exp (β * u k) := Real.exp_pos _
    linarith
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (β * t))
      (Real.exp (β * u k) * β) (u k) := by
    have hlin : HasDerivAt (fun t : ℝ => β * t) β (u k) :=
      hasDerivAt_const_mul β
    exact hlin.exp
  have hlog : HasDerivAt (fun t : ℝ => Real.log (Real.exp (β * t) + A))
      ((Real.exp (β * u k) * β) / (Real.exp (β * u k) + A)) (u k) := by
    have hadd : HasDerivAt (fun t : ℝ => Real.exp (β * t) + A)
        (Real.exp (β * u k) * β) (u k) := hexp.add_const A
    exact hadd.log (ne_of_gt hpos)
  have hscaled : HasDerivAt (fun t : ℝ => β⁻¹ * Real.log (Real.exp (β * t) + A))
      (β⁻¹ * ((Real.exp (β * u k) * β) / (Real.exp (β * u k) + A))) (u k) :=
    hlog.const_mul β⁻¹
  have hβinv : β⁻¹ * β = (1 : ℝ) := inv_mul_cancel₀ (ne_of_gt hβ)
  have hmon : β⁻¹ * (Real.exp (β * u k) * β) = Real.exp (β * u k) := by
    rw [mul_comm (Real.exp (β * u k)) β, ← mul_assoc, hβinv, one_mul]
  have hval : β⁻¹ * ((Real.exp (β * u k) * β) / (Real.exp (β * u k) + A))
      = Real.exp (β * u k) / (Real.exp (β * u k) + A) := by
    rw [div_eq_mul_inv, ← mul_assoc, hmon, div_eq_mul_inv]
  have hwt : softmaxWt β u k = Real.exp (β * u k) / (Real.exp (β * u k) + A) := by
    show Real.exp (β * u k) / (∑ l : Fin p, Real.exp (β * u l))
      = Real.exp (β * u k) / (Real.exp (β * u k) + A)
    rw [hS]
  rw [hslice, hwt]
  rw [hval] at hscaled
  exact hscaled
  /- @proof-region region.target-node.session.6bb802bcff1b6fd0 end -/

end Statlib.Imported
end

