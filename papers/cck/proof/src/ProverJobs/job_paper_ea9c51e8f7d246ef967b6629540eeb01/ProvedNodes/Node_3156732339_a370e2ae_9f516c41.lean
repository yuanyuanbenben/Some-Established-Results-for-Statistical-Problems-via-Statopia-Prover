import Statlib.StatFoundation.Statistics.Asymptotic.ScoreCLT
import Statlib.StatFoundation.Convergence.Resampling.GaussianMaxComparison
import Statlib.StatFoundation.Convergence.AnalysisTools.GaussianMaxAnticoncentration
import Statlib.StatFoundation.Statistics.Asymptotic.LAN
import Statlib.StatFoundation.Convergence.AnalysisTools.SmoothMax
import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import ProverJobs.job_paper_ea9c51e8f7d246ef967b6629540eeb01.Vocabulary
import ProverJobs.job_paper_ea9c51e8f7d246ef967b6629540eeb01.Base
import ProverJobs.job_paper_ea9c51e8f7d246ef967b6629540eeb01.ExternalNodes.Node_2f43420c7b66475da0e6
import ProverJobs.job_paper_ea9c51e8f7d246ef967b6629540eeb01.ExternalNodes.Node_af0332c83cb34e8cac43

namespace PaperProofTasks.job_paper_ea9c51e8f7d246ef967b6629540eeb01


open _root_.PaperProofTasks.job_paper_ea9c51e8f7d246ef967b6629540eeb01.Statlib.Imported
open MeasureTheory ProbabilityTheory
open PaperProofTasks.job_paper_a86aea8c92ff4120874a0fdca6db77c5.Statlib.Imported
open scoped BigOperators

namespace Statlib.Imported

open MeasureTheory ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_3156732339_a370e2ae : ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℕ) (hp : 0 < p)
    (Z : Ω → Fin p → ℝ) (hZ : Measurable Z)
    (β : ℝ) (hβ : 0 < β)
    (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g)
    (hg1 : BddAbove (Set.range fun y : ℝ => |deriv g y|))
    (hg2 : BddAbove (Set.range fun y : ℝ => |deriv (deriv g) y|)),
    (∀ z : Fin p → ℝ,
        (∑ j : Fin p, ∑ k : Fin p,
            |coordPartial j (coordPartial k (compSmoothMax (p := p) g β)) z|) ≤
          supNormR (deriv (deriv g)) + 2 * β * supNormR (deriv g)) ∧
      (∀ j k : Fin p,
          Integrable (fun ω : Ω =>
            coordPartial j (coordPartial k (compSmoothMax (p := p) g β)) (Z ω)) μ) ∧
        (∑ j : Fin p, ∑ k : Fin p,
            |∫ ω, coordPartial j (coordPartial k (compSmoothMax (p := p) g β)) (Z ω) ∂μ|) ≤
          supNormR (deriv (deriv g)) + 2 * β * supNormR (deriv g) := by
  /- @proof-region region.target-node.session.cd9a926b129f4537 begin -/
  intro Ω instΩ μ instμ p hp Z hZ β hβ g hg hg1 hg2
  have hpt : ∀ z : Fin p → ℝ,
      (∑ j : Fin p, ∑ k : Fin p,
          |coordPartial j (coordPartial k (compSmoothMax (p := p) g β)) z|) ≤
        supNormR (deriv (deriv g)) + 2 * β * supNormR (deriv g) := by
    intro z
    have hb := PaperProofTasks.job_paper_68f77b4042a84f6999315e1f7b578de2.Statlib.Imported.paper_68f77b4042a84f6999315e1f7b578de2 p hp β hβ
    have hsum : (∑ j : Fin p, softmaxWt β z j) = 1 := hb.2.2.1 z
    have hw : (∑ a : Fin p, ∑ b : Fin p, |softmaxPair β z a b|) ≤ 2 := hb.2.2.2 z
    have hnn : ∀ j : Fin p, 0 ≤ softmaxWt β z j := fun j => hb.2.1 z j
    have hhess := paper_a86aea8c92ff4120874a0fdca6db77c5 p hp β hβ g hg
    have hg1' : |deriv g (smoothMaxFun β z)| ≤ supNormR (deriv g) := le_ciSup hg1 (smoothMaxFun β z)
    have hg2' : |deriv (deriv g) (smoothMaxFun β z)| ≤ supNormR (deriv (deriv g)) := le_ciSup hg2 (smoothMaxFun β z)
    have hbound : ∀ j k : Fin p,
        |coordPartial j (coordPartial k (compSmoothMax (p := p) g β)) z|
        ≤ |deriv (deriv g) (smoothMaxFun β z)| * softmaxWt β z j * softmaxWt β z k
          + β * |deriv g (smoothMaxFun β z)| * |softmaxPair β z j k| := by
      have htri : ∀ a b : ℝ, |a + b| ≤ |a| + |b| := by
        intro a b
        rw [abs_le]
        exact ⟨by linarith [neg_abs_le a, neg_abs_le b],
               by linarith [le_abs_self a, le_abs_self b]⟩
      intro j k
      rw [hhess z j k]
      calc |(deriv (deriv g) (smoothMaxFun β z) * softmaxWt β z j) * softmaxWt β z k
              + (β * deriv g (smoothMaxFun β z)) * softmaxPair β z j k|
          ≤ |(deriv (deriv g) (smoothMaxFun β z) * softmaxWt β z j) * softmaxWt β z k|
              + |(β * deriv g (smoothMaxFun β z)) * softmaxPair β z j k| := htri _ _
        _ = |deriv (deriv g) (smoothMaxFun β z)| * softmaxWt β z j * softmaxWt β z k
              + β * |deriv g (smoothMaxFun β z)| * |softmaxPair β z j k| := by
            simp only [abs_mul, abs_of_nonneg (hnn j), abs_of_nonneg (hnn k), abs_of_pos hβ]
    have h1 : (∑ j : Fin p, ∑ k : Fin p, |deriv (deriv g) (smoothMaxFun β z)| * softmaxWt β z j * softmaxWt β z k) = |deriv (deriv g) (smoothMaxFun β z)| := by
      rw [← Finset.sum_mul_sum, ← Finset.mul_sum]
      simp only [hsum, mul_one]
    have h2 : (∑ j : Fin p, ∑ k : Fin p, β * |deriv g (smoothMaxFun β z)| * |softmaxPair β z j k|) = β * |deriv g (smoothMaxFun β z)| * (∑ j : Fin p, ∑ k : Fin p, |softmaxPair β z j k|) := by
      simp_rw [← Finset.mul_sum]
    have h2le : (∑ j : Fin p, ∑ k : Fin p, β * |deriv g (smoothMaxFun β z)| * |softmaxPair β z j k|) ≤ 2 * β * |deriv g (smoothMaxFun β z)| := by
      rw [h2]
      calc β * |deriv g (smoothMaxFun β z)| * (∑ j : Fin p, ∑ k : Fin p, |softmaxPair β z j k|)
          ≤ β * |deriv g (smoothMaxFun β z)| * 2 := by
            apply mul_le_mul_of_nonneg_left hw
            exact mul_nonneg (le_of_lt hβ) (abs_nonneg _)
        _ = 2 * β * |deriv g (smoothMaxFun β z)| := by ring
    have hmain : (∑ j : Fin p, ∑ k : Fin p, |coordPartial j (coordPartial k (compSmoothMax (p := p) g β)) z|)
        ≤ |deriv (deriv g) (smoothMaxFun β z)| + 2 * β * |deriv g (smoothMaxFun β z)| := by
      calc (∑ j : Fin p, ∑ k : Fin p, |coordPartial j (coordPartial k (compSmoothMax (p := p) g β)) z|)
          ≤ (∑ j : Fin p, ∑ k : Fin p, (|deriv (deriv g) (smoothMaxFun β z)| * softmaxWt β z j * softmaxWt β z k + β * |deriv g (smoothMaxFun β z)| * |softmaxPair β z j k|)) := by
            apply Finset.sum_le_sum
            intro j _
            apply Finset.sum_le_sum
            intro k _
            exact hbound j k
        _ = (∑ j : Fin p, ∑ k : Fin p, |deriv (deriv g) (smoothMaxFun β z)| * softmaxWt β z j * softmaxWt β z k)
            + (∑ j : Fin p, ∑ k : Fin p, β * |deriv g (smoothMaxFun β z)| * |softmaxPair β z j k|) := by
            simp_rw [Finset.sum_add_distrib]
        _ = |deriv (deriv g) (smoothMaxFun β z)| + (∑ j : Fin p, ∑ k : Fin p, β * |deriv g (smoothMaxFun β z)| * |softmaxPair β z j k|) := by
            rw [h1]
        _ ≤ |deriv (deriv g) (smoothMaxFun β z)| + 2 * β * |deriv g (smoothMaxFun β z)| := by
            linarith [h2le]
    have hfin : |deriv (deriv g) (smoothMaxFun β z)| + 2 * β * |deriv g (smoothMaxFun β z)| ≤ supNormR (deriv (deriv g)) + 2 * β * supNormR (deriv g) := by
      have hG : 2 * β * |deriv g (smoothMaxFun β z)| ≤ 2 * β * supNormR (deriv g) := by
        have h2β : (0:ℝ) ≤ 2 * β := by linarith [hβ]
        calc 2 * β * |deriv g (smoothMaxFun β z)| = (2 * β) * |deriv g (smoothMaxFun β z)| := by ring
          _ ≤ (2 * β) * supNormR (deriv g) := mul_le_mul_of_nonneg_left hg1' h2β
          _ = 2 * β * supNormR (deriv g) := by ring
      linarith [hg2', hG]
    exact le_trans hmain hfin
  have hint : ∀ j k : Fin p,
      Integrable (fun ω : Ω =>
        coordPartial j (coordPartial k (compSmoothMax (p := p) g β)) (Z ω)) μ := by
    intro j k
    have hmeas : Measurable (fun z : Fin p → ℝ =>
        coordPartial j (coordPartial k (compSmoothMax (p := p) g β)) z) := by
      have hfun : (fun z : Fin p → ℝ =>
            coordPartial j (coordPartial k (compSmoothMax (p := p) g β)) z)
          = (fun z : Fin p → ℝ =>
              deriv (deriv g) (smoothMaxFun β z) * softmaxWt β z j * softmaxWt β z k
                + β * deriv g (smoothMaxFun β z) * softmaxPair β z j k) := by
        funext z
        exact paper_a86aea8c92ff4120874a0fdca6db77c5 p hp β hβ g hg z j k
      rw [hfun]
      simp only [smoothMaxFun, softmaxWt, softmaxPair]
      fun_prop
    have hbdd : ∀ z : Fin p → ℝ,
        ‖coordPartial j (coordPartial k (compSmoothMax (p := p) g β)) z‖ ≤
          supNormR (deriv (deriv g)) + 2 * β * supNormR (deriv g) := by
      intro z
      rw [Real.norm_eq_abs]
      have h1 : |coordPartial j (coordPartial k (compSmoothMax (p := p) g β)) z| ≤
          ∑ k' : Fin p, |coordPartial j (coordPartial k' (compSmoothMax (p := p) g β)) z| :=
        Finset.single_le_sum
          (f := fun k' => |coordPartial j (coordPartial k' (compSmoothMax (p := p) g β)) z|)
          (fun k' _ => abs_nonneg _) (Finset.mem_univ k)
      have h2 : (∑ k' : Fin p, |coordPartial j (coordPartial k' (compSmoothMax (p := p) g β)) z|) ≤
          ∑ j' : Fin p, ∑ k' : Fin p, |coordPartial j' (coordPartial k' (compSmoothMax (p := p) g β)) z| :=
        Finset.single_le_sum
          (f := fun j' => ∑ k', |coordPartial j' (coordPartial k' (compSmoothMax (p := p) g β)) z|)
          (fun j' _ => Finset.sum_nonneg (fun k' _ => abs_nonneg _)) (Finset.mem_univ j)
      exact le_trans (le_trans h1 h2) (hpt z)
    exact MeasureTheory.Integrable.of_bound (hmeas.comp hZ).aestronglyMeasurable
      (supNormR (deriv (deriv g)) + 2 * β * supNormR (deriv g))
      (Filter.Eventually.of_forall (fun ω => hbdd (Z ω)))
  refine ⟨hpt, hint, ?_⟩
  · have hAbsK : ∀ j k : Fin p, Integrable (fun ω : Ω =>
        |coordPartial j (coordPartial k (compSmoothMax (p := p) g β)) (Z ω)|) μ := by
      intro j k
      simpa only [Real.norm_eq_abs] using (hint j k).norm
    have hIntK : ∀ j : Fin p, Integrable (fun ω : Ω =>
        ∑ k : Fin p, |coordPartial j (coordPartial k (compSmoothMax (p := p) g β)) (Z ω)|) μ := by
      intro j
      exact MeasureTheory.integrable_finset_sum Finset.univ (fun k _ => hAbsK j k)
    have hIntAll : Integrable (fun ω : Ω =>
        ∑ j : Fin p, ∑ k : Fin p, |coordPartial j (coordPartial k (compSmoothMax (p := p) g β)) (Z ω)|) μ :=
      MeasureTheory.integrable_finset_sum Finset.univ (fun j _ => hIntK j)
    have heq : (∫ ω : Ω, ∑ j : Fin p, ∑ k : Fin p,
          |coordPartial j (coordPartial k (compSmoothMax (p := p) g β)) (Z ω)| ∂μ)
        = ∑ j : Fin p, ∑ k : Fin p,
          ∫ ω : Ω, |coordPartial j (coordPartial k (compSmoothMax (p := p) g β)) (Z ω)| ∂μ := by
      have e1 : (∫ ω : Ω, ∑ j : Fin p, (∑ k : Fin p,
            |coordPartial j (coordPartial k (compSmoothMax (p := p) g β)) (Z ω)|) ∂μ)
          = ∑ j : Fin p, (∫ ω : Ω, ∑ k : Fin p,
            |coordPartial j (coordPartial k (compSmoothMax (p := p) g β)) (Z ω)| ∂μ) :=
        MeasureTheory.integral_finset_sum Finset.univ
          (f := fun j (ω : Ω) => ∑ k : Fin p, |coordPartial j (coordPartial k (compSmoothMax (p := p) g β)) (Z ω)|)
          (fun j _ => hIntK j)
      have e2 : ∀ j : Fin p, (∫ ω : Ω, ∑ k : Fin p,
            |coordPartial j (coordPartial k (compSmoothMax (p := p) g β)) (Z ω)| ∂μ)
          = ∑ k : Fin p, ∫ ω : Ω, |coordPartial j (coordPartial k (compSmoothMax (p := p) g β)) (Z ω)| ∂μ := fun j =>
        MeasureTheory.integral_finset_sum Finset.univ
          (f := fun k (ω : Ω) => |coordPartial j (coordPartial k (compSmoothMax (p := p) g β)) (Z ω)|)
          (fun k _ => hAbsK j k)
      rw [e1]
      exact Finset.sum_congr rfl (fun j _ => e2 j)
    calc (∑ j : Fin p, ∑ k : Fin p, |∫ ω : Ω, coordPartial j (coordPartial k (compSmoothMax (p := p) g β)) (Z ω) ∂μ|)
        ≤ (∑ j : Fin p, ∑ k : Fin p, ∫ ω : Ω, |coordPartial j (coordPartial k (compSmoothMax (p := p) g β)) (Z ω)| ∂μ) := by
          apply Finset.sum_le_sum
          intro j _
          apply Finset.sum_le_sum
          intro k _
          simpa only [Real.norm_eq_abs] using MeasureTheory.norm_integral_le_integral_norm (fun ω => coordPartial j (coordPartial k (compSmoothMax (p := p) g β)) (Z ω))
      _ = (∫ ω : Ω, ∑ j : Fin p, ∑ k : Fin p, |coordPartial j (coordPartial k (compSmoothMax (p := p) g β)) (Z ω)| ∂μ) := heq.symm
      _ ≤ (∫ ω : Ω, (supNormR (deriv (deriv g)) + 2 * β * supNormR (deriv g)) ∂μ) := by
          apply MeasureTheory.integral_mono
          · exact hIntAll
          · exact MeasureTheory.integrable_const _
          · intro ω
            exact hpt (Z ω)
      _ = supNormR (deriv (deriv g)) + 2 * β * supNormR (deriv g) := by
          rw [MeasureTheory.integral_const]
          simp
  /- @proof-region region.target-node.session.cd9a926b129f4537 end -/

end Statlib.Imported

