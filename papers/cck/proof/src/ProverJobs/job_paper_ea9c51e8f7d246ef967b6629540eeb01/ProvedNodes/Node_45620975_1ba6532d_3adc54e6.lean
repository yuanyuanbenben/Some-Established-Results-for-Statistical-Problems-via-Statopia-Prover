import Statlib.StatFoundation.Statistics.Asymptotic.ScoreCLT
import Statlib.StatFoundation.Convergence.Resampling.GaussianMaxComparison
import Statlib.StatFoundation.Convergence.AnalysisTools.GaussianMaxAnticoncentration
import Statlib.StatFoundation.Statistics.Asymptotic.LAN
import Statlib.StatFoundation.Convergence.AnalysisTools.SmoothMax
import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import ProverJobs.job_paper_ea9c51e8f7d246ef967b6629540eeb01.Vocabulary
import ProverJobs.job_paper_ea9c51e8f7d246ef967b6629540eeb01.Base

namespace PaperProofTasks.job_paper_ea9c51e8f7d246ef967b6629540eeb01

open _root_.PaperProofTasks.job_paper_ea9c51e8f7d246ef967b6629540eeb01.Statlib.Imported
open MeasureTheory ProbabilityTheory

namespace Statlib.Imported

open MeasureTheory ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_45620975_1ba6532d : ∀ {p : ℕ} (hp : 0 < p) {beta : ℝ} (hbeta : 0 < beta)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) (M : ℝ)
    (hM : ∀ z : ℝ, |deriv g z| ≤ M),
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Fin p → ℝ,
      |g (Statlib.StatFoundation.Convergence.smoothMax beta (WithLp.toLp 2 z))| ≤
        C * (1 + ∑ j : Fin p, |z j|) := by
  /- @proof-region region.target-node.session.6251a906b82d2389 begin -/
  intro p hp beta hbeta g hg M hM
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hgrow : ∀ y : ℝ, |g y| ≤ |g 0| + M * |y| := by
    intro y
    have hmv : ‖g y - g 0‖ ≤ M * ‖y - 0‖ := by
      apply Convex.norm_image_sub_le_of_norm_deriv_le (f := g) (s := Set.univ) (x := 0) (y := y) (C := M)
      · intro z _
        exact hg.contDiffAt.differentiableAt_one
      · intro z _
        rw [Real.norm_eq_abs]
        exact hM z
      · exact convex_univ
      · exact Set.mem_univ 0
      · exact Set.mem_univ y
    simp only [Real.norm_eq_abs, sub_zero] at hmv
    calc |g y| = |(g y - g 0) + g 0| := by rw [sub_add_cancel]
      _ ≤ |g y - g 0| + |g 0| := by simpa only [Real.norm_eq_abs] using norm_add_le (g y - g 0) (g 0)
      _ ≤ M * |y| + |g 0| := by linarith
      _ = |g 0| + M * |y| := by ring
  have hS_growth : ∀ x : EuclideanSpace ℝ (Fin p),
      |(Statlib.StatFoundation.Convergence.smoothMax beta) x| ≤
        |(Statlib.StatFoundation.Convergence.smoothMax beta) (0 : EuclideanSpace ℝ (Fin p))| + ∑ j : Fin p, |x.ofLp j| := by
    intro x
    have hfderiv : ∀ y : EuclideanSpace ℝ (Fin p),
        HasFDerivAt (Statlib.StatFoundation.Convergence.smoothMax beta)
          ((innerSL ℝ) (WithLp.toLp 2 (fun j => Statlib.StatFoundation.Convergence.softmaxWeight beta y j))) y :=
      fun y => Statlib.StatFoundation.Convergence.smoothMax_gradient_eq_softmax hp hbeta y
    have hfdnorm : ∀ y : EuclideanSpace ℝ (Fin p),
        ‖fderiv ℝ (Statlib.StatFoundation.Convergence.smoothMax beta) y‖ ≤ 1 := by
      intro y
      rw [(hfderiv y).fderiv, innerSL_apply_norm ℝ]
      rw [EuclideanSpace.norm_eq]
      have hw0 : ∀ j : Fin p, 0 ≤ Statlib.StatFoundation.Convergence.softmaxWeight beta y j :=
        (Statlib.StatFoundation.Convergence.softmax_weights_sum_nonneg hp y).1
      have hw1 : ∑ j : Fin p, Statlib.StatFoundation.Convergence.softmaxWeight beta y j = 1 :=
        (Statlib.StatFoundation.Convergence.softmax_weights_sum_nonneg hp y).2
      have hle1 : ∀ j : Fin p, Statlib.StatFoundation.Convergence.softmaxWeight beta y j ≤ 1 := by
        intro j
        have h := Finset.single_le_sum (f := fun k => Statlib.StatFoundation.Convergence.softmaxWeight beta y k) (fun k _ => hw0 k) (Finset.mem_univ j)
        rwa [hw1] at h
      have hcoord : ∀ j : Fin p,
          ‖(WithLp.toLp 2 (fun j => Statlib.StatFoundation.Convergence.softmaxWeight beta y j) : EuclideanSpace ℝ (Fin p)).ofLp j‖
            = Statlib.StatFoundation.Convergence.softmaxWeight beta y j := by
        intro j
        rw [WithLp.ofLp_toLp, Real.norm_eq_abs]
        exact abs_of_nonneg (hw0 j)
      have hsq : ∑ j : Fin p, ‖(WithLp.toLp 2 (fun j => Statlib.StatFoundation.Convergence.softmaxWeight beta y j) : EuclideanSpace ℝ (Fin p)).ofLp j‖ ^ 2
          = ∑ j : Fin p, (Statlib.StatFoundation.Convergence.softmaxWeight beta y j) ^ 2 := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hcoord j]
      have hsum_le : ∑ j : Fin p, ‖(WithLp.toLp 2 (fun j => Statlib.StatFoundation.Convergence.softmaxWeight beta y j) : EuclideanSpace ℝ (Fin p)).ofLp j‖ ^ 2 ≤ 1 := by
        rw [hsq, ← hw1]
        apply Finset.sum_le_sum
        intro j _
        nlinarith [mul_nonneg (hw0 j) (sub_nonneg.mpr (hle1 j))]
      calc √(∑ j : Fin p, ‖(WithLp.toLp 2 (fun j => Statlib.StatFoundation.Convergence.softmaxWeight beta y j) : EuclideanSpace ℝ (Fin p)).ofLp j‖ ^ 2)
          ≤ √1 := Real.sqrt_le_sqrt hsum_le
        _ = 1 := Real.sqrt_one
    have hmv : ‖(Statlib.StatFoundation.Convergence.smoothMax beta) x - (Statlib.StatFoundation.Convergence.smoothMax beta) (0 : EuclideanSpace ℝ (Fin p))‖ ≤ 1 * ‖x - 0‖ := by
      exact @Convex.norm_image_sub_le_of_norm_fderiv_le (EuclideanSpace ℝ (Fin p)) _ _ ℝ ℝ _ _ _ _ _
        (Statlib.StatFoundation.Convergence.smoothMax beta) 1 Set.univ 0 x
        (fun z _ => (hfderiv z).differentiableAt) (fun z _ => hfdnorm z) convex_univ (Set.mem_univ 0) (Set.mem_univ x)
    rw [Real.norm_eq_abs, sub_zero, one_mul] at hmv
    have hnorm : ‖x‖ ≤ ∑ j : Fin p, |x.ofLp j| := by
      rw [EuclideanSpace.norm_eq]
      have hc : ∀ j : Fin p, 0 ≤ |x.ofLp j| := fun j => abs_nonneg _
      have hsq : (∑ j : Fin p, |x.ofLp j|) ^ 2 = ∑ j : Fin p, ∑ k : Fin p, |x.ofLp j| * |x.ofLp k| := by
        rw [pow_two, Finset.sum_mul_sum]
      have hle : ∑ j : Fin p, ‖x.ofLp j‖ ^ 2 ≤ (∑ j : Fin p, |x.ofLp j|) ^ 2 := by
        rw [hsq]
        apply Finset.sum_le_sum
        intro j _
        have h1 : ‖x.ofLp j‖ ^ 2 = |x.ofLp j| * |x.ofLp j| := by
          rw [Real.norm_eq_abs]; ring
        rw [h1]
        exact Finset.single_le_sum (fun k _ => mul_nonneg (hc j) (hc k)) (Finset.mem_univ j)
      calc √(∑ j : Fin p, ‖x.ofLp j‖ ^ 2) ≤ √((∑ j : Fin p, |x.ofLp j|) ^ 2) := Real.sqrt_le_sqrt hle
        _ = ∑ j : Fin p, |x.ofLp j| := Real.sqrt_sq (Finset.sum_nonneg (fun j _ => hc j))
    calc |(Statlib.StatFoundation.Convergence.smoothMax beta) x|
        = |((Statlib.StatFoundation.Convergence.smoothMax beta) x - (Statlib.StatFoundation.Convergence.smoothMax beta) (0 : EuclideanSpace ℝ (Fin p))) + (Statlib.StatFoundation.Convergence.smoothMax beta) (0 : EuclideanSpace ℝ (Fin p))| := by rw [sub_add_cancel]
      _ ≤ |(Statlib.StatFoundation.Convergence.smoothMax beta) x - (Statlib.StatFoundation.Convergence.smoothMax beta) (0 : EuclideanSpace ℝ (Fin p))| + |(Statlib.StatFoundation.Convergence.smoothMax beta) (0 : EuclideanSpace ℝ (Fin p))| := by
          simpa only [Real.norm_eq_abs] using norm_add_le ((Statlib.StatFoundation.Convergence.smoothMax beta) x - (Statlib.StatFoundation.Convergence.smoothMax beta) (0 : EuclideanSpace ℝ (Fin p))) ((Statlib.StatFoundation.Convergence.smoothMax beta) (0 : EuclideanSpace ℝ (Fin p)))
      _ ≤ ‖x‖ + |(Statlib.StatFoundation.Convergence.smoothMax beta) (0 : EuclideanSpace ℝ (Fin p))| := by linarith
      _ ≤ (∑ j : Fin p, |x.ofLp j|) + |(Statlib.StatFoundation.Convergence.smoothMax beta) (0 : EuclideanSpace ℝ (Fin p))| := by linarith
      _ = |(Statlib.StatFoundation.Convergence.smoothMax beta) (0 : EuclideanSpace ℝ (Fin p))| + ∑ j : Fin p, |x.ofLp j| := by ring
  refine ⟨|g 0| + M * |(Statlib.StatFoundation.Convergence.smoothMax beta) (0 : EuclideanSpace ℝ (Fin p))| + M, ?_, ?_⟩
  · have h1 : 0 ≤ |g 0| + M * |(Statlib.StatFoundation.Convergence.smoothMax beta) (0 : EuclideanSpace ℝ (Fin p))| :=
      add_nonneg (abs_nonneg _) (mul_nonneg hM0 (abs_nonneg _))
    linarith
  · intro z
    have hSz : |(Statlib.StatFoundation.Convergence.smoothMax beta) (WithLp.toLp 2 z)| ≤
        |(Statlib.StatFoundation.Convergence.smoothMax beta) (0 : EuclideanSpace ℝ (Fin p))| + ∑ j : Fin p, |z j| := by
      have h := hS_growth (WithLp.toLp 2 z)
      simpa using h
    have hA0 : 0 ≤ |g 0| + M * |(Statlib.StatFoundation.Convergence.smoothMax beta) (0 : EuclideanSpace ℝ (Fin p))| :=
      add_nonneg (abs_nonneg _) (mul_nonneg hM0 (abs_nonneg _))
    have hs0 : 0 ≤ ∑ j : Fin p, |z j| := Finset.sum_nonneg (fun j _ => abs_nonneg _)
    have hgoal : |g 0| + M * (|(Statlib.StatFoundation.Convergence.smoothMax beta) (0 : EuclideanSpace ℝ (Fin p))| + ∑ j : Fin p, |z j|)
        ≤ (|g 0| + M * |(Statlib.StatFoundation.Convergence.smoothMax beta) (0 : EuclideanSpace ℝ (Fin p))| + M) * (1 + ∑ j : Fin p, |z j|) := by
      have hAs : 0 ≤ (|g 0| + M * |(Statlib.StatFoundation.Convergence.smoothMax beta) (0 : EuclideanSpace ℝ (Fin p))|) * ∑ j : Fin p, |z j| :=
        mul_nonneg hA0 hs0
      nlinarith [hAs, hM0]
    calc |g ((Statlib.StatFoundation.Convergence.smoothMax beta) (WithLp.toLp 2 z))|
        ≤ |g 0| + M * |(Statlib.StatFoundation.Convergence.smoothMax beta) (WithLp.toLp 2 z)| := hgrow _
      _ ≤ |g 0| + M * (|(Statlib.StatFoundation.Convergence.smoothMax beta) (0 : EuclideanSpace ℝ (Fin p))| + ∑ j : Fin p, |z j|) := by linarith [mul_le_mul_of_nonneg_left hSz hM0]
      _ ≤ (|g 0| + M * |(Statlib.StatFoundation.Convergence.smoothMax beta) (0 : EuclideanSpace ℝ (Fin p))| + M) * (1 + ∑ j : Fin p, |z j|) := hgoal
  /- @proof-region region.target-node.session.6251a906b82d2389 end -/

end Statlib.Imported

