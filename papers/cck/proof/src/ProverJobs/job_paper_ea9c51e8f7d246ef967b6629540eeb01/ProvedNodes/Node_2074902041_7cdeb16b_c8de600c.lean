import Statlib.StatFoundation.Statistics.Asymptotic.ScoreCLT
import Statlib.StatFoundation.Convergence.Resampling.GaussianMaxComparison
import Statlib.StatFoundation.Convergence.AnalysisTools.GaussianMaxAnticoncentration
import Statlib.StatFoundation.Statistics.Asymptotic.LAN
import Statlib.StatFoundation.Convergence.AnalysisTools.SmoothMax
import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import ProverJobs.job_paper_ea9c51e8f7d246ef967b6629540eeb01.Vocabulary
import ProverJobs.job_paper_ea9c51e8f7d246ef967b6629540eeb01.Base
import ProverJobs.job_paper_ea9c51e8f7d246ef967b6629540eeb01.ProvedNodes.Node_1854214930_5c94c0df_e3ca69c5
import ProverJobs.job_paper_ea9c51e8f7d246ef967b6629540eeb01.ProvedNodes.Node_1904015730_8e8aa481_1d108aa5
import ProverJobs.job_paper_ea9c51e8f7d246ef967b6629540eeb01.ProvedNodes.Node_2606212885_28c76b68_e993dd06
import ProverJobs.job_paper_ea9c51e8f7d246ef967b6629540eeb01.ProvedNodes.Node_3156732339_a370e2ae_9f516c41
import ProverJobs.job_paper_ea9c51e8f7d246ef967b6629540eeb01.ExternalNodes.Node_6515c10a3b2a6920f75d

namespace PaperProofTasks.job_paper_ea9c51e8f7d246ef967b6629540eeb01




open _root_.PaperProofTasks.job_paper_ea9c51e8f7d246ef967b6629540eeb01.Statlib.Imported
open MeasureTheory ProbabilityTheory
open PaperProofTasks.job_paper_a86aea8c92ff4120874a0fdca6db77c5.Statlib.Imported
open scoped BigOperators

namespace Statlib.Imported

open MeasureTheory ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_2074902041_7cdeb16b : ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℕ) (hp : 0 < p)
    (X Y : Ω → Fin p → ℝ)
    (hX : Measurable X) (hY : Measurable Y)
    (SigmaX SigmaY : Matrix (Fin p) (Fin p) ℝ)
    (hSigmaX : SigmaX = SigmaX.transpose) (hSigmaY : SigmaY = SigmaY.transpose)
    (SigmaXY : Matrix (Fin (p + p)) (Fin (p + p)) ℝ)
    (hXY : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector μ
      (fun ω : Ω => Fin.append (X ω) (Y ω)) SigmaXY)
    (hintX : ∀ j k : Fin p, Integrable (fun ω => X ω j * X ω k) μ)
    (hintY : ∀ j k : Fin p, Integrable (fun ω => Y ω j * Y ω k) μ)
    (hintXY : ∀ j k : Fin p, Integrable (fun ω => X ω j * Y ω k) μ)
    (hmomX : ∀ j k : Fin p, ∫ ω, X ω j * X ω k ∂μ = SigmaX j k)
    (hmomY : ∀ j k : Fin p, ∫ ω, Y ω j * Y ω k ∂μ = SigmaY j k)
    (hmomXY : ∀ j k : Fin p, ∫ ω, X ω j * Y ω k ∂μ = 0)
    (β : ℝ) (hβ : 0 < β)
    (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g)
    (hg1 : BddAbove (Set.range fun z : ℝ => |deriv g z|))
    (hg2 : BddAbove (Set.range fun z : ℝ => |deriv (deriv g) z|)),
    ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      (let Fbeta : (Fin p → ℝ) → ℝ :=
          fun z => Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 z)
       let Z : ℝ → Ω → Fin p → ℝ :=
          fun s ω j => Real.sqrt s * X ω j + Real.sqrt (1 - s) * Y ω j
       let Psi : ℝ → ℝ := fun s => ∫ ω, g (Fbeta (Z s ω)) ∂μ
       (∀ j k : Fin p,
            Integrable (fun ω => coordPartial j (coordPartial k (compSmoothMax (p := p) g β)) (Z t ω)) μ) ∧
         HasDerivAt Psi
            ((1 / 2 : ℝ) * ∑ j : Fin p, ∑ k : Fin p,
              (SigmaX j k - SigmaY j k) *
                ∫ ω, coordPartial j (coordPartial k (compSmoothMax (p := p) g β)) (Z t ω) ∂μ) t) := by
  /- @proof-region region.target-node.session.4f6887e56c12b2c9 begin -/
  intro Ω instΩ μ instμ p hp X Y hX hY SigmaX SigmaY hSigmaX hSigmaY SigmaXY hXY
    hintX hintY hintXY hmomX hmomY hmomXY β hβ g hg hg1 hg2 t ht
  have hZmeas : Measurable (fun ω : Ω => fun j : Fin p =>
      Real.sqrt t * X ω j + Real.sqrt (1 - t) * Y ω j) := by
    fun_prop
  refine ⟨fun j k => ?_, ?_⟩
  · exact (statopia_math_node_3156732339_a370e2ae μ p hp
      (fun ω : Ω => fun j : Fin p => Real.sqrt t * X ω j + Real.sqrt (1 - t) * Y ω j)
      hZmeas β hβ g hg hg1 hg2).2.1 j k
  · dsimp only
    have hXint : ∀ j : Fin p, Integrable (fun ω => X ω j) μ := by
      intro j
      have hb : Integrable (fun ω : Ω => (1 / 2 : ℝ) * (X ω j * X ω j + 1)) μ :=
        ((hintX j j).add (integrable_const (1 : ℝ))).const_mul (1 / 2)
      refine hb.mono' ?_ ?_
      · exact (by fun_prop : Measurable fun ω : Ω => X ω j).aestronglyMeasurable
      · filter_upwards with ω
        have hle : ∀ x : ℝ, |x| ≤ (1 / 2 : ℝ) * (x * x + 1) := by
          intro x
          nlinarith [sq_nonneg (|x| - 1), sq_abs x, abs_nonneg x]
        simpa using hle (X ω j)
    have hYint : ∀ j : Fin p, Integrable (fun ω => Y ω j) μ := by
      intro j
      have hb : Integrable (fun ω : Ω => (1 / 2 : ℝ) * (Y ω j * Y ω j + 1)) μ :=
        ((hintY j j).add (integrable_const (1 : ℝ))).const_mul (1 / 2)
      refine hb.mono' ?_ ?_
      · exact (by fun_prop : Measurable fun ω : Ω => Y ω j).aestronglyMeasurable
      · filter_upwards with ω
        have hle : ∀ x : ℝ, |x| ≤ (1 / 2 : ℝ) * (x * x + 1) := by
          intro x
          nlinarith [sq_nonneg (|x| - 1), sq_abs x, abs_nonneg x]
        simpa using hle (Y ω j)
    have hstein : ∀ j : Fin p,
        ∫ ω, (fderiv ℝ (fun z : Fin p → ℝ =>
            g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 z)))
            (fun i => Real.sqrt t * X ω i + Real.sqrt (1 - t) * Y ω i)) (Pi.single j 1)
          * (t ^ (-(1 / 2) : ℝ) * X ω j - (1 - t) ^ (-(1 / 2) : ℝ) * Y ω j) ∂μ
        = ∑ k : Fin p, (SigmaX j k - SigmaY j k) *
            ∫ ω, coordPartial k (coordPartial j (compSmoothMax (p := p) g β))
              (fun i => Real.sqrt t * X ω i + Real.sqrt (1 - t) * Y ω i) ∂μ := by
      exact fun j => statopia_math_node_1854214930_5c94c0df μ p hp X Y hX hY SigmaX SigmaY
        hSigmaX hSigmaY SigmaXY hXY hintX hintY hintXY hmomX hmomY hmomXY β hβ g hg hg1 hg2
        t ht j
    have hXsymm : ∀ j k : Fin p, SigmaX j k = SigmaX k j := by
      intro j k
      have h := congrFun (congrFun hSigmaX j) k
      simpa [Matrix.transpose_apply] using h
    have hYsymm : ∀ j k : Fin p, SigmaY j k = SigmaY k j := by
      intro j k
      have h := congrFun (congrFun hSigmaY j) k
      simpa [Matrix.transpose_apply] using h
    obtain ⟨-, -, hderiv, -⟩ :=
      statopia_math_node_1904015730_8e8aa481 μ p hp X Y hX hY hXint hYint β hβ g
        (hg.of_le (by norm_num)) hg1
    have h1 : (∑ j : Fin p, ∑ k : Fin p, (SigmaX j k - SigmaY j k) *
          ∫ ω, coordPartial j (coordPartial k (compSmoothMax (p := p) g β))
            (fun i => Real.sqrt t * X ω i + Real.sqrt (1 - t) * Y ω i) ∂μ)
        = ∑ j : Fin p, ∑ k : Fin p, (SigmaX j k - SigmaY j k) *
          ∫ ω, coordPartial k (coordPartial j (compSmoothMax (p := p) g β))
            (fun i => Real.sqrt t * X ω i + Real.sqrt (1 - t) * Y ω i) ∂μ := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
      rw [show SigmaX b a - SigmaY b a = SigmaX a b - SigmaY a b from by
        rw [hXsymm b a, hYsymm b a]]
    have h2 : (∑ j : Fin p, ∑ k : Fin p, (SigmaX j k - SigmaY j k) *
          ∫ ω, coordPartial k (coordPartial j (compSmoothMax (p := p) g β))
            (fun i => Real.sqrt t * X ω i + Real.sqrt (1 - t) * Y ω i) ∂μ)
        = ∑ j : Fin p, ∫ ω, (fderiv ℝ (fun z : Fin p → ℝ =>
            g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 z)))
            (fun i => Real.sqrt t * X ω i + Real.sqrt (1 - t) * Y ω i)) (Pi.single j 1)
          * (t ^ (-(1 / 2) : ℝ) * X ω j - (1 - t) ^ (-(1 / 2) : ℝ) * Y ω j) ∂μ :=
      Finset.sum_congr rfl (fun j _ => (hstein j).symm)
    have heq : (1 / 2 : ℝ) * ∑ j : Fin p, ∑ k : Fin p,
          (SigmaX j k - SigmaY j k) *
          ∫ ω, coordPartial j (coordPartial k (compSmoothMax (p := p) g β))
            (fun i => Real.sqrt t * X ω i + Real.sqrt (1 - t) * Y ω i) ∂μ
        = (1 / 2 : ℝ) * ∑ j : Fin p, ∫ ω, (fderiv ℝ (fun z : Fin p → ℝ =>
            g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 z)))
            (fun i => Real.sqrt t * X ω i + Real.sqrt (1 - t) * Y ω i)) (Pi.single j 1)
          * (t ^ (-(1 / 2) : ℝ) * X ω j - (1 - t) ^ (-(1 / 2) : ℝ) * Y ω j) ∂μ := by
      rw [h1, h2]
    rw [heq]
    exact hderiv t ht
  /- @proof-region region.target-node.session.4f6887e56c12b2c9 end -/

end Statlib.Imported

