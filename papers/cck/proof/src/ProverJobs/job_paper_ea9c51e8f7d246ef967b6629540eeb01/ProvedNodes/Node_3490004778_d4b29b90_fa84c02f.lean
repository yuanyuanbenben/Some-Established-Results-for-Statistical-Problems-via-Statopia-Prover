import Statlib.StatFoundation.Statistics.Asymptotic.ScoreCLT
import Statlib.StatFoundation.Convergence.Resampling.GaussianMaxComparison
import Statlib.StatFoundation.Convergence.AnalysisTools.GaussianMaxAnticoncentration
import Statlib.StatFoundation.Statistics.Asymptotic.LAN
import Statlib.StatFoundation.Convergence.AnalysisTools.SmoothMax
import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import ProverJobs.job_paper_ea9c51e8f7d246ef967b6629540eeb01.Vocabulary
import ProverJobs.job_paper_ea9c51e8f7d246ef967b6629540eeb01.Base
import ProverJobs.job_paper_ea9c51e8f7d246ef967b6629540eeb01.ProvedNodes.Node_3426360121_2b3d487b_26518c41

namespace PaperProofTasks.job_paper_ea9c51e8f7d246ef967b6629540eeb01
open _root_.PaperProofTasks.job_paper_ea9c51e8f7d246ef967b6629540eeb01.Statlib.Imported
open MeasureTheory ProbabilityTheory

namespace Statlib.Imported

open MeasureTheory ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_3490004778_d4b29b90 : ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℕ) (hp : 0 < p) (X Y : Ω → Fin p → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXint : ∀ j : Fin p, Integrable (fun ω => X ω j) μ)
    (hYint : ∀ j : Fin p, Integrable (fun ω => Y ω j) μ)
    (β : ℝ) (hβ : 0 < β) (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g)
    (hg_bdd : BddAbove (Set.range fun z : ℝ => |deriv g z|)),
    ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ j : Fin p,
      Integrable
        (fun ω => (fderiv ℝ (fun z : Fin p → ℝ =>
              g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 z)))
            (fun j : Fin p => Real.sqrt t * X ω j + Real.sqrt (1 - t) * Y ω j))
          (Pi.single j (1 : ℝ)) *
          (t ^ (-(1/2) : ℝ) * X ω j - (1 - t) ^ (-(1/2) : ℝ) * Y ω j)) μ := by
  /- @proof-region region.target-node.session.dc0d2479eb739ec0 begin -/
  intro Ω _ μ _ p hp X Y hX hY hXint hYint β hβ g hg hg_bdd t ht j
  obtain ⟨M, hM⟩ := hg_bdd
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (deriv g 0)) (hM ⟨0, rfl⟩)
  set c1 : ℝ := t ^ (-(1 / 2) : ℝ) with hc1def
  set c2 : ℝ := (1 - t) ^ (-(1 / 2) : ℝ) with hc2def
  have hc1 : 0 ≤ c1 := Real.rpow_nonneg ht.1.le _
  have hc2 : 0 ≤ c2 := Real.rpow_nonneg (by linarith [ht.2]) _
  have hchild := statopia_math_node_3426360121_2b3d487b hp hβ hg
  have hderiv : ∀ z : Fin p → ℝ,
      ‖(fderiv ℝ (fun z : Fin p → ℝ =>
          g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 z))) z)
        (Pi.single j (1 : ℝ))‖ ≤ M := by
    intro z
    have hh := Statlib.StatFoundation.Convergence.softmax_weights_sum_nonneg (β := β) hp (WithLp.toLp 2 z)
    have hw0 : 0 ≤ Statlib.StatFoundation.Convergence.softmaxWeight β (WithLp.toLp 2 z) j := hh.1 j
    have hw1 : Statlib.StatFoundation.Convergence.softmaxWeight β (WithLp.toLp 2 z) j ≤ 1 := by
      rw [← hh.2]
      exact Finset.single_le_sum (fun i _ => hh.1 i) (Finset.mem_univ j)
    rw [hchild.2 z j, norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg hw0]
    calc |deriv g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 z))| *
          Statlib.StatFoundation.Convergence.softmaxWeight β (WithLp.toLp 2 z) j
        ≤ M * 1 := by
          refine mul_le_mul ?_ hw1 hw0 hM0
          exact hM ⟨Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 z), rfl⟩
      _ = M := mul_one M
  have hbound_int : Integrable (fun ω => M * (c1 * ‖X ω j‖ + c2 * ‖Y ω j‖)) μ := by
    have hx : Integrable (fun ω => c1 * ‖X ω j‖) μ := (hXint j).norm.const_mul c1
    have hy : Integrable (fun ω => c2 * ‖Y ω j‖) μ := (hYint j).norm.const_mul c2
    exact (hx.add hy).const_mul M
  refine Integrable.mono' hbound_int ?_ ?_
  · have hcontΦ : Continuous (fun z : Fin p → ℝ =>
        (fderiv ℝ (fun z : Fin p → ℝ =>
            g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 z))) z)
          (Pi.single j (1 : ℝ))) := by
      have h1 := hchild.1.contDiff_fderiv_apply (m := 0) (by simp)
      have h2 : Continuous (fun z : Fin p → ℝ => (z, (Pi.single j (1 : ℝ) : Fin p → ℝ))) := by
        fun_prop
      simpa using h1.continuous.comp h2
    have hEq : (fun ω : Ω => Real.sqrt t • X ω + Real.sqrt (1 - t) • Y ω)
        = (fun ω : Ω => fun i : Fin p =>
            Real.sqrt t * X ω i + Real.sqrt (1 - t) * Y ω i) := by
      funext ω i
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hZaem : AEMeasurable (fun ω : Ω => fun i : Fin p =>
        Real.sqrt t * X ω i + Real.sqrt (1 - t) * Y ω i) μ := by
      have h0 : AEMeasurable (fun ω : Ω => Real.sqrt t • X ω + Real.sqrt (1 - t) • Y ω) μ :=
        (hX.aemeasurable.const_smul (Real.sqrt t)).add
          (hY.aemeasurable.const_smul (Real.sqrt (1 - t)))
      rw [hEq] at h0
      exact h0
    have hΦaem : AEMeasurable (fun ω : Ω =>
        (fderiv ℝ (fun z : Fin p → ℝ =>
            g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 z)))
          (fun i : Fin p => Real.sqrt t * X ω i + Real.sqrt (1 - t) * Y ω i))
        (Pi.single j (1 : ℝ))) μ :=
      hcontΦ.measurable.comp_aemeasurable hZaem
    have h2aem : AEMeasurable (fun ω : Ω => c1 * X ω j - c2 * Y ω j) μ :=
      ((hXint j).aestronglyMeasurable.aemeasurable.const_mul c1).sub
        ((hYint j).aestronglyMeasurable.aemeasurable.const_mul c2)
    exact (hΦaem.mul h2aem).aestronglyMeasurable
  · filter_upwards with ω
    rw [norm_mul]
    refine mul_le_mul (hderiv _) ?_ (norm_nonneg _) hM0
    calc ‖c1 * X ω j - c2 * Y ω j‖ ≤ ‖c1 * X ω j‖ + ‖c2 * Y ω j‖ := norm_sub_le _ _
      _ = c1 * ‖X ω j‖ + c2 * ‖Y ω j‖ := by
          rw [norm_mul, norm_mul, Real.norm_of_nonneg hc1, Real.norm_of_nonneg hc2]
  /- @proof-region region.target-node.session.dc0d2479eb739ec0 end -/

end Statlib.Imported

