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
theorem statopia_math_node_3426360121_2b3d487b : ∀ {p : ℕ} (hp : 0 < p) {β : ℝ} (hβ : 0 < β) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g),
    ContDiff ℝ 1
        (fun z : Fin p → ℝ =>
          g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 z)))
      ∧ ∀ (z : Fin p → ℝ) (j : Fin p),
          (fderiv ℝ
              (fun z : Fin p → ℝ =>
                g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 z)))
              z)
            (Pi.single j (1 : ℝ))
            = deriv g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 z))
                * Statlib.StatFoundation.Convergence.softmaxWeight β (WithLp.toLp 2 z) j := by
  /- @proof-region region.target-node.session.670eedc4fbf7a13c begin -/
  intro p hp β hβ g hg
  obtain ⟨g', hg'0, hg'⟩ := (contDiff_succ_iff_hasFDerivAt (𝕜 := ℝ) (n := 0)).mp (by simpa using hg)
  set Tclm : (Fin p → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin p) :=
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin p => ℝ)).symm :
      (Fin p → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin p)) with hTclm
  have hsoft0 : ∀ i : Fin p,
      Continuous (fun x : EuclideanSpace ℝ (Fin p) =>
        Statlib.StatFoundation.Convergence.softmaxWeight β x i) := by
    have hofLp : ∀ k : Fin p, Continuous (fun x : EuclideanSpace ℝ (Fin p) => x.ofLp k) := by
      intro k
      have h1 : Continuous (fun x : EuclideanSpace ℝ (Fin p) => x.ofLp) := by
        simpa using (↑(PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin p => ℝ)) :
          EuclideanSpace ℝ (Fin p) →L[ℝ] (Fin p → ℝ)).continuous
      exact (continuous_apply k).comp h1
    intro i
    simp only [Statlib.StatFoundation.Convergence.softmaxWeight]
    have hne : ∀ x : EuclideanSpace ℝ (Fin p), (∑ k : Fin p, Real.exp (β * x.ofLp k)) ≠ 0 := by
      intro x
      have hpos : 0 < ∑ k : Fin p, Real.exp (β * x.ofLp k) := by
        have hle : Real.exp (β * x.ofLp (⟨0, hp⟩ : Fin p)) ≤ ∑ k : Fin p, Real.exp (β * x.ofLp k) :=
          Finset.single_le_sum (f := fun k : Fin p => Real.exp (β * x.ofLp k))
            (fun k _ => (Real.exp_pos _).le) (Finset.mem_univ _)
        exact lt_of_lt_of_le (Real.exp_pos _) hle
      exact ne_of_gt hpos
    exact (Real.continuous_exp.comp (continuous_const.mul (hofLp i))).div
      (continuous_finset_sum _ (fun k _ => Real.continuous_exp.comp (continuous_const.mul (hofLp k))))
      hne
  have hV : Continuous (fun x : EuclideanSpace ℝ (Fin p) =>
      WithLp.toLp 2 (fun i => Statlib.StatFoundation.Convergence.softmaxWeight β x i)) := by
    have h1 : Continuous (fun x : EuclideanSpace ℝ (Fin p) =>
        (fun i => Statlib.StatFoundation.Convergence.softmaxWeight β x i)) := continuous_pi hsoft0
    exact (PiLp.contDiff_toLp (𝕜 := ℝ) (p := 2) (n := 1)).continuous.comp h1
  have hSC1 : ContDiff ℝ 1 (fun x : EuclideanSpace ℝ (Fin p) =>
      Statlib.StatFoundation.Convergence.smoothMax β x) := by
    have h0 : ContDiff ℝ (↑(0 : ℕ)) (fun x : EuclideanSpace ℝ (Fin p) =>
        (innerSL ℝ) (WithLp.toLp 2 (fun i =>
          Statlib.StatFoundation.Convergence.softmaxWeight β x i))) := by
      have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin p) =>
          (innerSL ℝ) (WithLp.toLp 2 (fun i =>
            Statlib.StatFoundation.Convergence.softmaxWeight β x i))) :=
        (innerSL ℝ : EuclideanSpace ℝ (Fin p) →L[ℝ] (EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ)).continuous.comp hV
      simpa using (contDiff_zero.mpr hcont : ContDiff ℝ 0 (fun x : EuclideanSpace ℝ (Fin p) =>
        (innerSL ℝ) (WithLp.toLp 2 (fun i =>
          Statlib.StatFoundation.Convergence.softmaxWeight β x i))))
    have hkey := (contDiff_succ_iff_hasFDerivAt (𝕜 := ℝ) (n := 0)
      (f := fun x : EuclideanSpace ℝ (Fin p) =>
        Statlib.StatFoundation.Convergence.smoothMax β x)).mpr
      ⟨fun x => (innerSL ℝ) (WithLp.toLp 2 (fun i =>
          Statlib.StatFoundation.Convergence.softmaxWeight β x i)),
        h0, fun x => Statlib.StatFoundation.Convergence.smoothMax_gradient_eq_softmax hp hβ x⟩
    simpa using hkey
  have hTC1 : ContDiff ℝ 1 (fun z : Fin p → ℝ => WithLp.toLp 2 z) := PiLp.contDiff_toLp
  have hSTC1 : ContDiff ℝ 1 (fun z : Fin p → ℝ =>
      Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 z)) := hSC1.comp hTC1
  refine ⟨hg.comp hSTC1, ?_⟩
  intro z j
  have hTz : HasFDerivAt (fun z : Fin p → ℝ => WithLp.toLp 2 z) Tclm z := PiLp.hasFDerivAt_toLp 2 z
  have hSz : HasFDerivAt
      (fun x : EuclideanSpace ℝ (Fin p) => Statlib.StatFoundation.Convergence.smoothMax β x)
      ((innerSL ℝ) (WithLp.toLp 2 (fun i =>
        Statlib.StatFoundation.Convergence.softmaxWeight β (WithLp.toLp 2 z) i)))
      (WithLp.toLp 2 z) :=
    Statlib.StatFoundation.Convergence.smoothMax_gradient_eq_softmax hp hβ _
  have hSTz : HasFDerivAt
      (fun z : Fin p → ℝ => Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 z))
      (((innerSL ℝ) (WithLp.toLp 2 (fun i =>
        Statlib.StatFoundation.Convergence.softmaxWeight β (WithLp.toLp 2 z) i))).comp Tclm) z :=
    hSz.comp z hTz
  have hGz : HasFDerivAt
      (fun z : Fin p → ℝ => g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 z)))
      ((g' (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 z))).comp
        (((innerSL ℝ) (WithLp.toLp 2 (fun i =>
          Statlib.StatFoundation.Convergence.softmaxWeight β (WithLp.toLp 2 z) i))).comp Tclm)) z :=
    (hg' _).comp z hSTz
  rw [hGz.fderiv]
  have hTapply : Tclm (Pi.single j (1 : ℝ)) = EuclideanSpace.single j 1 := by
    simp [hTclm, EuclideanSpace.toLp_single]
  have hinner : (innerSL ℝ) (WithLp.toLp 2 (fun i =>
      Statlib.StatFoundation.Convergence.softmaxWeight β (WithLp.toLp 2 z) i))
      (EuclideanSpace.single j (1 : ℝ))
      = Statlib.StatFoundation.Convergence.softmaxWeight β (WithLp.toLp 2 z) j := by
    have h2 : inner ℝ (WithLp.toLp 2 (fun i =>
        Statlib.StatFoundation.Convergence.softmaxWeight β (WithLp.toLp 2 z) i))
        (EuclideanSpace.single j (1 : ℝ))
        = Statlib.StatFoundation.Convergence.softmaxWeight β (WithLp.toLp 2 z) j := by
      rw [EuclideanSpace.inner_single_right]
      simp [PiLp.toLp_apply]
    simpa using h2
  have hgap : ∀ a : ℝ, g' (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 z)) a
      = a * deriv g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 z)) := by
    intro a
    have h1 : g' (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 z)) 1
        = deriv g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 z)) :=
      ((hg' (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 z))).hasDerivAt).deriv.symm
    have h2 : g' (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 z)) a
        = a • g' (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 z)) 1 := by
      have h3 := (g' (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 z))).map_smul a (1 : ℝ)
      rwa [show a • (1 : ℝ) = a from by simp] at h3
    rw [h2, h1]
    simp
  simp only [ContinuousLinearMap.comp_apply]
  rw [hTapply, hinner, hgap]
  exact mul_comm _ _
  /- @proof-region region.target-node.session.670eedc4fbf7a13c end -/

end Statlib.Imported

