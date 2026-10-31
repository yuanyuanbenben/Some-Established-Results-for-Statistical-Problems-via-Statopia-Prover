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
theorem statopia_math_node_1363480033_de485796 : ∀ {p : ℕ} (hp : 0 < p) {β : ℝ} (hβ : 0 < β)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) (X Y : Fin p → ℝ) {s : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) 1),
    HasDerivAt
      (fun u : ℝ => g (Statlib.StatFoundation.Convergence.smoothMax β
        (WithLp.toLp 2 (fun j : Fin p => Real.sqrt u * X j + Real.sqrt (1 - u) * Y j))))
      (∑ j : Fin p,
        (fderiv ℝ (fun z : Fin p → ℝ =>
            g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 z)))
          (fun j : Fin p => Real.sqrt s * X j + Real.sqrt (1 - s) * Y j))
        (Pi.single j (1 : ℝ)) *
        ((1 / 2 : ℝ) * (s ^ (-(1 / 2) : ℝ) * X j - (1 - s) ^ (-(1 / 2) : ℝ) * Y j)))
      s := by
  /- @proof-region region.target-node.session.1db2c00e89dabf47 begin -/
  intro p hp β hβ g hg X Y s hs
  have hs0 : (0 : ℝ) < s := hs.1
  have hs1 : s < 1 := hs.2
  have hs_ne : s ≠ 0 := ne_of_gt hs0
  have h1s_ne : (1 - s) ≠ 0 := by linarith
  have hpow : s ^ (-(1 / 2) : ℝ) = (Real.sqrt s)⁻¹ := by
    rw [Real.rpow_neg_eq_inv_rpow, ← Real.sqrt_eq_rpow, Real.sqrt_inv]
  have hpow1 : (1 - s) ^ (-(1 / 2) : ℝ) = (Real.sqrt (1 - s))⁻¹ := by
    rw [Real.rpow_neg_eq_inv_rpow, ← Real.sqrt_eq_rpow, Real.sqrt_inv]
  have hcoord : ∀ j : Fin p,
      HasDerivAt (fun u : ℝ => Real.sqrt u * X j + Real.sqrt (1 - u) * Y j)
        ((1 / 2 : ℝ) * (s ^ (-(1 / 2) : ℝ) * X j - (1 - s) ^ (-(1 / 2) : ℝ) * Y j)) s := by
    intro j
    have h1 : HasDerivAt (fun u : ℝ => Real.sqrt u * X j) ((1 / (2 * Real.sqrt s)) * X j) s :=
      (Real.hasDerivAt_sqrt hs_ne).mul_const (X j)
    have h2 : HasDerivAt (fun u : ℝ => Real.sqrt (1 - u) * Y j)
        (((1 / (2 * Real.sqrt (1 - s))) * (-1)) * Y j) s := by
      have hinner : HasDerivAt (fun u : ℝ => 1 - u) (-1) s := by
        simpa using HasDerivAt.const_sub (1 : ℝ) (hasDerivAt_id s)
      have houter : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt (1 - s))) (1 - s) :=
        Real.hasDerivAt_sqrt h1s_ne
      simpa [Function.comp] using (HasDerivAt.comp s houter hinner).mul_const (Y j)
    have hderiv_eq : (1 / (2 * Real.sqrt s)) * X j + (((1 / (2 * Real.sqrt (1 - s))) * (-1)) * Y j)
        = (1 / 2 : ℝ) * (s ^ (-(1 / 2) : ℝ) * X j - (1 - s) ^ (-(1 / 2) : ℝ) * Y j) := by
      rw [hpow, hpow1]
      have hsq : Real.sqrt s ≠ 0 := (Real.sqrt_pos.2 hs0).ne'
      have hsq1 : Real.sqrt (1 - s) ≠ 0 := (Real.sqrt_pos.2 (by linarith : (0 : ℝ) < 1 - s)).ne'
      field_simp [hsq, hsq1]
      ring
    have hadd := h1.add h2
    rw [hderiv_eq] at hadd
    simpa using hadd
  have hW : HasDerivAt
      (fun u : ℝ => fun j : Fin p => Real.sqrt u * X j + Real.sqrt (1 - u) * Y j)
      (fun j : Fin p => (1 / 2 : ℝ) * (s ^ (-(1 / 2) : ℝ) * X j - (1 - s) ^ (-(1 / 2) : ℝ) * Y j)) s := by
    rw [hasDerivAt_pi]
    exact hcoord
  set G : (Fin p → ℝ) → ℝ :=
    fun z : Fin p → ℝ => g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 z)) with hG
  have hGcont : ContDiff ℝ 1 G := by
    simpa [hG] using (statopia_math_node_3426360121_2b3d487b hp hβ hg).1
  have hGdiff : DifferentiableAt ℝ G
      (fun j : Fin p => Real.sqrt s * X j + Real.sqrt (1 - s) * Y j) :=
    (hGcont.contDiffAt).differentiableAt_one
  have hGderiv : HasFDerivAt G
      (fderiv ℝ G (fun j : Fin p => Real.sqrt s * X j + Real.sqrt (1 - s) * Y j))
      (fun j : Fin p => Real.sqrt s * X j + Real.sqrt (1 - s) * Y j) :=
    hGdiff.hasFDerivAt
  have hcomp : HasDerivAt
      (G ∘ (fun u : ℝ => fun j : Fin p => Real.sqrt u * X j + Real.sqrt (1 - u) * Y j))
      ((fderiv ℝ G (fun j : Fin p => Real.sqrt s * X j + Real.sqrt (1 - s) * Y j))
        (fun j : Fin p => (1 / 2 : ℝ) * (s ^ (-(1 / 2) : ℝ) * X j - (1 - s) ^ (-(1 / 2) : ℝ) * Y j))) s :=
    HasFDerivAt.comp_hasDerivAt s hGderiv hW
  have hexp : ∀ (L : (Fin p → ℝ) →L[ℝ] ℝ) (v : Fin p → ℝ),
      L v = ∑ j : Fin p, L (Pi.single j (1 : ℝ)) * v j := by
    intro L v
    rw [← ContinuousLinearMap.sum_comp_single ℝ (fun _ : Fin p => ℝ) L v]
    refine Finset.sum_congr rfl ?_
    intro j _
    have hsingle : (Pi.single j (v j) : Fin p → ℝ) = v j • (Pi.single j (1 : ℝ) : Fin p → ℝ) := by
      funext k
      by_cases hk : k = j
      · subst hk; simp
      · simp [hk]
    show (L.comp (ContinuousLinearMap.single ℝ (fun _ : Fin p => ℝ) j)) (v j)
        = L (Pi.single j (1 : ℝ)) * v j
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.single_apply, hsingle,
      ContinuousLinearMap.map_smul, smul_eq_mul, mul_comm]
  rw [hexp] at hcomp
  rw [hG] at hcomp ⊢
  simpa [Function.comp] using hcomp
  /- @proof-region region.target-node.session.1db2c00e89dabf47 end -/

end Statlib.Imported

