import Statlib.StatFoundation.Statistics.Asymptotic.ScoreCLT
import Statlib.StatFoundation.Convergence.Resampling.GaussianMaxComparison
import Statlib.StatFoundation.Convergence.AnalysisTools.GaussianMaxAnticoncentration
import Statlib.StatFoundation.Statistics.Asymptotic.LAN
import Statlib.StatFoundation.Convergence.AnalysisTools.SmoothMax
import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.Vocabulary
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.Base

namespace PaperProofTasks.job_paper_de3065fb922748188f3a0354eba90ed9

open _root_.PaperProofTasks.job_paper_de3065fb922748188f3a0354eba90ed9.Statlib.Imported
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

set_option autoImplicit false in
theorem statopia_math_node_154348488_06fea6fe : ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℕ) (hp : 1 ≤ p) (X : Ω → Fin p → ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (hGauss : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector μ X Sigma)
    (hL2 : ∀ j : Fin p, MemLp (fun ω => X ω j) 2 μ),
    ∀ j : Fin p, ∫ ω, X ω j ∂μ = 0 := by
  /- @proof-region region.target-node.session.60c81b8ac5e98c94 begin -/
  intro Ω Ωinst μ μinst p hp X Sigma hGauss hL2 j
  rcases hGauss with ⟨hmeas, hexp, hmgf⟩
  have hGauss' : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector μ X Sigma :=
    ⟨hmeas, hexp, hmgf⟩
  have key : ∀ u : Fin p → ℝ,
      (∑ i, ∑ k, u i * ((2:ℝ)⁻¹ • (Sigma + Sigma.transpose)) i k * u k)
        = ∑ i, ∑ k, u i * Sigma i k * u k := by
    intro u
    have htrans : (∑ i, ∑ k, u i * (Sigma.transpose) i k * u k)
        = ∑ i, ∑ k, u i * Sigma i k * u k := by
      simp only [Matrix.transpose_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
      ring
    have hstep1 : (∑ i, ∑ k, u i * ((2:ℝ)⁻¹ • (Sigma + Sigma.transpose)) i k * u k)
        = ∑ i, ∑ k, (2:ℝ)⁻¹ * (u i * ((Sigma + Sigma.transpose) i k) * u k) := by
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
      rw [Matrix.smul_apply, smul_eq_mul]; ring
    have hstep2 : (∑ i, ∑ k, (2:ℝ)⁻¹ * (u i * ((Sigma + Sigma.transpose) i k) * u k))
        = (2:ℝ)⁻¹ * (∑ i, ∑ k, u i * ((Sigma + Sigma.transpose) i k) * u k) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
    have hstep3 : (∑ i, ∑ k, u i * ((Sigma + Sigma.transpose) i k) * u k)
        = (∑ i, ∑ k, u i * Sigma i k * u k)
          + (∑ i, ∑ k, u i * (Sigma.transpose) i k * u k) := by
      have hinner : ∀ i, (∑ k, u i * ((Sigma + Sigma.transpose) i k) * u k)
          = (∑ k, u i * Sigma i k * u k) + (∑ k, u i * (Sigma.transpose) i k * u k) := by
        intro i
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Matrix.add_apply]; ring
      simp only [hinner]
      rw [Finset.sum_add_distrib]
    calc ∑ i, ∑ k, u i * ((2:ℝ)⁻¹ • (Sigma + Sigma.transpose)) i k * u k
        = ∑ i, ∑ k, (2:ℝ)⁻¹ * (u i * ((Sigma + Sigma.transpose) i k) * u k) := hstep1
      _ = (2:ℝ)⁻¹ * (∑ i, ∑ k, u i * ((Sigma + Sigma.transpose) i k) * u k) := hstep2
      _ = (2:ℝ)⁻¹ * ((∑ i, ∑ k, u i * Sigma i k * u k)
            + (∑ i, ∑ k, u i * (Sigma.transpose) i k * u k)) := by rw [hstep3]
      _ = (2:ℝ)⁻¹ * ((∑ i, ∑ k, u i * Sigma i k * u k)
            + (∑ i, ∑ k, u i * Sigma i k * u k)) := by rw [htrans]
      _ = ∑ i, ∑ k, u i * Sigma i k * u k := by ring_nf
  have hG' : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector μ X
      ((2:ℝ)⁻¹ • (Sigma + Sigma.transpose)) := by
    refine ⟨hmeas, hexp, ?_⟩
    intro u
    rw [hmgf u, key u]
  have hSigma' : ((2:ℝ)⁻¹ • (Sigma + Sigma.transpose)).PosSemidef :=
    Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector.posSemidef_symmetrizedCovariance
      hGauss' hp
  have hmap :=
    Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector.map_linearCombination
      μ X ((2:ℝ)⁻¹ • (Sigma + Sigma.transpose)) hG' hSigma' (Pi.single j (1 : ℝ) : Fin p → ℝ)
  have hcomp : ∀ ω, (∑ k, (Pi.single j (1 : ℝ) : Fin p → ℝ) k * X ω k) = X ω j := by
    intro ω
    have hs : (∑ k, (Pi.single j (1 : ℝ) : Fin p → ℝ) k * X ω k)
        = (Pi.single j (1 : ℝ) : Fin p → ℝ) j * X ω j :=
      Finset.sum_eq_single j
        (fun b _ hb => by rw [Pi.single_eq_of_ne hb, zero_mul])
        (fun h => absurd (Finset.mem_univ j) h)
    rw [hs, Pi.single_eq_same, one_mul]
  have hfun : (fun ω => ∑ k, (Pi.single j (1 : ℝ) : Fin p → ℝ) k * X ω k) = (fun ω => X ω j) := by
    funext ω; exact hcomp ω
  rw [hfun] at hmap
  have hφ : AEMeasurable (fun ω => X ω j) μ := (hL2 j).aestronglyMeasurable.aemeasurable
  have hint : ∫ ω, X ω j ∂μ = ∫ x, x ∂(Measure.map (fun ω => X ω j) μ) :=
    (MeasureTheory.integral_map (φ := fun ω => X ω j) (f := id) hφ measurable_id.aestronglyMeasurable).symm
  rw [hint, hmap]
  exact ProbabilityTheory.integral_id_gaussianReal
  /- @proof-region region.target-node.session.60c81b8ac5e98c94 end -/

end Statlib.Imported

