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
theorem statopia_math_node_2322479387_a1995076 : ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℕ) (hp : 1 ≤ p) (X : Ω → Fin p → ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (hGauss : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector μ X Sigma)
    (a c : Fin p → ℝ),
    IsGaussian
      (Measure.map (fun ω : Ω => fun j : Fin p => a j * X ω j + c j) μ) := by
  /- @proof-region region.target-node.session.f1bb0c8c8798cd81 begin -/
  intro Ω instΩ μ instμ p hp X Sigma hGauss a c
  have hpsd : ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)).PosSemidef :=
    hGauss.posSemidef_symmetrizedCovariance hp
  have hX : Measurable X := hGauss.1
  have hsym : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector μ X
      ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) := by
    refine ⟨hX, hGauss.2, ?_⟩
    intro u
    rw [hGauss.3 u]
    have hsum : (∑ i, ∑ j, u i * ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) i j * u j)
        = ∑ i, ∑ j, u i * Sigma i j * u j := by
      have hscale : ∀ (F : Fin p → Fin p → ℝ),
          (∑ i, ∑ j, (2 : ℝ)⁻¹ * F i j) = (2 : ℝ)⁻¹ * ∑ i, ∑ j, F i j := by
        intro F
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]
      have hQR : (∑ i, ∑ j, u i * Sigma j i * u j) = ∑ i, ∑ j, u i * Sigma i j * u j := by
        conv_lhs => rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
      calc (∑ i, ∑ j, u i * ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) i j * u j)
          = ∑ i, ∑ j, (2⁻¹ * (u i * Sigma i j * u j) + 2⁻¹ * (u i * Sigma j i * u j)) := by
            refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
            simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul]
            ring
        _ = (∑ i, ∑ j, 2⁻¹ * (u i * Sigma i j * u j)) +
              (∑ i, ∑ j, 2⁻¹ * (u i * Sigma j i * u j)) := by
            simp only [Finset.sum_add_distrib]
        _ = 2⁻¹ * (∑ i, ∑ j, u i * Sigma i j * u j) +
              2⁻¹ * (∑ i, ∑ j, u i * Sigma j i * u j) := by
            rw [hscale (fun i j => u i * Sigma i j * u j),
              hscale (fun i j => u i * Sigma j i * u j)]
        _ = 2⁻¹ * (∑ i, ∑ j, u i * Sigma i j * u j) +
              2⁻¹ * (∑ i, ∑ j, u i * Sigma i j * u j) := by
            rw [hQR]
        _ = ∑ i, ∑ j, u i * Sigma i j * u j := by
            have h2 : (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ = 1 := by norm_num
            rw [← add_mul, h2, one_mul]
    rw [hsum]
  have hlin : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector μ
      (fun ω => (Matrix.diagonal a).mulVec (X ω))
      (Matrix.diagonal a * ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) *
        (Matrix.diagonal a).transpose) :=
    Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector.linearImage μ X
      ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) hsym (Matrix.diagonal a)
  have hYpsd : (Matrix.diagonal a * ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) *
      (Matrix.diagonal a).transpose).PosSemidef := by
    have h := Matrix.PosSemidef.mul_mul_conjTranspose_same hpsd (Matrix.diagonal a)
    simpa using h
  have hcen : IsGaussian (Measure.map (fun ω => (Matrix.diagonal a).mulVec (X ω)) μ) :=
    Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector.pushforward_isGaussian
      μ (fun ω => (Matrix.diagonal a).mulVec (X ω)) _ hlin hYpsd
  have hfun : (fun ω : Ω => (Matrix.diagonal a).mulVec (X ω)) = (fun ω j => a j * X ω j) := by
    funext ω j
    exact Matrix.mulVec_diagonal a (X ω) j
  have hcen' : IsGaussian (Measure.map (fun ω => fun j => a j * X ω j) μ) := by
    rw [hfun] at hcen
    exact hcen
  have htrans : ∀ (ρ : Measure (Fin p → ℝ)), IsGaussian ρ →
      IsGaussian (Measure.map (fun y : Fin p → ℝ => y + c) ρ) := by
    intro ρ hρ
    haveI : IsGaussian ρ := hρ
    refine isGaussian_of_map_eq_gaussianReal (fun L => ?_)
    have hLρ : IsGaussian (Measure.map (⇑L) ρ) := isGaussian_map (μ := ρ) L
    obtain ⟨m, v, hmv⟩ : ∃ m v, Measure.map (⇑L) ρ = gaussianReal m v :=
      ⟨_, _, IsGaussian.eq_gaussianReal (Measure.map (⇑L) ρ) hLρ⟩
    refine ⟨m + L c, v, ?_⟩
    have hLm : Measurable (⇑L) := L.continuous.measurable
    have hsh : Measurable (fun y : Fin p → ℝ => y + c) :=
      (continuous_id.add continuous_const).measurable
    have hsh2 : Measurable (fun t : ℝ => t + L c) :=
      (continuous_id.add continuous_const).measurable
    have hfe1 : ((⇑L) ∘ (fun y : Fin p → ℝ => y + c)) = (fun y : Fin p → ℝ => L y + L c) := by
      funext y
      simp only [Function.comp_apply]
      exact map_add L y c
    have hfe2 : ((fun t : ℝ => t + L c) ∘ (⇑L)) = (fun y : Fin p → ℝ => L y + L c) := by
      funext y
      rfl
    have e1 : Measure.map (⇑L) (Measure.map (fun y : Fin p → ℝ => y + c) ρ)
        = Measure.map (fun y : Fin p → ℝ => L y + L c) ρ :=
      (MeasureTheory.Measure.map_map (μ := ρ) (g := ⇑L)
        (f := fun y : Fin p → ℝ => y + c) hLm hsh).trans
        (congrArg (fun k : (Fin p → ℝ) → ℝ => Measure.map k ρ) hfe1)
    have e2 : Measure.map (fun y : Fin p → ℝ => L y + L c) ρ
        = Measure.map (fun t : ℝ => t + L c) (Measure.map (⇑L) ρ) :=
      (congrArg (fun k : (Fin p → ℝ) → ℝ => Measure.map k ρ) hfe2).trans
        (MeasureTheory.Measure.map_map (μ := ρ) (g := fun t : ℝ => t + L c)
          (f := ⇑L) hsh2 hLm).symm
    have e3 : Measure.map (fun t : ℝ => t + L c) (Measure.map (⇑L) ρ)
        = gaussianReal (m + L c) v := by
      rw [hmv]
      exact gaussianReal_map_add_const (L c)
    exact e1.trans (e2.trans e3)
  have hgen : Measurable (fun ω : Ω => fun j => a j * X ω j) := by
    refine measurable_pi_iff.2 (fun j => ?_)
    exact measurable_const.mul ((measurable_pi_iff.1 hX) j)
  have hcomp : Measure.map (fun y : Fin p → ℝ => y + c)
      (Measure.map (fun ω => fun j => a j * X ω j) μ)
      = Measure.map (fun ω : Ω => fun j => a j * X ω j + c j) μ :=
    MeasureTheory.Measure.map_map (μ := μ) (g := fun y : Fin p → ℝ => y + c)
      (f := fun ω => fun j => a j * X ω j) ((continuous_id.add continuous_const).measurable) hgen
  rw [← hcomp]
  exact htrans _ hcen'
  /- @proof-region region.target-node.session.f1bb0c8c8798cd81 end -/

end Statlib.Imported

