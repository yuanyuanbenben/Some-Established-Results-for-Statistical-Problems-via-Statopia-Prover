import Statlib.StatFoundation.Convergence.AnalysisTools.ConvergenceModes
import ProverJobs.job_paper_c1b4b2ae4a83402c9ed74e46a3652ba5.Vocabulary
import ProverJobs.job_paper_c1b4b2ae4a83402c9ed74e46a3652ba5.Base
import ProverJobs.job_paper_c1b4b2ae4a83402c9ed74e46a3652ba5.ProvedNodes.Node_1966510948_89ba2840_e4516c19
import ProverJobs.job_paper_c1b4b2ae4a83402c9ed74e46a3652ba5.ProvedNodes.Node_566849461_e206dd4e_57422b29


open MeasureTheory Filter Topology
open scoped ENNReal
open Statlib.Imported

open MeasureTheory Filter Topology
open scoped ENNReal
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_3655512486_d9d5ae90 : ∀ {X Θ : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) (k : Θ → X → ℝ) (hK : ∀ θ : Θ, IsProbDensity μ (k θ))
    (t : ℕ) (ht : 2 ≤ t)
    (W : ℕ → ExactMixture Θ X μ k t)
    (P : ProbabilityMeasure X)
    (l : Fin t) (sigma : Fin (t - 1) → Fin t)
    (hsigma_mono : StrictMono sigma)
    (hsigma_range : Set.range sigma = ({l} : Set (Fin t))ᶜ)
    (G : ℕ → ExactMixture Θ X μ k (t - 1))
    (hG : ∀ (i : ℕ) (x : X),
      (G i).f x = ∑ r : Fin (t - 1),
        ((W i).weights (sigma r) / (1 - (W i).weights l)) * k ((W i).params (sigma r)) x)
    (hconv : Statlib.StatFoundation.Convergence.WeakConvergence
      (fun i => probOfDensity μ (W i).f (W i).dens) P)
    (hdel : Tendsto (fun i => (W i).weights l) atTop (nhds 0)),
    Statlib.StatFoundation.Convergence.WeakConvergence
      (fun i => probOfDensity μ (G i).f (G i).dens) P := by
  /- @proof-region region.target-node.session.49934e94d76f00a0 begin -/
  intro X Θ _ _ _ μ k hK t ht W P l sigma hsigma_mono hsigma_range G hG hconv hdel
  unfold Statlib.StatFoundation.Convergence.WeakConvergence at hconv ⊢
  rw [MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at hconv ⊢
  intro g
  have hcoe : ∀ (f : X → ℝ) (hf : IsProbDensity μ f),
      ((probOfDensity μ f hf : ProbabilityMeasure X) : Measure X)
        = μ.withDensity (fun x => ENNReal.ofReal (f x)) := fun f hf => rfl
  have hdensity : ∀ (f : X → ℝ) (hf : IsProbDensity μ f),
      ∫ x, g x ∂↑(probOfDensity μ f hf) = ∫ x, g x * f x ∂μ := by
    intro f hf
    have hmeas : AEMeasurable (fun x => ENNReal.ofReal (f x)) μ :=
      ENNReal.measurable_ofReal.comp_aemeasurable hf.1
    have hfin : ∀ᵐ x ∂μ, (fun x => ENNReal.ofReal (f x)) x < ⊤ := by
      filter_upwards with x
      exact ENNReal.ofReal_lt_top
    rw [hcoe f hf, integral_withDensity_eq_integral_toReal_smul₀ hmeas hfin]
    refine integral_congr_ae ?_
    filter_upwards [hf.2.1] with x hx
    rw [ENNReal.toReal_ofReal hx, smul_eq_mul, mul_comm]
  have hgC : ∀ x : X, |g x| ≤ ‖g‖ := by
    intro x
    simpa [Real.norm_eq_abs] using BoundedContinuousFunction.norm_coe_le_norm g x
  have hgmeas : AEStronglyMeasurable (fun x => g x) μ := g.continuous.aestronglyMeasurable
  have hbdd : ∀ᵐ x ∂μ, ‖g x‖ ≤ ‖g‖ := by
    filter_upwards with x
    simpa [Real.norm_eq_abs] using hgC x
  have hbound : ∀ i : ℕ,
      |(∫ x, g x ∂↑(probOfDensity μ (G i).f (G i).dens))
        - ∫ x, g x ∂↑(probOfDensity μ (W i).f (W i).dens)|
        ≤ 2 * ‖g‖ * (W i).weights l := by
    intro i
    have hWG : Integrable (W i).f μ :=
      (statopia_math_node_566849461_e206dd4e.{_, 0} μ (W i).f (W i).dens).1.1
    have hGG : Integrable (G i).f μ :=
      (statopia_math_node_566849461_e206dd4e.{_, 0} μ (G i).f (G i).dens).1.1
    have hL1 : ∫ x, |(W i).f x - (G i).f x| ∂μ ≤ 2 * (W i).weights l :=
      statopia_math_node_1966510948_89ba2840 μ k hK t ht W l sigma hsigma_mono hsigma_range G hG i
    have hL1' : ∫ x, |(G i).f x - (W i).f x| ∂μ ≤ 2 * (W i).weights l := by
      simpa only [abs_sub_comm] using hL1
    have hdiff : Integrable (fun x => (G i).f x - (W i).f x) μ := hGG.sub hWG
    have hprodG : Integrable (fun x => g x * (G i).f x) μ :=
      Integrable.bdd_mul hGG hgmeas hbdd
    have hprodW : Integrable (fun x => g x * (W i).f x) μ :=
      Integrable.bdd_mul hWG hgmeas hbdd
    have hprodD : Integrable (fun x => g x * ((G i).f x - (W i).f x)) μ :=
      Integrable.bdd_mul hdiff hgmeas hbdd
    have hIntEq :
        (∫ x, g x ∂↑(probOfDensity μ (G i).f (G i).dens))
          - ∫ x, g x ∂↑(probOfDensity μ (W i).f (W i).dens)
        = ∫ x, g x * ((G i).f x - (W i).f x) ∂μ := by
      rw [hdensity (G i).f (G i).dens, hdensity (W i).f (W i).dens]
      rw [← integral_sub hprodG hprodW]
      refine integral_congr_ae ?_
      filter_upwards with x
      ring
    have hleft : Integrable (fun x => |g x * ((G i).f x - (W i).f x)|) μ := by
      simpa only [Real.norm_eq_abs] using hprodD.norm
    have hright : Integrable (fun x => ‖g‖ * |(G i).f x - (W i).f x|) μ := by
      simpa only [Real.norm_eq_abs] using hdiff.norm.const_mul ‖g‖
    calc |(∫ x, g x ∂↑(probOfDensity μ (G i).f (G i).dens))
          - ∫ x, g x ∂↑(probOfDensity μ (W i).f (W i).dens)|
        = |∫ x, g x * ((G i).f x - (W i).f x) ∂μ| := by rw [hIntEq]
      _ ≤ ∫ x, |g x * ((G i).f x - (W i).f x)| ∂μ := by
          simpa only [Real.norm_eq_abs] using
            norm_integral_le_integral_norm (fun x => g x * ((G i).f x - (W i).f x))
      _ ≤ ∫ x, ‖g‖ * |(G i).f x - (W i).f x| ∂μ := by
          refine integral_mono_ae hleft hright ?_
          filter_upwards with x
          calc |g x * ((G i).f x - (W i).f x)|
              = |g x| * |(G i).f x - (W i).f x| := abs_mul _ _
            _ ≤ ‖g‖ * |(G i).f x - (W i).f x| :=
                mul_le_mul_of_nonneg_right (hgC x) (abs_nonneg _)
      _ = ‖g‖ * ∫ x, |(G i).f x - (W i).f x| ∂μ := integral_const_mul ‖g‖ _
      _ ≤ ‖g‖ * (2 * (W i).weights l) := mul_le_mul_of_nonneg_left hL1' (norm_nonneg g)
      _ = 2 * ‖g‖ * (W i).weights l := by ring
  have hzero : Tendsto (fun i =>
      (∫ x, g x ∂↑(probOfDensity μ (G i).f (G i).dens))
        - ∫ x, g x ∂↑(probOfDensity μ (W i).f (W i).dens)) atTop (nhds 0) := by
    have hupper : Tendsto (fun i => 2 * ‖g‖ * (W i).weights l) atTop (nhds 0) := by
      simpa using hdel.const_mul (2 * ‖g‖)
    have habs : Tendsto (fun i => |(∫ x, g x ∂↑(probOfDensity μ (G i).f (G i).dens))
        - ∫ x, g x ∂↑(probOfDensity μ (W i).f (W i).dens)|) atTop (nhds 0) :=
      squeeze_zero (fun i => abs_nonneg _) hbound hupper
    have habs2 : Tendsto (fun i => ‖(∫ x, g x ∂↑(probOfDensity μ (G i).f (G i).dens))
        - ∫ x, g x ∂↑(probOfDensity μ (W i).f (W i).dens)‖) atTop (nhds 0) := by
      simpa only [Real.norm_eq_abs] using habs
    exact tendsto_zero_iff_norm_tendsto_zero.mpr habs2
  have hmain : Tendsto (fun i => ∫ x, g x ∂↑(probOfDensity μ (G i).f (G i).dens)) atTop
      (nhds (∫ x, g x ∂↑P)) := by
    have hsum := hzero.add (hconv g)
    have heq : (fun i => ((∫ x, g x ∂↑(probOfDensity μ (G i).f (G i).dens))
        - ∫ x, g x ∂↑(probOfDensity μ (W i).f (W i).dens))
        + ∫ x, g x ∂↑(probOfDensity μ (W i).f (W i).dens))
        = (fun i => ∫ x, g x ∂↑(probOfDensity μ (G i).f (G i).dens)) := by
      funext i
      ring
    rw [heq] at hsum
    simpa using hsum
  exact hmain
  /- @proof-region region.target-node.session.49934e94d76f00a0 end -/

end Statlib.Imported
