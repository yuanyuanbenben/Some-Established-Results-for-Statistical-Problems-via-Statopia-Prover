import ProverJobs.paper_fresh_20261028t151409527z_hmc_v5.Vocabulary
import ProverJobs.paper_fresh_20261028t151409527z_hmc_v5.Base

namespace PaperProofTasks.paper_fresh_20261028t151409527z_hmc_v5

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal
open _root_.PaperProofTasks.paper_fresh_20261028t151409527z_hmc_v5.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal
namespace Statlib.Imported
open _root_.Statlib

set_option autoImplicit false in
theorem statopia_math_node_170196137_a4c2281b : ∀ (d : ℕ) (U : HMCState d → ℝ) (L : ℕ) (ε : ℝ)
    (hU : Differentiable ℝ U),
    Measurable (hmcKernel U L ε) ∧
      (∀ x : HMCState d,
        ENNReal.ofReal (1 - ∫ p, hmcAlpha U L ε x p ∂(standardGaussianMomentum d))
          • Measure.dirac x ≤ hmcKernel U L ε x) := by
  /- @proof-region region.target-node.session.d3ec55cd0c1f1aff begin -/
  intro d U L ε hU
  have hUm : Measurable U := hU.continuous.measurable
  have hgrad : Measurable fun x : HMCState d => gradient U x := by
    have hfd : Measurable fun x : HMCState d => fderiv ℝ U x := measurable_fderiv ℝ U
    exact ((InnerProductSpace.toDual ℝ (HMCState d)).symm.continuous.measurable).comp hfd
  have hstep : Measurable (leapStep U ε) := by
    have hg : Measurable fun z : HMCState d × HMCState d => gradient U z.1 :=
      hgrad.comp measurable_fst
    have hpH : Measurable fun z : HMCState d × HMCState d => z.2 - (ε / 2) • gradient U z.1 :=
      measurable_snd.sub (hg.const_smul (ε / 2))
    have hx : Measurable fun z : HMCState d × HMCState d =>
        z.1 + ε • (z.2 - (ε / 2) • gradient U z.1) :=
      measurable_fst.add (hpH.const_smul ε)
    have hp : Measurable fun z : HMCState d × HMCState d =>
        (z.2 - (ε / 2) • gradient U z.1) -
          (ε / 2) • gradient U (z.1 + ε • (z.2 - (ε / 2) • gradient U z.1)) :=
      hpH.sub ((hgrad.comp hx).const_smul (ε / 2))
    exact hx.prodMk hp
  have hflow : Measurable (leapFlow U ε L) := by
    induction L with
    | zero => simpa [leapFlow] using measurable_id
    | succ n ih =>
        have hs : leapFlow U ε (n + 1) = leapFlow U ε n ∘ leapStep U ε := rfl
        rw [hs]
        exact ih.comp hstep
  have ha : Measurable fun z : HMCState d × HMCState d => hmcAlpha U L ε z.1 z.2 := by
    have hq1 : Measurable fun z : HMCState d × HMCState d => (leapFlow U ε L z).1 :=
      measurable_fst.comp hflow
    have hpn : Measurable fun z : HMCState d × HMCState d => ‖z.2‖ := measurable_snd.norm
    have hqn : Measurable fun z : HMCState d × HMCState d => ‖(leapFlow U ε L z).2‖ :=
      (measurable_snd.comp hflow).norm
    have hp2 : Measurable fun z : HMCState d × HMCState d => ‖z.2‖ * ‖z.2‖ := hpn.mul hpn
    have hq2 : Measurable fun z : HMCState d × HMCState d =>
        ‖(leapFlow U ε L z).2‖ * ‖(leapFlow U ε L z).2‖ := hqn.mul hqn
    have harg : Measurable fun z : HMCState d × HMCState d =>
        U z.1 - U (leapFlow U ε L z).1 + (1 / 2) * (‖z.2‖ * ‖z.2‖) -
          (1 / 2) * (‖(leapFlow U ε L z).2‖ * ‖(leapFlow U ε L z).2‖) :=
      (((hUm.comp measurable_fst).sub (hUm.comp hq1)).add (hp2.const_mul (1 / 2))).sub
        (hq2.const_mul (1 / 2))
    have hsq : ∀ t : ℝ, t ^ 2 = t * t := fun t => by ring
    have hexp : Measurable fun z : HMCState d × HMCState d =>
        min 1 (Real.exp (U z.1 - U (leapFlow U ε L z).1 + (1 / 2) * (‖z.2‖ * ‖z.2‖) -
          (1 / 2) * (‖(leapFlow U ε L z).2‖ * ‖(leapFlow U ε L z).2‖))) :=
      Measurable.min measurable_const (Real.measurable_exp.comp harg)
    simp only [hmcAlpha, hsq]
    exact hexp
  have hprob : IsProbabilityMeasure (standardGaussianMomentum d) := by
    unfold standardGaussianMomentum
    exact Measure.isProbabilityMeasure_map
      ((EuclideanSpace.measurableEquiv (Fin d)).symm.measurable.aemeasurable)
  haveI := hprob
  have hcoe : ∀ s : Set (HMCState d), MeasurableSet s →
      Measurable fun z : HMCState d × HMCState d =>
        (ENNReal.ofReal (hmcAlpha U L ε z.1 z.2) • Measure.dirac (leapFlow U ε L z).1
          + ENNReal.ofReal (1 - hmcAlpha U L ε z.1 z.2) • Measure.dirac z.1) s := by
    intro s hs
    have hind : Measurable fun y : HMCState d => s.indicator (1 : HMCState d → ENNReal) y :=
      Measurable.indicator measurable_const hs
    have hofA : Measurable fun z : HMCState d × HMCState d =>
        ENNReal.ofReal (hmcAlpha U L ε z.1 z.2) := by
      measurability
    have hofB : Measurable fun z : HMCState d × HMCState d =>
        ENNReal.ofReal (1 - hmcAlpha U L ε z.1 z.2) := by
      measurability
    have h1 : Measurable fun z : HMCState d × HMCState d =>
        ENNReal.ofReal (hmcAlpha U L ε z.1 z.2) * s.indicator 1 (leapFlow U ε L z).1 :=
      hofA.mul (hind.comp (measurable_fst.comp hflow))
    have h2 : Measurable fun z : HMCState d × HMCState d =>
        ENNReal.ofReal (1 - hmcAlpha U L ε z.1 z.2) * s.indicator 1 z.1 :=
      hofB.mul (hind.comp measurable_fst)
    have hpt : ∀ z : HMCState d × HMCState d,
        (ENNReal.ofReal (hmcAlpha U L ε z.1 z.2) • Measure.dirac (leapFlow U ε L z).1
          + ENNReal.ofReal (1 - hmcAlpha U L ε z.1 z.2) • Measure.dirac z.1) s
        = ENNReal.ofReal (hmcAlpha U L ε z.1 z.2) * s.indicator 1 (leapFlow U ε L z).1
          + ENNReal.ofReal (1 - hmcAlpha U L ε z.1 z.2) * s.indicator 1 z.1 := by
      intro z
      rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
        Measure.dirac_apply' _ hs, Measure.dirac_apply' _ hs, smul_eq_mul, smul_eq_mul]
    simp only [hpt]
    exact h1.add h2
  have hmix : Measurable fun z : HMCState d × HMCState d =>
      ENNReal.ofReal (hmcAlpha U L ε z.1 z.2) • Measure.dirac (leapFlow U ε L z).1
        + ENNReal.ofReal (1 - hmcAlpha U L ε z.1 z.2) • Measure.dirac z.1 :=
    Measure.measurable_of_measurable_coe _ hcoe
  have hpair : ∀ x : HMCState d, Measurable fun p0 : HMCState d => (x, p0) :=
    fun x => measurable_const.prodMk measurable_id
  have hae : ∀ x : HMCState d, AEMeasurable (fun p0 : HMCState d =>
      ENNReal.ofReal (hmcAlpha U L ε x p0) • Measure.dirac (leapFlow U ε L (x, p0)).1
        + ENNReal.ofReal (1 - hmcAlpha U L ε x p0) • Measure.dirac x)
      (standardGaussianMomentum d) := by
    intro x
    exact (hmix.comp (hpair x)).aemeasurable
  constructor
  · refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    have hf : Measurable fun z : HMCState d × HMCState d =>
        (ENNReal.ofReal (hmcAlpha U L ε z.1 z.2) • Measure.dirac (leapFlow U ε L z).1
          + ENNReal.ofReal (1 - hmcAlpha U L ε z.1 z.2) • Measure.dirac z.1) s := hcoe s hs
    have hlin : Measurable fun x : HMCState d => ∫⁻ p0,
        (ENNReal.ofReal (hmcAlpha U L ε x p0) • Measure.dirac (leapFlow U ε L (x, p0)).1
          + ENNReal.ofReal (1 - hmcAlpha U L ε x p0) • Measure.dirac x) s
        ∂(standardGaussianMomentum d) :=
      Measurable.lintegral_prod_right' hf
    have hval : ∀ x : HMCState d, (hmcKernel U L ε x) s = ∫⁻ p0,
        (ENNReal.ofReal (hmcAlpha U L ε x p0) • Measure.dirac (leapFlow U ε L (x, p0)).1
          + ENNReal.ofReal (1 - hmcAlpha U L ε x p0) • Measure.dirac x) s
        ∂(standardGaussianMomentum d) := by
      intro x
      unfold hmcKernel
      exact Measure.bind_apply hs (hae x)
    simp only [hval]
    exact hlin
  · intro x
    have hmeasa : Measurable fun p : HMCState d => hmcAlpha U L ε x p := ha.comp (hpair x)
    have hge0 : ∀ p : HMCState d, 0 ≤ hmcAlpha U L ε x p := fun p => by
      simp only [hmcAlpha]
      exact le_min zero_le_one (Real.exp_pos _).le
    have hle1 : ∀ p : HMCState d, hmcAlpha U L ε x p ≤ 1 := fun p => by
      simp only [hmcAlpha]
      exact min_le_left _ _
    have hIA : Integrable (fun p : HMCState d => hmcAlpha U L ε x p)
        (standardGaussianMomentum d) := by
      refine Integrable.of_bound hmeasa.aestronglyMeasurable 1 (Eventually.of_forall fun p => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hge0 p)]
      exact hle1 p
    have hI1 : Integrable (fun _ : HMCState d => (1 : ℝ)) (standardGaussianMomentum d) :=
      integrable_const 1
    have hone : ∫ _ : HMCState d, (1 : ℝ) ∂(standardGaussianMomentum d) = 1 := by simp
    have hInt : ∫ p, (1 - hmcAlpha U L ε x p) ∂(standardGaussianMomentum d)
        = 1 - ∫ p, hmcAlpha U L ε x p ∂(standardGaussianMomentum d) := by
      rw [integral_sub hI1 hIA, hone]
    have hid : ENNReal.ofReal (1 - ∫ p, hmcAlpha U L ε x p ∂(standardGaussianMomentum d))
        = ∫⁻ p, ENNReal.ofReal (1 - hmcAlpha U L ε x p) ∂(standardGaussianMomentum d) := by
      rw [← hInt]
      refine ofReal_integral_eq_lintegral_ofReal (hI1.sub hIA) (Eventually.of_forall fun p => ?_)
      show (0 : ℝ) ≤ 1 - hmcAlpha U L ε x p
      linarith [hle1 p]
    have hatom : ENNReal.ofReal (1 - ∫ p, hmcAlpha U L ε x p ∂(standardGaussianMomentum d))
        ≤ (hmcKernel U L ε x) {x} := by
      have hb : (hmcKernel U L ε x) {x} = ∫⁻ p0,
          (ENNReal.ofReal (hmcAlpha U L ε x p0) • Measure.dirac (leapFlow U ε L (x, p0)).1
            + ENNReal.ofReal (1 - hmcAlpha U L ε x p0) • Measure.dirac x) {x}
          ∂(standardGaussianMomentum d) := by
        unfold hmcKernel
        exact Measure.bind_apply (measurableSet_singleton x) (hae x)
      rw [hb, hid]
      refine lintegral_mono fun p0 => ?_
      rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
        Measure.dirac_apply_of_mem (Set.mem_singleton x), smul_eq_mul, smul_eq_mul, mul_one]
      calc ENNReal.ofReal (1 - hmcAlpha U L ε x p0)
          = 0 + ENNReal.ofReal (1 - hmcAlpha U L ε x p0) := (zero_add _).symm
        _ ≤ ENNReal.ofReal (hmcAlpha U L ε x p0) *
              (Measure.dirac (leapFlow U ε L (x, p0)).1) {x} +
              ENNReal.ofReal (1 - hmcAlpha U L ε x p0) :=
            add_le_add (zero_le _) le_rfl
    intro s
    rw [Measure.smul_apply, Measure.dirac_apply x s, smul_eq_mul]
    by_cases hx : x ∈ s
    · rw [Set.indicator_of_mem hx]
      have hc1 : ENNReal.ofReal (1 - ∫ p, hmcAlpha U L ε x p ∂(standardGaussianMomentum d)) *
          (1 : HMCState d → ENNReal) x
          = ENNReal.ofReal (1 - ∫ p, hmcAlpha U L ε x p ∂(standardGaussianMomentum d)) := by
        simp
      rw [hc1]
      exact hatom.trans (measure_mono (Set.singleton_subset_iff.mpr hx))
    · rw [Set.indicator_of_notMem hx]
      simp
  /- @proof-region region.target-node.session.d3ec55cd0c1f1aff end -/

end Statlib.Imported
end

