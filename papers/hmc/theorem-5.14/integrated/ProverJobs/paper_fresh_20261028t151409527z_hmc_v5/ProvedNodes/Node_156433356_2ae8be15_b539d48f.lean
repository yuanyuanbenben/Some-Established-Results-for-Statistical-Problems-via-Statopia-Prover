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
theorem statopia_math_node_156433356_2ae8be15 : ∀ (d : ℕ) (U : HMCState d → ℝ) (L : ℕ) (ε : ℝ)
    (halpha_nonneg : ∀ (x p : HMCState d), 0 ≤ hmcAlpha U L ε x p)
    (halpha_le_one : ∀ (x p : HMCState d), hmcAlpha U L ε x p ≤ 1)
    (halpha_aemeasurable : ∀ x : HMCState d,
      AEMeasurable (fun p : HMCState d => hmcAlpha U L ε x p) (standardGaussianMomentum d))
    (halpha_integrable : ∀ x : HMCState d,
      Integrable (fun p : HMCState d => hmcAlpha U L ε x p) (standardGaussianMomentum d))
    (h_integrand_aemeasurable : ∀ x : HMCState d,
      AEMeasurable (fun p : HMCState d =>
        ENNReal.ofReal (hmcAlpha U L ε x p) • Measure.dirac (leapFlow U ε L (x, p)).1 +
          ENNReal.ofReal (1 - hmcAlpha U L ε x p) • Measure.dirac x)
        (standardGaussianMomentum d))
    (x : HMCState d) (A : Set (HMCState d)) (hA : MeasurableSet A),
    ENNReal.ofReal (1 - ∫ p, hmcAlpha U L ε x p ∂(standardGaussianMomentum d)) *
        Measure.dirac x A ≤ hmcKernel U L ε x A := by
  /- @proof-region region.target-node.session.3cbde429249509cd begin -/
  intro d U L ε hα_nonneg hα_le_one hα_aem hα_intg hF_aem x A hA
  haveI hprob : IsProbabilityMeasure (standardGaussianMomentum d) := by
    unfold standardGaussianMomentum
    exact Measure.isProbabilityMeasure_map
      (EuclideanSpace.measurableEquiv (Fin d)).symm.measurable.aemeasurable
  have hαm : AEMeasurable (fun p : HMCState d => hmcAlpha U L ε x p) (standardGaussianMomentum d) :=
    hα_aem x
  have hα_int : Integrable (fun p : HMCState d => hmcAlpha U L ε x p) (standardGaussianMomentum d) :=
    hα_intg x
  have hone_int : Integrable (fun p : HMCState d => (1:ℝ)) (standardGaussianMomentum d) :=
    integrable_const 1
  have hsub_int :
      Integrable (fun p : HMCState d => (1:ℝ) - hmcAlpha U L ε x p) (standardGaussianMomentum d) :=
    hone_int.sub hα_int
  have hnonneg :
      0 ≤ᶠ[ae (standardGaussianMomentum d)] (fun p : HMCState d => (1:ℝ) - hmcAlpha U L ε x p) := by
    filter_upwards with p
    simpa [sub_nonneg] using hα_le_one x p
  have hconst : ∫ p : HMCState d, (1:ℝ) ∂(standardGaussianMomentum d) = 1 := by
    rw [MeasureTheory.integral_const]
    simp [MeasureTheory.Measure.real, measure_univ]
  have hsub_eq :
      ∫ p : HMCState d, ((1:ℝ) - hmcAlpha U L ε x p) ∂(standardGaussianMomentum d)
        = 1 - ∫ p : HMCState d, hmcAlpha U L ε x p ∂(standardGaussianMomentum d) := by
    rw [MeasureTheory.integral_sub hone_int hα_int, hconst]
  have hlintegral :
      ∫⁻ p : HMCState d, ENNReal.ofReal ((1:ℝ) - hmcAlpha U L ε x p)
          ∂(standardGaussianMomentum d)
        = ENNReal.ofReal
            (1 - ∫ p : HMCState d, hmcAlpha U L ε x p ∂(standardGaussianMomentum d)) := by
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hsub_int hnonneg, hsub_eq]
  have hc_aemeas :
      AEMeasurable (fun p : HMCState d => ENNReal.ofReal ((1:ℝ) - hmcAlpha U L ε x p))
        (standardGaussianMomentum d) := by
    have h1 : AEMeasurable (fun p : HMCState d => (1:ℝ) - hmcAlpha U L ε x p)
        (standardGaussianMomentum d) :=
      AEMeasurable.sub aemeasurable_const hαm
    exact Measurable.comp_aemeasurable' (g := ENNReal.ofReal) ENNReal.measurable_ofReal h1
  have hkernel_eq : hmcKernel U L ε x
      = (fun p : HMCState d =>
          ENNReal.ofReal (hmcAlpha U L ε x p) • Measure.dirac (leapFlow U ε L (x, p)).1 +
            ENNReal.ofReal (1 - hmcAlpha U L ε x p) • Measure.dirac x) ∘ₘ
          (standardGaussianMomentum d) := by
    unfold hmcKernel hmcAlpha
    rfl
  have hker : (hmcKernel U L ε x) A
      = ∫⁻ p : HMCState d,
          (ENNReal.ofReal (hmcAlpha U L ε x p) • Measure.dirac (leapFlow U ε L (x, p)).1 +
            ENNReal.ofReal (1 - hmcAlpha U L ε x p) • Measure.dirac x) A
          ∂(standardGaussianMomentum d) := by
    rw [hkernel_eq]
    exact MeasureTheory.Measure.bind_apply hA (hF_aem x)
  have hmul :
      (∫⁻ p : HMCState d, ENNReal.ofReal ((1:ℝ) - hmcAlpha U L ε x p) * (Measure.dirac x) A
          ∂(standardGaussianMomentum d))
        = (∫⁻ p : HMCState d, ENNReal.ofReal ((1:ℝ) - hmcAlpha U L ε x p)
            ∂(standardGaussianMomentum d)) * (Measure.dirac x) A :=
    MeasureTheory.lintegral_mul_const'' ((Measure.dirac x) A) hc_aemeas
  have hpt : ∀ p : HMCState d,
      ENNReal.ofReal ((1:ℝ) - hmcAlpha U L ε x p) * (Measure.dirac x) A
        ≤ (ENNReal.ofReal (hmcAlpha U L ε x p) • Measure.dirac (leapFlow U ε L (x, p)).1 +
            ENNReal.ofReal (1 - hmcAlpha U L ε x p) • Measure.dirac x) A := by
    intro p
    rw [MeasureTheory.Measure.add_apply, MeasureTheory.Measure.smul_apply,
      MeasureTheory.Measure.smul_apply, smul_eq_mul, smul_eq_mul]
    calc ENNReal.ofReal ((1:ℝ) - hmcAlpha U L ε x p) * (Measure.dirac x) A
        = 0 + ENNReal.ofReal ((1:ℝ) - hmcAlpha U L ε x p) * (Measure.dirac x) A :=
          (zero_add _).symm
      _ ≤ ENNReal.ofReal (hmcAlpha U L ε x p) * (Measure.dirac (leapFlow U ε L (x, p)).1) A
            + ENNReal.ofReal ((1:ℝ) - hmcAlpha U L ε x p) * (Measure.dirac x) A :=
          add_le_add (zero_le _) le_rfl
  have hbound :
      (∫⁻ p : HMCState d, ENNReal.ofReal ((1:ℝ) - hmcAlpha U L ε x p) * (Measure.dirac x) A
          ∂(standardGaussianMomentum d))
        ≤ ∫⁻ p : HMCState d,
            (ENNReal.ofReal (hmcAlpha U L ε x p) • Measure.dirac (leapFlow U ε L (x, p)).1 +
              ENNReal.ofReal (1 - hmcAlpha U L ε x p) • Measure.dirac x) A
            ∂(standardGaussianMomentum d) :=
    MeasureTheory.lintegral_mono hpt
  rw [← hlintegral, ← hmul]
  exact hbound.trans (le_of_eq hker.symm)
  /- @proof-region region.target-node.session.3cbde429249509cd end -/

end Statlib.Imported
end

