import ProverJobs.paper_fresh_20261028t151409527z_hmc_v5.Vocabulary
import ProverJobs.paper_fresh_20261028t151409527z_hmc_v5.Base
import ProverJobs.paper_fresh_20261028t151409527z_hmc_v5.ProvedNodes.Node_156433356_2ae8be15_b539d48f

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
theorem statopia_math_node_2756182807_18c8f00c : ∀ (d : ℕ) (U : HMCState d → ℝ) (L : ℕ) (ε : ℝ)
    (hdom : ∀ x : HMCState d,
      ENNReal.ofReal (1 - ∫ p, hmcAlpha U L ε x p ∂(standardGaussianMomentum d)) •
          Measure.dirac x ≤ hmcKernel U L ε x)
    (hRej_nonneg : ∀ x : HMCState d,
      0 ≤ 1 - ∫ p, hmcAlpha U L ε x p ∂(standardGaussianMomentum d))
    (hRej_le_one : ∀ x : HMCState d,
      1 - ∫ p, hmcAlpha U L ε x p ∂(standardGaussianMomentum d) ≤ 1)
    (hP : Measurable (hmcKernel U L ε)),
    ∀ (n : ℕ) (x : HMCState d),
      ENNReal.ofReal ((1 - ∫ p, hmcAlpha U L ε x p ∂(standardGaussianMomentum d)) ^ n) •
          Measure.dirac x ≤ kernelPow (hmcKernel U L ε) n x := by
  /- @proof-region region.target-node.session.99eea2eda6678cee begin -/
  intro d U L ε hdom hRej_nonneg hRej_le_one hP n x
  induction n with
  | zero =>
      simp [kernelPow]
  | succ n ih =>
      set R : ℝ := 1 - ∫ p, hmcAlpha U L ε x p ∂(standardGaussianMomentum d) with hR
      have hR0 : 0 ≤ R := by
        rw [hR]
        exact hRej_nonneg x
      have hdomR : ENNReal.ofReal R • Measure.dirac x ≤ hmcKernel U L ε x := by
        rw [hR]
        exact hdom x
      have ihn : ENNReal.ofReal (R ^ n) • Measure.dirac x ≤
          kernelPow (hmcKernel U L ε) n x := by
        simpa only [← hR] using ih
      have hmono : ∀ (m₁ m₂ : Measure (HMCState d)), m₁ ≤ m₂ →
          m₁.bind (hmcKernel U L ε) ≤ m₂.bind (hmcKernel U L ε) := by
        intro m₁ m₂ h12
        rw [Measure.le_iff]
        intro s hs
        have hb₁ : m₁.bind (hmcKernel U L ε) s =
            ∫⁻ a, hmcKernel U L ε a s ∂m₁ :=
          Measure.bind_apply hs hP.aemeasurable
        have hb₂ : m₂.bind (hmcKernel U L ε) s =
            ∫⁻ a, hmcKernel U L ε a s ∂m₂ :=
          Measure.bind_apply hs hP.aemeasurable
        rw [hb₁, hb₂]
        exact lintegral_mono' h12 le_rfl
      have hdirac : ∀ s : Set (HMCState d), MeasurableSet s →
          (∫⁻ a, hmcKernel U L ε a s ∂Measure.dirac x) = (hmcKernel U L ε x) s := by
        intro s hs
        have hb : (Measure.dirac x).bind (hmcKernel U L ε) s =
            ∫⁻ a, hmcKernel U L ε a s ∂Measure.dirac x :=
          Measure.bind_apply hs hP.aemeasurable
        have hdb : (Measure.dirac x).bind (hmcKernel U L ε) = hmcKernel U L ε x :=
          Measure.dirac_bind hP x
        rw [← hb, hdb]
      have hpow : ENNReal.ofReal (R ^ (n + 1)) =
          ENNReal.ofReal (R ^ n) * ENNReal.ofReal R := by
        rw [pow_succ, ENNReal.ofReal_mul (pow_nonneg hR0 n)]
      rw [hpow]
      refine le_trans
        (b := (ENNReal.ofReal (R ^ n) • Measure.dirac x).bind (hmcKernel U L ε)) ?_ ?_
      · rw [Measure.le_iff]
        intro s hs
        have hb : (ENNReal.ofReal (R ^ n) • Measure.dirac x).bind (hmcKernel U L ε) s =
            ∫⁻ a, hmcKernel U L ε a s ∂(ENNReal.ofReal (R ^ n) • Measure.dirac x) :=
          Measure.bind_apply hs (hP.aemeasurable.smul_measure (ENNReal.ofReal (R ^ n)))
        rw [hb, lintegral_smul_measure, hdirac s hs, Measure.smul_apply, smul_eq_mul,
          smul_eq_mul, mul_assoc]
        have hx : ENNReal.ofReal R * Measure.dirac x s ≤ hmcKernel U L ε x s := by
          simpa only [Measure.smul_apply, smul_eq_mul] using (Measure.le_iff.mp hdomR) s hs
        exact mul_le_mul_left' hx _
      · exact hmono _ _ ihn
  /- @proof-region region.target-node.session.99eea2eda6678cee end -/

end Statlib.Imported
end

