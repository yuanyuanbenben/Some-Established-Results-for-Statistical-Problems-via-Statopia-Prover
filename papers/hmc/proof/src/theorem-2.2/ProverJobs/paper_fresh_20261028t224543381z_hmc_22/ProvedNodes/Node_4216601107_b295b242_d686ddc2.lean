import ProverJobs.paper_fresh_20261028t224543381z_hmc_22.Vocabulary
import ProverJobs.paper_fresh_20261028t224543381z_hmc_22.Base
import ProverJobs.paper_fresh_20261028t224543381z_hmc_22.ProvedNodes.Node_3672800187_e652fc75_39c024da

namespace PaperProofTasks.paper_fresh_20261028t224543381z_hmc_22
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
open _root_.PaperProofTasks.paper_fresh_20261028t224543381z_hmc_22.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
namespace Statlib.Imported


set_option autoImplicit false in
theorem statopia_math_node_4216601107_b295b242 : ∀ (d : ℕ),
    (MeasureTheory.Measure.pi (fun _ : Fin d => ProbabilityTheory.gaussianReal (0 : ℝ) 1)) =
      ENNReal.ofReal (((Real.sqrt (2 * Real.pi)) ^ d))⁻¹ •
        (volume : MeasureTheory.Measure (Fin d → ℝ)).withDensity
          (fun x : Fin d → ℝ =>
            ENNReal.ofReal (Real.exp (-(1 / 2) * ∑ i : Fin d, (x i) ^ 2))) := by
  /- @proof-region region.target-node.session.b3d9fc8892b30a8d begin -/
  intro d
  have hstep1 : ∀ (s : Set ℝ), MeasurableSet s →
      (ProbabilityTheory.gaussianReal (0 : ℝ) 1) s =
        ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹) *
          ∫⁻ t in s, ENNReal.ofReal (Real.exp (-(t ^ 2) / 2)) := by
    intro s hs
    rw [ProbabilityTheory.gaussianReal, if_neg (by simp : ¬ (1 : NNReal) = 0), withDensity_apply']
    have hpt : ∀ t : ℝ, gaussianPDF (0 : ℝ) 1 t =
        ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹) *
          ENNReal.ofReal (Real.exp (-(t ^ 2) / 2)) := by
      intro t
      simp only [ProbabilityTheory.gaussianPDF, gaussianPDFReal_def, NNReal.coe_one, mul_one,
        sub_zero]
      rw [ENNReal.ofReal_mul (inv_nonneg.mpr (Real.sqrt_nonneg _))]
    rw [lintegral_congr hpt, lintegral_const_mul]
    measurability
  have hstep2 : ∀ (s : Fin d → Set ℝ), (∀ i, MeasurableSet (s i)) →
      ∫⁻ x in Set.univ.pi s,
          ENNReal.ofReal (Real.exp (-(1 / 2) * ∑ i : Fin d, (x i) ^ 2)) ∂(volume : Measure (Fin d → ℝ)) =
        ∏ i : Fin d, ∫⁻ t in s i, ENNReal.ofReal (Real.exp (-(t ^ 2) / 2)) := by
    exact fun s hs => statopia_math_node_3672800187_e652fc75 d s hs
  apply Measure.pi_eq
  intro s hs
  have h2 : (∏ i : Fin d, ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹)) =
      ENNReal.ofReal (((Real.sqrt (2 * Real.pi)) ^ d))⁻¹ := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← inv_pow, ENNReal.ofReal_pow]
    exact inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hL : (∏ i : Fin d, (ProbabilityTheory.gaussianReal (0 : ℝ) 1) (s i)) =
      ENNReal.ofReal (((Real.sqrt (2 * Real.pi)) ^ d))⁻¹ *
        ∏ i : Fin d, ∫⁻ t in s i, ENNReal.ofReal (Real.exp (-(t ^ 2) / 2)) := by
    have h1 : (∏ i : Fin d, (ProbabilityTheory.gaussianReal (0 : ℝ) 1) (s i)) =
        ∏ i : Fin d, (ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹) *
          ∫⁻ t in s i, ENNReal.ofReal (Real.exp (-(t ^ 2) / 2))) :=
      Finset.prod_congr rfl (fun i _ => hstep1 (s i) (hs i))
    rw [h1, Finset.prod_mul_distrib, h2]
  have hR : (ENNReal.ofReal (((Real.sqrt (2 * Real.pi)) ^ d))⁻¹ •
      (volume : Measure (Fin d → ℝ)).withDensity
        (fun x : Fin d → ℝ =>
          ENNReal.ofReal (Real.exp (-(1 / 2) * ∑ i : Fin d, (x i) ^ 2)))) (Set.univ.pi s) =
      ENNReal.ofReal (((Real.sqrt (2 * Real.pi)) ^ d))⁻¹ *
        ∏ i : Fin d, ∫⁻ t in s i, ENNReal.ofReal (Real.exp (-(t ^ 2) / 2)) := by
    have hW : (volume : Measure (Fin d → ℝ)).withDensity
        (fun x : Fin d → ℝ => ENNReal.ofReal (Real.exp (-(1 / 2) * ∑ i : Fin d, (x i) ^ 2))) (Set.univ.pi s) =
        ∫⁻ x in Set.univ.pi s, ENNReal.ofReal (Real.exp (-(1 / 2) * ∑ i : Fin d, (x i) ^ 2)) ∂(volume : Measure (Fin d → ℝ)) := by
      rw [withDensity_apply]
      exact MeasurableSet.univ_pi hs
    rw [Measure.smul_apply, hW, hstep2 s hs]
    exact smul_eq_mul _ _
  rw [hR, hL]
  /- @proof-region region.target-node.session.b3d9fc8892b30a8d end -/

end Statlib.Imported

end

