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
theorem statopia_math_node_2488397496_e86e6104 : ∀ (d : ℕ) (hd : 0 < d) (U : HMCState d → ℝ) (hU : Measurable U)
    (π : Measure (HMCState d)) (c : ℝ≥0∞) (R : ℝ)
    (hc_ne_zero : c ≠ 0) (hc_ne_top : c ≠ ⊤)
    (hπ_eq : π = c • volume.withDensity (fun x : HMCState d => ENNReal.ofReal (Real.exp (-(U x))))),
    π {x : HMCState d | R < ‖x‖} > 0 := by
  /- @proof-region region.target-node.session.eaea66370ddde967 begin -/
  intro d hd U hU π c R hc0 hcTop hπ
  have hf_meas : Measurable fun x : HMCState d => ENNReal.ofReal (Real.exp (-U x)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hU.neg)
  have hS_open : IsOpen {x : HMCState d | R < ‖x‖} := isOpen_Ioi.preimage continuous_norm
  have hS_meas : MeasurableSet {x : HMCState d | R < ‖x‖} := hS_open.measurableSet
  obtain ⟨i⟩ : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  haveI : Nonempty (Fin d) := ⟨i⟩
  set y : HMCState d := EuclideanSpace.single i (1 : ℝ) with hydef
  have hy : y ≠ 0 := by
    intro h
    have h2 := congrArg (fun z : HMCState d => z.ofLp i) h
    simpa [hydef, EuclideanSpace.single_apply] using h2
  have hny : (0 : ℝ) < ‖y‖ := norm_pos_iff.mpr hy
  have hS_ne : {x : HMCState d | R < ‖x‖}.Nonempty := by
    refine ⟨((max R 0 + 1) / ‖y‖) • y, ?_⟩
    have hpos : (0 : ℝ) < max R 0 + 1 := by
      have hle := le_max_right R 0
      linarith
    have h1 : ‖((max R 0 + 1) / ‖y‖) • y‖ = max R 0 + 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hpos hny),
        div_mul_cancel₀ _ (ne_of_gt hny)]
    show R < ‖((max R 0 + 1) / ‖y‖) • y‖
    rw [h1]
    exact lt_of_le_of_lt (le_max_left R 0) (lt_add_one _)
  haveI hvol : (volume : Measure (HMCState d)).IsOpenPosMeasure := inferInstance
  have hS_pos : 0 < volume {x : HMCState d | R < ‖x‖} := hS_open.measure_pos volume hS_ne
  have hI : 0 < ∫⁻ x in {x | R < ‖x‖}, ENNReal.ofReal (Real.exp (-U x)) ∂volume := by
    have hsupp : Function.support (fun x : HMCState d => ENNReal.ofReal (Real.exp (-U x)))
        = Set.univ := by
      ext x
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
    refine (MeasureTheory.lintegral_pos_iff_support
      (μ := volume.restrict {x : HMCState d | R < ‖x‖}) hf_meas).mpr ?_
    rw [hsupp]
    simpa using hS_pos
  have hwD : (volume.withDensity fun x : HMCState d => ENNReal.ofReal (Real.exp (-U x)))
        {x | R < ‖x‖}
      = ∫⁻ x in {x | R < ‖x‖}, ENNReal.ofReal (Real.exp (-U x)) ∂volume :=
    MeasureTheory.withDensity_apply _ hS_meas
  have hcalc : π {x | R < ‖x‖}
      = c * ∫⁻ x in {x | R < ‖x‖}, ENNReal.ofReal (Real.exp (-U x)) ∂volume := by
    rw [hπ, MeasureTheory.Measure.smul_apply, hwD, smul_eq_mul]
  rw [hcalc]
  exact ENNReal.mul_pos (ne_of_gt (pos_iff_ne_zero.mpr hc0)) (ne_of_gt hI)
  /- @proof-region region.target-node.session.eaea66370ddde967 end -/

end Statlib.Imported
end

