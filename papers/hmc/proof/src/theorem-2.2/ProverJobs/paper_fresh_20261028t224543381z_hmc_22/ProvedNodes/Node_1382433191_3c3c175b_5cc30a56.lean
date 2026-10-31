import ProverJobs.paper_fresh_20261028t224543381z_hmc_22.Vocabulary
import ProverJobs.paper_fresh_20261028t224543381z_hmc_22.Base

namespace PaperProofTasks.paper_fresh_20261028t224543381z_hmc_22

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
open _root_.PaperProofTasks.paper_fresh_20261028t224543381z_hmc_22.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
namespace Statlib.Imported


set_option autoImplicit false in
theorem statopia_math_node_1382433191_3c3c175b : ∀ (d : ℕ) (hd : 0 < d) (U : HMCState d → ℝ) (hU : Measurable U)
    (π : Measure (HMCState d)) [IsProbabilityMeasure π],
    (∃ c : ℝ, 0 < c ∧
        π = volume.withDensity (fun x => ENNReal.ofReal (c * Real.exp (-(U x))))) →
      ∀ (S : ℝ) (N : Set (HMCState d)), π N = 0 →
        ∃ x : HMCState d, S ≤ ‖x‖ ∧ x ∉ N := by
  /- @proof-region region.target-node.session.9c24f329dae98670 begin -/
  intro d hd U hU π hprob hdens S N hN
  obtain ⟨c, hc, hπeq⟩ := hdens
  set f : HMCState d → ℝ≥0∞ := fun x => ENNReal.ofReal (c * Real.exp (-(U x))) with hf_def
  have hf_meas : Measurable f := by
    rw [hf_def]
    exact ENNReal.measurable_ofReal.comp (measurable_const.mul (Real.measurable_exp.comp hU.neg))
  have hf_pos : ∀ x, f x ≠ 0 := by
    intro x
    rw [hf_def]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (mul_pos hc (Real.exp_pos _)))
  set B : Set (HMCState d) := {x | S ≤ ‖x‖} with hB_def
  have hB_meas : MeasurableSet B := by
    rw [hB_def]
    exact (isClosed_le continuous_const continuous_norm).measurableSet
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨v, hv⟩ := exists_ne (0 : HMCState d)
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set t : ℝ := (|S| + 2) / ‖v‖ with ht_def
  have ht_pos : 0 < t := by
    rw [ht_def]
    exact div_pos (by positivity) hvpos
  set y : HMCState d := t • v with hy_def
  have hy_norm : ‖y‖ = |S| + 2 := by
    rw [hy_def, norm_smul, Real.norm_eq_abs, abs_of_pos ht_pos, ht_def]
    exact div_mul_cancel₀ _ (ne_of_gt hvpos)
  have hy_ge : S + 2 ≤ ‖y‖ := by
    rw [hy_norm]
    linarith [le_abs_self S]
  have hball_sub : Metric.ball y 1 ⊆ B := by
    intro z hz
    have hzdist : dist z y < 1 := Metric.mem_ball.mp hz
    have hle : ‖y‖ ≤ ‖y - z‖ + ‖z‖ := by
      have h := norm_add_le (y - z) z
      rwa [sub_add_cancel] at h
    have hdist : ‖y - z‖ = dist y z := (dist_eq_norm y z).symm
    have hcomm : dist z y = dist y z := dist_comm z y
    have hmem : z ∈ {x : HMCState d | S ≤ ‖x‖} := by
      rw [Set.mem_setOf_eq]
      linarith
    rwa [hB_def]
  have hball_pos : (0 : ℝ≥0∞) < volume (Metric.ball y 1) :=
    Metric.measure_ball_pos volume y (by norm_num)
  have hvolB : volume B ≠ 0 := by
    intro h0
    have hle : volume (Metric.ball y 1) ≤ volume B := MeasureTheory.measure_mono hball_sub
    rw [h0] at hle
    exact (not_le.mpr hball_pos) hle
  have hπpos : π B ≠ 0 := by
    intro h0
    rw [hπeq] at h0
    have hz : volume ({x : HMCState d | f x ≠ 0} ∩ B) = 0 :=
      (MeasureTheory.withDensity_apply_eq_zero (μ := volume) (f := f) (s := B) hf_meas).mp h0
    have hsupp : {x : HMCState d | f x ≠ 0} = Set.univ := by
      ext x
      simp [hf_pos x]
    rw [hsupp, Set.univ_inter] at hz
    exact hvolB hz
  by_contra hcon
  push_neg at hcon
  have hBN : B ⊆ N := by
    intro x hx
    rw [hB_def] at hx
    simp only [Set.mem_setOf_eq] at hx
    exact hcon x hx
  have hmono : π B ≤ π N := MeasureTheory.measure_mono hBN
  rw [hN] at hmono
  exact hπpos (le_antisymm hmono (zero_le _))
  /- @proof-region region.target-node.session.9c24f329dae98670 end -/

end Statlib.Imported

end

