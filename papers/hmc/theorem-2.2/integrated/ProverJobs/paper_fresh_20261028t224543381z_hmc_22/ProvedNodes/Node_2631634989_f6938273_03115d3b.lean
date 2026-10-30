import ProverJobs.paper_fresh_20261028t224543381z_hmc_22.Vocabulary
import ProverJobs.paper_fresh_20261028t224543381z_hmc_22.Base
import ProverJobs.paper_fresh_20261028t224543381z_hmc_22.ProvedNodes.Node_1277695823_4133e1d3_ca2c2343
import ProverJobs.paper_fresh_20261028t224543381z_hmc_22.ProvedNodes.Node_2370441094_f2816c1d_79f1d6ed

namespace PaperProofTasks.paper_fresh_20261028t224543381z_hmc_22

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
open _root_.PaperProofTasks.paper_fresh_20261028t224543381z_hmc_22.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
namespace Statlib.Imported
open _root_.Statlib

set_option autoImplicit false in
theorem statopia_math_node_2631634989_f6938273 : ∀ (d : ℕ) (hd : 0 < d) (U : HMCState d → ℝ) (hU : Differentiable ℝ U)
    (ε : ℝ) (hε : 0 < ε) (L : ℕ) (hL : 1 ≤ L)
    (hgrad : ∀ N : ℝ, ∃ S : ℝ, ∀ z : HMCState d, S ≤ ‖z‖ → N * ‖z‖ ≤ ‖gradient U z‖)
    (hosc : ∃ C : ℝ, ∀ x y : HMCState d, ‖y‖ ≥ 2 * ‖x‖ → C ≤ 2 * ‖x‖ →
      ‖gradient U y‖ ≥ 3 * ‖gradient U x‖)
    (hjoint : ∀ R : ℝ, ∃ K : ℝ, ∀ x y : HMCState d, K ≤ ‖x‖ →
      (2 : ℝ) ^ L * ‖x‖ ≤ ‖y‖ → U x - U y - (1 / 2) * ‖x‖ ^ 2 ≤ -R)
    (δ : ℝ) (hδ : 0 < δ),
    ∃ S : ℝ, ∀ x : HMCState d, S ≤ ‖x‖ →
      (∫ p, acceptProb U ε L (x, p) ∂(gaussianMomentum d) ≤ δ ∧
        1 - ∫ p, (1 - acceptProb U ε L (x, p)) ∂(gaussianMomentum d) ≤ δ) := by
  /- @proof-region region.target-node.session.75c5bbcbdf8e47f7 begin -/
  classical
  intro d hd U hU ε hε L hL hgrad hosc hjoint δ hδ
  obtain ⟨S₀, hS₀⟩ :=
    statopia_math_node_1277695823_4133e1d3 d hd U hU ε hε L hL
      (1 / 2) (by norm_num) (by norm_num) hgrad hosc hjoint (δ / 2) (by linarith)
  haveI hprob : IsProbabilityMeasure (gaussianMomentum d) := by
    unfold gaussianMomentum
    exact Measure.isProbabilityMeasure_map
      (Measurable.aemeasurable (f := (EuclideanSpace.equiv (Fin d) ℝ).symm) (by fun_prop))
  have hnonneg : ∀ y p : HMCState d, 0 ≤ acceptProb U ε L (y, p) := by
    intro y p
    unfold acceptProb
    exact le_min zero_le_one (Real.exp_pos _).le
  have hle1 : ∀ y p : HMCState d, acceptProb U ε L (y, p) ≤ 1 := by
    intro y p
    unfold acceptProb
    exact min_le_left _ _
  have hgrad_meas : Measurable (gradient U) := by
    have hgrad_eq : gradient U = fun x => (InnerProductSpace.toDual ℝ (HMCState d)).symm (fderiv ℝ U x) := by
      funext x
      have hGA := (hU x).hasGradientAt
      have h1 : (InnerProductSpace.toDual ℝ (HMCState d)) (gradient U x) = fderiv ℝ U x := by
        ext y
        rw [InnerProductSpace.toDual_apply_apply, HasGradientAt.fderiv_apply hGA]
      calc gradient U x = (InnerProductSpace.toDual ℝ (HMCState d)).symm ((InnerProductSpace.toDual ℝ (HMCState d)) (gradient U x)) :=
            ((InnerProductSpace.toDual ℝ (HMCState d)).symm_apply_apply (gradient U x)).symm
        _ = (InnerProductSpace.toDual ℝ (HMCState d)).symm (fderiv ℝ U x) := by rw [h1]
    rw [hgrad_eq]
    exact (by fun_prop : Measurable ((InnerProductSpace.toDual ℝ (HMCState d)).symm)).comp (measurable_fderiv ℝ U)
  have hUm : Measurable U := hU.continuous.measurable
  have hham_meas : Measurable (hamiltonian U) := by
    unfold hamiltonian
    fun_prop
  have hstep_meas : Measurable (leapfrogStep U ε) := by
    unfold leapfrogStep
    fun_prop
  have hflow_meas : Measurable (leapfrogFlow U ε L) := by
    unfold leapfrogFlow
    exact hstep_meas.iterate L
  have hacc_meas_full : Measurable (acceptProb U ε L) := by
    unfold acceptProb
    exact Measurable.min measurable_const
      (Real.measurable_exp.comp (hham_meas.sub (hham_meas.comp hflow_meas)))
  have hmeas : ∀ y : HMCState d, Measurable (fun p => acceptProb U ε L (y, p)) := by
    intro y
    exact hacc_meas_full.comp (by fun_prop)
  have hacc_int : ∀ y : HMCState d, Integrable (fun p => acceptProb U ε L (y, p)) (gaussianMomentum d) := by
    intro y
    refine MeasureTheory.Integrable.of_bound (hmeas y).aestronglyMeasurable 1 ?_
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg y p)]
    exact hle1 y p
  obtain ⟨hint, hval⟩ := statopia_math_node_2370441094_f2816c1d d
  have hfirst : ∃ S : ℝ, ∀ x : HMCState d, S ≤ ‖x‖ →
      ∫ p, acceptProb U ε L (x, p) ∂(gaussianMomentum d) ≤ δ := by
    refine ⟨max (max S₀ (2 * (d : ℝ) / δ)) 1, ?_⟩
    intro x hx
    have hx1 : (1 : ℝ) ≤ ‖x‖ := le_trans (le_max_right _ _) hx
    have hxpos : (0 : ℝ) < ‖x‖ := lt_of_lt_of_le one_pos hx1
    have hxS0 : S₀ ≤ ‖x‖ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
    have hx2d : 2 * (d : ℝ) / δ ≤ ‖x‖ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
    have hdδ : (d : ℝ) / ‖x‖ ≤ δ / 2 := by
      rw [div_le_iff₀ hxpos]
      have h2 : 2 * (d : ℝ) ≤ ‖x‖ * δ := by
        calc 2 * (d : ℝ) = (2 * (d : ℝ) / δ) * δ := by field_simp
          _ ≤ ‖x‖ * δ := by gcongr
      nlinarith [h2]
    set s : Set (HMCState d) := {p | ‖p‖ ≤ ‖x‖ ^ (1 / 2 : ℝ)} with hs
    have hs_meas : MeasurableSet s := by
      rw [hs]
      exact measurableSet_le continuous_norm.measurable measurable_const
    have hnorm_meas : Measurable (fun p : HMCState d => ‖p‖ ^ 2) := (continuous_norm.pow 2).measurable
    have hnorm_nonneg : 0 ≤ᵐ[(gaussianMomentum d)] (fun p : HMCState d => ‖p‖ ^ 2) := by
      filter_upwards with p; positivity
    have hmarkov := Statlib.StatFoundation.Concentration.MomentType.markov_nonneg_rv_meas_gt_le_expectation_div
      (gaussianMomentum d) (fun p : HMCState d => ‖p‖ ^ 2) ‖x‖ hnorm_meas hnorm_nonneg hint hxpos
    rw [hval] at hmarkov
    have htail : (gaussianMomentum d).real sᶜ ≤ (d : ℝ) / ‖x‖ := by
      have hle : (gaussianMomentum d) sᶜ ≤ ENNReal.ofReal ((d : ℝ) / ‖x‖) := by
        have hsub : sᶜ ⊆ {p : HMCState d | ‖x‖ < ‖p‖ ^ 2} := by
          intro p hp
          simp only [Set.mem_compl_iff, hs, Set.mem_setOf_eq] at hp ⊢
          have hxp : ‖x‖ ^ (1 / 2 : ℝ) < ‖p‖ := lt_of_not_ge hp
          have hr2 : (‖x‖ ^ (1 / 2 : ℝ)) ^ 2 = ‖x‖ := by
            rw [(Real.sqrt_eq_rpow ‖x‖).symm, Real.sq_sqrt (le_of_lt hxpos)]
          have hsq : (‖x‖ ^ (1 / 2 : ℝ)) ^ 2 < ‖p‖ ^ 2 := by
            nlinarith [hxp, Real.rpow_pos_of_pos hxpos (1 / 2 : ℝ), norm_nonneg p]
          linarith [hr2, hsq]
        calc (gaussianMomentum d) sᶜ ≤ (gaussianMomentum d) {p : HMCState d | ‖x‖ < ‖p‖ ^ 2} :=
              MeasureTheory.measure_mono hsub
          _ ≤ ENNReal.ofReal (d : ℝ) / ENNReal.ofReal ‖x‖ := hmarkov
          _ = ENNReal.ofReal ((d : ℝ) / ‖x‖) := (ENNReal.ofReal_div_of_pos hxpos).symm
      calc (gaussianMomentum d).real sᶜ = ((gaussianMomentum d) sᶜ).toReal := rfl
        _ ≤ (ENNReal.ofReal ((d : ℝ) / ‖x‖)).toReal := ENNReal.toReal_mono (by simp) hle
        _ = (d : ℝ) / ‖x‖ := ENNReal.toReal_ofReal (by positivity)
    have hmu_s : (gaussianMomentum d).real s ≤ 1 := MeasureTheory.measureReal_le_one (μ := gaussianMomentum d)
    have hgood : ∫ p in s, acceptProb U ε L (x, p) ∂(gaussianMomentum d) ≤ (δ / 2) * (gaussianMomentum d).real s := by
      have hle : (fun p => acceptProb U ε L (x, p)) ≤ᵐ[(gaussianMomentum d).restrict s] (fun _ => δ / 2) := by
        filter_upwards [MeasureTheory.ae_restrict_mem hs_meas] with p hp
        exact hS₀ x p hxS0 hp
      have hfi : Integrable (fun p => acceptProb U ε L (x, p)) ((gaussianMomentum d).restrict s) :=
        (hacc_int x).mono_measure MeasureTheory.Measure.restrict_le_self
      have hgi : Integrable (fun _ : HMCState d => δ / 2) ((gaussianMomentum d).restrict s) :=
        MeasureTheory.integrable_const _
      have hstep := MeasureTheory.integral_mono_ae hfi hgi hle
      calc ∫ p in s, acceptProb U ε L (x, p) ∂(gaussianMomentum d)
          = ∫ p, acceptProb U ε L (x, p) ∂((gaussianMomentum d).restrict s) := rfl
        _ ≤ ∫ p, (δ / 2) ∂((gaussianMomentum d).restrict s) := hstep
        _ = (δ / 2) * (gaussianMomentum d).real s := by
            rw [MeasureTheory.integral_const, MeasureTheory.measureReal_restrict_apply_univ, smul_eq_mul, mul_comm]
    have hcompl : ∫ p in sᶜ, acceptProb U ε L (x, p) ∂(gaussianMomentum d) ≤ (gaussianMomentum d).real sᶜ := by
      have hbdd : ∀ᵐ p ∂(gaussianMomentum d), ‖acceptProb U ε L (x, p)‖ ≤ 1 := by
        filter_upwards with p
        rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg x p)]
        exact hle1 x p
      have h := MeasureTheory.norm_integral_sub_setIntegral_le (f := fun p => acceptProb U ε L (x, p))
        (C := 1) hbdd hs_meas (hacc_int x)
      rw [← MeasureTheory.setIntegral_compl (s := s) hs_meas (hacc_int x), mul_one] at h
      have hnn : 0 ≤ ∫ p in sᶜ, acceptProb U ε L (x, p) ∂(gaussianMomentum d) :=
        MeasureTheory.setIntegral_nonneg hs_meas.compl (fun p _ => hnonneg x p)
      rwa [Real.norm_of_nonneg hnn] at h
    have hsplit : ∫ p, acceptProb U ε L (x, p) ∂(gaussianMomentum d)
        = ∫ p in s, acceptProb U ε L (x, p) ∂(gaussianMomentum d)
          + ∫ p in sᶜ, acceptProb U ε L (x, p) ∂(gaussianMomentum d) := by
      have h := MeasureTheory.setIntegral_compl (s := s) hs_meas (hacc_int x)
      linarith [h]
    calc ∫ p, acceptProb U ε L (x, p) ∂(gaussianMomentum d)
        = ∫ p in s, acceptProb U ε L (x, p) ∂(gaussianMomentum d)
          + ∫ p in sᶜ, acceptProb U ε L (x, p) ∂(gaussianMomentum d) := hsplit
      _ ≤ (δ / 2) * (gaussianMomentum d).real s + (gaussianMomentum d).real sᶜ := add_le_add hgood hcompl
      _ ≤ δ / 2 + (d : ℝ) / ‖x‖ := by
          have h1 : (δ / 2) * (gaussianMomentum d).real s ≤ δ / 2 := by
            calc (δ / 2) * (gaussianMomentum d).real s ≤ (δ / 2) * 1 :=
                  mul_le_mul_of_nonneg_left hmu_s (by positivity)
              _ = δ / 2 := mul_one _
          exact add_le_add h1 htail
      _ ≤ δ / 2 + δ / 2 := by linarith [hdδ]
      _ = δ := by ring
  obtain ⟨S₁, hS₁⟩ := hfirst
  refine ⟨S₁, fun x hx => ⟨hS₁ x hx, ?_⟩⟩
  have hconv : (1 : ℝ) - ∫ p, (1 - acceptProb U ε L (x, p)) ∂(gaussianMomentum d)
      = ∫ p, acceptProb U ε L (x, p) ∂(gaussianMomentum d) := by
    have hconst : Integrable (fun _ : HMCState d => (1:ℝ)) (gaussianMomentum d) :=
      MeasureTheory.integrable_const (1:ℝ)
    have hsub : ∫ p, (1 - acceptProb U ε L (x, p)) ∂(gaussianMomentum d)
        = ∫ p, (1:ℝ) ∂(gaussianMomentum d) - ∫ p, acceptProb U ε L (x, p) ∂(gaussianMomentum d) :=
      MeasureTheory.integral_sub hconst (hacc_int x)
    have hreal : (gaussianMomentum d).real Set.univ = 1 := by
      rw [show (gaussianMomentum d).real Set.univ = ((gaussianMomentum d) Set.univ).toReal from rfl,
        MeasureTheory.measure_univ]
      simp
    have hone : ∫ p, (1:ℝ) ∂(gaussianMomentum d) = 1 := by
      rw [MeasureTheory.integral_const, hreal]
      simp
    rw [hsub, hone]
    ring
  rw [hconv]
  exact hS₁ x hx
  /- @proof-region region.target-node.session.75c5bbcbdf8e47f7 end -/

end Statlib.Imported

end

