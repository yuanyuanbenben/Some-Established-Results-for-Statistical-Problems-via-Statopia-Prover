import ProverJobs.paper_fresh_20261028t151409527z_hmc_v5.Vocabulary
import ProverJobs.paper_fresh_20261028t151409527z_hmc_v5.Base
import ProverJobs.paper_fresh_20261028t151409527z_hmc_v5.ProvedNodes.Node_359030125_cafa1cba_3f488281

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
theorem statopia_math_node_2575820610_02f1cc53 : ∀ (d : ℕ) (U : HMCState d → ℝ) (L : ℕ) (ε : ℝ)
    (hU : Differentiable ℝ U),
    (∀ x : HMCState d, Measurable (fun p : HMCState d => hmcAlpha U L ε x p)) ∧
      (∀ x : HMCState d, IsProbabilityMeasure (hmcKernel U L ε x)) := by
  /- @proof-region region.target-node.session.27c8eadcd903e6d6 begin -/
  intro d U L ε hU
  have hgrad : Measurable (gradient U) := statopia_math_node_359030125_cafa1cba d U hU
  have hstep : Measurable (leapStep U ε) := by
    have h1 : Measurable (fun xp : HMCState d × HMCState d => xp.1) := measurable_fst
    have h2 : Measurable (fun xp : HMCState d × HMCState d => xp.2) := measurable_snd
    have hg1 : Measurable (fun xp : HMCState d × HMCState d => gradient U xp.1) := hgrad.comp h1
    have hpHalf : Measurable
        (fun xp : HMCState d × HMCState d => xp.2 - (ε / 2) • gradient U xp.1) :=
      h2.sub (hg1.const_smul (ε / 2))
    have hx' : Measurable
        (fun xp : HMCState d × HMCState d => xp.1 + ε • (xp.2 - (ε / 2) • gradient U xp.1)) :=
      h1.add (hpHalf.const_smul ε)
    have hp' : Measurable (fun xp : HMCState d × HMCState d =>
        (xp.2 - (ε / 2) • gradient U xp.1) -
          (ε / 2) • gradient U (xp.1 + ε • (xp.2 - (ε / 2) • gradient U xp.1))) :=
      hpHalf.sub ((hgrad.comp hx').const_smul (ε / 2))
    exact Measurable.prodMk hx' hp'
  have hflow : Measurable (leapFlow U ε L) := hstep.iterate L
  constructor
  · intro x
    have hpair : Measurable (fun p : HMCState d => (x, p)) :=
      Measurable.prodMk (measurable_const : Measurable fun _ : HMCState d => x) measurable_id
    have hq : Measurable (fun p : HMCState d => leapFlow U ε L (x, p)) := hflow.comp hpair
    have hq1 : Measurable (fun p : HMCState d => (leapFlow U ε L (x, p)).1) :=
      measurable_fst.comp hq
    have hq2 : Measurable (fun p : HMCState d => (leapFlow U ε L (x, p)).2) :=
      measurable_snd.comp hq
    have hUq : Measurable (fun p : HMCState d => U (leapFlow U ε L (x, p)).1) :=
      hU.continuous.measurable.comp hq1
    have hA : Measurable (fun p : HMCState d =>
        U x - U (leapFlow U ε L (x, p)).1 + (1 / 2) * ‖p‖ ^ 2 -
          (1 / 2) * ‖(leapFlow U ε L (x, p)).2‖ ^ 2) := by
      have hnorm : Measurable (fun p : HMCState d => ‖p‖) := continuous_norm.measurable
      have hnorm2 : Measurable (fun p : HMCState d => ‖(leapFlow U ε L (x, p)).2‖) :=
        continuous_norm.measurable.comp hq2
      have hsq : Continuous fun t : ℝ => (1 / 2) * t ^ 2 := by fun_prop
      have hC : Measurable (fun p : HMCState d => (1 / 2) * ‖p‖ ^ 2) :=
        hsq.measurable.comp hnorm
      have hD : Measurable (fun p : HMCState d => (1 / 2) * ‖(leapFlow U ε L (x, p)).2‖ ^ 2) :=
        hsq.measurable.comp hnorm2
      exact ((measurable_const.sub hUq).add hC).sub hD
    unfold hmcAlpha
    exact measurable_const.min (Real.continuous_exp.measurable.comp hA)
  · intro x
    refine ⟨?_⟩
    have hk : Measurable (fun p : HMCState d =>
        let q := leapFlow U ε L (x, p)
        let a := min 1 (Real.exp (U x - U q.1 + (1 / 2) * ‖p‖ ^ 2 - (1 / 2) * ‖q.2‖ ^ 2))
        ENNReal.ofReal a • Measure.dirac q.1 + ENNReal.ofReal (1 - a) • Measure.dirac x) := by
      refine Measure.measurable_of_measurable_coe _ ?_
      intro s hs
      classical
      have hq : Measurable (fun p : HMCState d => leapFlow U ε L (x, p)) :=
        hflow.comp
          (Measurable.prodMk (measurable_const : Measurable fun _ : HMCState d => x) measurable_id)
      have hq1 : Measurable (fun p : HMCState d => (leapFlow U ε L (x, p)).1) :=
        measurable_fst.comp hq
      have hq2 : Measurable (fun p : HMCState d => (leapFlow U ε L (x, p)).2) :=
        measurable_snd.comp hq
      have hb : Measurable (fun p : HMCState d =>
          min 1 (Real.exp (U x - U (leapFlow U ε L (x, p)).1 + (1 / 2) * ‖p‖ ^ 2 -
            (1 / 2) * ‖(leapFlow U ε L (x, p)).2‖ ^ 2))) := by
        have hUq : Measurable (fun p : HMCState d => U (leapFlow U ε L (x, p)).1) :=
          hU.continuous.measurable.comp hq1
        have hsq : Continuous fun t : ℝ => (1 / 2) * t ^ 2 := by fun_prop
        have hC : Measurable (fun p : HMCState d => (1 / 2) * ‖p‖ ^ 2) :=
          hsq.measurable.comp continuous_norm.measurable
        have hD : Measurable (fun p : HMCState d => (1 / 2) * ‖(leapFlow U ε L (x, p)).2‖ ^ 2) :=
          hsq.measurable.comp (continuous_norm.measurable.comp hq2)
        exact measurable_const.min
          (Real.continuous_exp.measurable.comp (((measurable_const.sub hUq).add hC).sub hD))
      have hof : Measurable (ENNReal.ofReal : ℝ → ENNReal) := by fun_prop
      have hO1 : Measurable (fun p : HMCState d => ENNReal.ofReal (min 1 (Real.exp (U x -
          U (leapFlow U ε L (x, p)).1 + (1 / 2) * ‖p‖ ^ 2 -
            (1 / 2) * ‖(leapFlow U ε L (x, p)).2‖ ^ 2)))) := hof.comp hb
      have hone : Measurable (fun p : HMCState d => (1 : ℝ) - min 1 (Real.exp (U x -
          U (leapFlow U ε L (x, p)).1 + (1 / 2) * ‖p‖ ^ 2 -
            (1 / 2) * ‖(leapFlow U ε L (x, p)).2‖ ^ 2))) := measurable_const.sub hb
      have hO2 : Measurable (fun p : HMCState d => ENNReal.ofReal ((1 : ℝ) - min 1 (Real.exp (U x -
          U (leapFlow U ε L (x, p)).1 + (1 / 2) * ‖p‖ ^ 2 -
            (1 / 2) * ‖(leapFlow U ε L (x, p)).2‖ ^ 2)))) := hof.comp hone
      have hmem : MeasurableSet {p : HMCState d | (leapFlow U ε L (x, p)).1 ∈ s} := hs.preimage hq1
      have hit : Measurable (fun p : HMCState d =>
          if (leapFlow U ε L (x, p)).1 ∈ s then (1 : ENNReal) else 0) :=
        Measurable.ite hmem measurable_const measurable_const
      have hxt : Measurable (fun p : HMCState d => if x ∈ s then (1 : ENNReal) else 0) :=
        measurable_const
      have hval : ∀ p : HMCState d,
          (let q := leapFlow U ε L (x, p)
           let a := min 1 (Real.exp (U x - U q.1 + (1 / 2) * ‖p‖ ^ 2 - (1 / 2) * ‖q.2‖ ^ 2))
           ENNReal.ofReal a • Measure.dirac q.1 + ENNReal.ofReal (1 - a) • Measure.dirac x) s
            = ENNReal.ofReal (min 1 (Real.exp (U x - U (leapFlow U ε L (x, p)).1 +
                (1 / 2) * ‖p‖ ^ 2 - (1 / 2) * ‖(leapFlow U ε L (x, p)).2‖ ^ 2))) *
                s.indicator 1 (leapFlow U ε L (x, p)).1
              + ENNReal.ofReal ((1 : ℝ) - min 1 (Real.exp (U x - U (leapFlow U ε L (x, p)).1 +
                (1 / 2) * ‖p‖ ^ 2 - (1 / 2) * ‖(leapFlow U ε L (x, p)).2‖ ^ 2))) *
                s.indicator 1 x := by
        intro p
        have hd1 : (Measure.dirac (leapFlow U ε L (x, p)).1) s =
            s.indicator 1 (leapFlow U ε L (x, p)).1 := Measure.dirac_apply' _ hs
        have hd2 : (Measure.dirac x) s = s.indicator 1 x := Measure.dirac_apply' _ hs
        simp [Measure.add_apply, Measure.smul_apply, hd1, hd2]
      have hfun : (fun p : HMCState d => (let q := leapFlow U ε L (x, p)
            let a := min 1 (Real.exp (U x - U q.1 + (1 / 2) * ‖p‖ ^ 2 - (1 / 2) * ‖q.2‖ ^ 2))
            ENNReal.ofReal a • Measure.dirac q.1 + ENNReal.ofReal (1 - a) • Measure.dirac x) s)
          = fun p : HMCState d => ENNReal.ofReal (min 1 (Real.exp (U x - U (leapFlow U ε L (x, p)).1 +
              (1 / 2) * ‖p‖ ^ 2 - (1 / 2) * ‖(leapFlow U ε L (x, p)).2‖ ^ 2))) *
              s.indicator 1 (leapFlow U ε L (x, p)).1
            + ENNReal.ofReal ((1 : ℝ) - min 1 (Real.exp (U x - U (leapFlow U ε L (x, p)).1 +
              (1 / 2) * ‖p‖ ^ 2 - (1 / 2) * ‖(leapFlow U ε L (x, p)).2‖ ^ 2))) *
              s.indicator 1 x :=
        funext hval
      rw [hfun]
      exact (hO1.mul hit).add (hO2.mul hxt)
    have hmass : ∀ p : HMCState d,
        (let q := leapFlow U ε L (x, p)
         let a := min 1 (Real.exp (U x - U q.1 + (1 / 2) * ‖p‖ ^ 2 - (1 / 2) * ‖q.2‖ ^ 2))
         ENNReal.ofReal a • Measure.dirac q.1 + ENNReal.ofReal (1 - a) • Measure.dirac x) Set.univ
          = 1 := by
      intro p
      dsimp only
      set a := min 1 (Real.exp (U x - U (leapFlow U ε L (x, p)).1 + (1 / 2) * ‖p‖ ^ 2 -
        (1 / 2) * ‖(leapFlow U ε L (x, p)).2‖ ^ 2)) with ha
      have hexp : 0 < Real.exp (U x - U (leapFlow U ε L (x, p)).1 + (1 / 2) * ‖p‖ ^ 2 -
          (1 / 2) * ‖(leapFlow U ε L (x, p)).2‖ ^ 2) := Real.exp_pos _
      have h0 : 0 ≤ a := by rw [ha]; exact le_min zero_le_one hexp.le
      have h1 : a ≤ 1 := by rw [ha]; exact min_le_left _ _
      have hb : 0 ≤ 1 - a := by linarith
      have hd1 : (Measure.dirac (leapFlow U ε L (x, p)).1) Set.univ = 1 :=
        Measure.dirac_apply_of_mem (Set.mem_univ _)
      have hd2 : (Measure.dirac x) Set.univ = 1 := Measure.dirac_apply_of_mem (Set.mem_univ _)
      simp only [Measure.add_apply, Measure.smul_apply, hd1, hd2, smul_eq_mul, mul_one]
      rw [← ENNReal.ofReal_add h0 hb]
      rw [show a + (1 - a) = 1 by ring, ENNReal.ofReal_one]
    haveI : IsProbabilityMeasure (standardGaussianMomentum d) := by
      unfold standardGaussianMomentum
      exact Measure.isProbabilityMeasure_map
        (MeasurableEquiv.measurable (EuclideanSpace.measurableEquiv (Fin d)).symm).aemeasurable
    unfold hmcKernel
    rw [Measure.bind_apply MeasurableSet.univ hk.aemeasurable]
    simp only [hmass, lintegral_const, one_mul]
    exact measure_univ
  /- @proof-region region.target-node.session.27c8eadcd903e6d6 end -/

end Statlib.Imported
end

