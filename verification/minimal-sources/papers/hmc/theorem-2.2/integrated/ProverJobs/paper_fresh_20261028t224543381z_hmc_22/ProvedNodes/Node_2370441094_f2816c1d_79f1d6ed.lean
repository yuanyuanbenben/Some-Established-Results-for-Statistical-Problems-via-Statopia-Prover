import Statlib.StatFoundation.RandomVariable.Gaussian.Standard
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
theorem statopia_math_node_2370441094_f2816c1d : ∀ (d : ℕ),
    Integrable (fun p : HMCState d => ‖p‖ ^ 2) (gaussianMomentum d) ∧
      ∫ (p : HMCState d), ‖p‖ ^ 2 ∂(gaussianMomentum d) = (d : ℝ) := by
  /- @proof-region region.target-node.session.f7104d80349522c4 begin -/
  intro d
  set m : Measure (Fin d → ℝ) := Measure.pi (fun _ : Fin d => gaussianReal (0 : ℝ) 1) with hm
  have hG : gaussianMomentum d = m.map (EuclideanSpace.equiv (Fin d) ℝ).symm := by
    rw [gaussianMomentum, ← hm]
  have hcoord : ∀ i : Fin d, Integrable (fun y : Fin d → ℝ => (y i) ^ 2) m ∧
      ∫ y : Fin d → ℝ, (y i) ^ 2 ∂m = 1 := by
    intro i
    have hmp : MeasurePreserving (Function.eval i) m (gaussianReal (0 : ℝ) 1) := by
      rw [hm]
      exact MeasureTheory.measurePreserving_eval (fun _ : Fin d => gaussianReal (0 : ℝ) 1) i
    have hmem : MemLp (fun t : ℝ => t ^ 2) (1 : ℝ≥0∞) (gaussianReal (0 : ℝ) 1) :=
      Statlib.StatFoundation.RandomVariable.Gaussian.memLp_pow_id_gaussianReal 2 1 (by simp)
    have hint1 : Integrable (fun t : ℝ => t ^ 2) (gaussianReal (0 : ℝ) 1) :=
      MeasureTheory.MemLp.integrable le_rfl hmem
    have hmean : ∫ x : ℝ, id x ∂(gaussianReal (0 : ℝ) 1) = 0 := by
      have h := ProbabilityTheory.integral_linearMap_gaussianReal (μ := (0 : ℝ)) (v := 1)
        (LinearMap.id : ℝ →ₗ[ℝ] ℝ)
      simpa using h
    have h1 : ∫ t : ℝ, t ^ 2 ∂(gaussianReal (0 : ℝ) 1) = 1 := by
      have hvi := ProbabilityTheory.variance_eq_integral (μ := gaussianReal (0 : ℝ) 1)
        (X := id) measurable_id.aemeasurable
      rw [ProbabilityTheory.variance_id_gaussianReal] at hvi
      simpa [hmean] using hvi.symm
    have hint : Integrable (fun y : Fin d → ℝ => (y i) ^ 2) m := by
      have hmapint : Integrable (fun t : ℝ => t ^ 2) (Measure.map (Function.eval i) m) := by
        rw [hmp.map_eq]
        exact hint1
      have hback := (MeasureTheory.integrable_map_measure (f := Function.eval i)
        (g := fun t : ℝ => t ^ 2) (μ := m)
        ((continuous_id.pow 2).aestronglyMeasurable) hmp.measurable.aemeasurable).mp hmapint
      simpa using hback
    refine ⟨hint, ?_⟩
    have hmi := MeasureTheory.integral_map (μ := m) (φ := Function.eval i)
      (f := fun t : ℝ => t ^ 2) hmp.measurable.aemeasurable
      ((continuous_id.pow 2).aestronglyMeasurable)
    rw [hmp.map_eq, h1] at hmi
    simpa using hmi.symm
  have hnorm : ∀ y : Fin d → ℝ,
      ‖(EuclideanSpace.equiv (Fin d) ℝ).symm y‖ ^ 2 = ∑ i, (y i) ^ 2 := by
    intro y
    rw [EuclideanSpace.norm_sq_eq]
    have hy : ((EuclideanSpace.equiv (Fin d) ℝ).symm y).ofLp = y := rfl
    rw [hy]
    simp

  constructor
  · rw [hG]
    refine (MeasureTheory.integrable_map_measure
      (f := (EuclideanSpace.equiv (Fin d) ℝ).symm)
      (g := fun p : EuclideanSpace ℝ (Fin d) => ‖p‖ ^ 2) (μ := m)
      (continuous_norm.pow 2).aestronglyMeasurable
      ((EuclideanSpace.equiv (Fin d) ℝ).symm.continuous.measurable.aemeasurable)).mpr ?_
    have hcongr : (fun p : EuclideanSpace ℝ (Fin d) => ‖p‖ ^ 2) ∘
          (EuclideanSpace.equiv (Fin d) ℝ).symm
        = fun y : Fin d → ℝ => ∑ i, (y i) ^ 2 := by
      funext y
      exact hnorm y
    rw [hcongr]
    have key : ∀ s : Finset (Fin d), Integrable (fun y : Fin d → ℝ => ∑ i ∈ s, (y i) ^ 2) m := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
          have hfun : (fun y : Fin d → ℝ => ∑ i ∈ insert a s, (y i) ^ 2)
              = fun y : Fin d → ℝ => (y a) ^ 2 + ∑ i ∈ s, (y i) ^ 2 := by
            funext y
            rw [Finset.sum_insert ha]
          rw [hfun]
          exact (hcoord a).1.add ih
    simpa using key Finset.univ
  · rw [hG]
    rw [MeasureTheory.integral_map (φ := (EuclideanSpace.equiv (Fin d) ℝ).symm)
      (f := fun p : EuclideanSpace ℝ (Fin d) => ‖p‖ ^ 2)
      ((EuclideanSpace.equiv (Fin d) ℝ).symm.continuous.measurable.aemeasurable)
      (continuous_norm.pow 2).aestronglyMeasurable]
    simp only [hnorm]
    rw [MeasureTheory.integral_finset_sum (Finset.univ)
      (f := fun i (y : Fin d → ℝ) => (y i) ^ 2) (fun i _ => (hcoord i).1)]
    have hone : ∀ i ∈ (Finset.univ : Finset (Fin d)), ∫ y : Fin d → ℝ, (y i) ^ 2 ∂m = 1 := by
      intro i _
      exact (hcoord i).2
    simp [hone]
  /- @proof-region region.target-node.session.f7104d80349522c4 end -/

end Statlib.Imported

end

