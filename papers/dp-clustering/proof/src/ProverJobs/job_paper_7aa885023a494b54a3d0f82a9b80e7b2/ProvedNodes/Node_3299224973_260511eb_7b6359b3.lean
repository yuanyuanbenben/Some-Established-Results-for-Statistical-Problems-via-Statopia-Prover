import ProverJobs.job_paper_7aa885023a494b54a3d0f82a9b80e7b2.Vocabulary
import ProverJobs.job_paper_7aa885023a494b54a3d0f82a9b80e7b2.Base
import ProverJobs.job_paper_7aa885023a494b54a3d0f82a9b80e7b2.ProvedNodes.Node_213959928_9402e920_a09b596a
open MeasureTheory
open scoped ENNReal BigOperators
open Statlib.Imported

open MeasureTheory
open scoped ENNReal BigOperators
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_3299224973_260511eb : ∀ (c thetaStar : ℝ) (hc : 0 < c)
    (P : Measure ℝ) [IsProbabilityMeasure P]
    (g q0 : ℝ → ℝ)
    (hg_meas : Measurable g) (hq0_meas : Measurable q0)
    (hg_nonneg : ∀ x : ℝ, 0 ≤ g x)
    (hq0_nonneg : ∀ θ : ℝ, 0 ≤ q0 θ)
    (hg_pos : ∀ x ∈ Set.Icc (-c) c, 0 < g x)
    (A : Type*) [Fintype A] (hA : 1 ≤ Fintype.card A),
    ∫⁻ y in {y : A → ℝ | ∀ i : A, y i ∈ Set.Icc (thetaStar - c) (thetaStar + c)},
        (∫⁻ θ, (∏ i : A, ENNReal.ofReal (g (y i - θ) / g (y i - thetaStar)))
            * ENNReal.ofReal (q0 θ) ∂(volume : Measure ℝ))
      ∂(Measure.pi (fun _ : A => P))
      = ∫⁻ θ, ((∫⁻ x in Set.Icc (thetaStar - c) (thetaStar + c),
            ENNReal.ofReal (g (x - θ) / g (x - thetaStar)) ∂P) ^ (Fintype.card A))
          * ENNReal.ofReal (q0 θ) ∂volume := by
  /- @proof-region region.target-node.session.e7f6a8a337418713 begin -/
  intro c thetaStar hc P hP g q0 hg_meas hq0_meas hg_nonneg hq0_nonneg hg_pos A hAinst hA
  set W : Set ℝ := Set.Icc (thetaStar - c) (thetaStar + c) with hW
  set S : Set (A → ℝ) := {y | ∀ i, y i ∈ W} with hS
  have hpi : Measure.pi (fun _ : A => P.restrict W) = (Measure.pi (fun _ : A => P)).restrict S := by
    refine Measure.pi_eq (fun s hs => ?_)
    have hbox : Set.univ.pi s ∩ S = Set.univ.pi (fun i => s i ∩ W) := by
      ext y
      simp [hS, Set.mem_univ_pi, Set.mem_inter_iff, forall_and]
    rw [Measure.restrict_apply (MeasurableSet.univ_pi hs), hbox, Measure.pi_pi]
    exact Finset.prod_congr rfl (fun i _ => by rw [Measure.restrict_apply (hs i)])
  have hfac : ∀ θ : ℝ, ∫⁻ (y : A → ℝ),
        (∏ i, ENNReal.ofReal (g (y i - θ) / g (y i - thetaStar)))
        ∂(Measure.pi (fun _ : A => P.restrict W))
      = (∫⁻ x in W, ENNReal.ofReal (g (x - θ) / g (x - thetaStar)) ∂P) ^ (Fintype.card A) := by
    intro θ
    exact statopia_math_node_213959928_9402e920 A (P.restrict W)
      (fun x : ℝ => ENNReal.ofReal (g (x - θ) / g (x - thetaStar))) (by measurability)
  have hTon : ∫⁻ y in S,
        (∫⁻ θ, (∏ i, ENNReal.ofReal (g (y i - θ) / g (y i - thetaStar)))
            * ENNReal.ofReal (q0 θ) ∂(volume : Measure ℝ))
        ∂(Measure.pi (fun _ : A => P))
      = ∫⁻ θ, (∫⁻ (y : A → ℝ),
            (∏ i, ENNReal.ofReal (g (y i - θ) / g (y i - thetaStar)))
            ∂(Measure.pi (fun _ : A => P.restrict W))) * ENNReal.ofReal (q0 θ)
          ∂(volume : Measure ℝ) := by
    have hf : Measurable (fun z : (A → ℝ) × ℝ =>
        (∏ i, ENNReal.ofReal (g (z.1 i - z.2) / g (z.1 i - thetaStar)))
          * ENNReal.ofReal (q0 z.2)) := by measurability
    rw [← hpi]
    rw [← MeasureTheory.lintegral_prod (fun z : (A → ℝ) × ℝ =>
        (∏ i, ENNReal.ofReal (g (z.1 i - z.2) / g (z.1 i - thetaStar)))
          * ENNReal.ofReal (q0 z.2)) hf.aemeasurable]
    rw [MeasureTheory.lintegral_prod_symm (fun z : (A → ℝ) × ℝ =>
        (∏ i, ENNReal.ofReal (g (z.1 i - z.2) / g (z.1 i - thetaStar)))
          * ENNReal.ofReal (q0 z.2)) hf.aemeasurable]
    have hcongr : (∫⁻ (y : ℝ), ∫⁻ (x : A → ℝ),
          (∏ i, ENNReal.ofReal (g (x i - y) / g (x i - thetaStar))) * ENNReal.ofReal (q0 y)
          ∂(Measure.pi (fun _ : A => P.restrict W)) ∂(volume : Measure ℝ))
        = ∫⁻ (y : ℝ), (∫⁻ (x : A → ℝ),
          (∏ i, ENNReal.ofReal (g (x i - y) / g (x i - thetaStar)))
          ∂(Measure.pi (fun _ : A => P.restrict W))) * ENNReal.ofReal (q0 y)
          ∂(volume : Measure ℝ) := by
      refine MeasureTheory.lintegral_congr (fun y => ?_)
      exact MeasureTheory.lintegral_mul_const (ENNReal.ofReal (q0 y)) (by measurability)
    exact hcongr
  rw [hTon]
  simp only [hfac]
  /- @proof-region region.target-node.session.e7f6a8a337418713 end -/

end Statlib.Imported
