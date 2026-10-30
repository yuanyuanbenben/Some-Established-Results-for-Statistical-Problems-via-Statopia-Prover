import ProverJobs.paper_fresh_20261028t224543381z_eills.Vocabulary
import ProverJobs.paper_fresh_20261028t224543381z_eills.Base

namespace PaperProofTasks.paper_fresh_20261028t224543381z_eills

open _root_.PaperProofTasks.paper_fresh_20261028t224543381z_eills.Statlib.Imported
open _root_.PaperProofTasks.paper_fresh_20261028t224543381z_eills.Statlib.Imported.StrongConvexityMain
open MeasureTheory ProbabilityTheory
open StrongConvexityMain

namespace Statlib.Imported

open MeasureTheory ProbabilityTheory
open _root_.PaperProofTasks.paper_fresh_20261028t224543381z_eills.Statlib.Imported.StrongConvexityMain

set_option autoImplicit false in
theorem statopia_math_node_3875025507_3baf775f : ∀ (p : ℕ) {ι : Type*} [Fintype ι] [Nonempty ι]
    (μ : ι → Measure (Eucl p × ℝ))
    (βstar : Eucl p) (S_star : Finset (Fin p))
    (hS_star : ∀ j : Fin p, j ∈ S_star ↔ βstar j ≠ 0)
    (hProb : ∀ e : ι, IsProbabilityMeasure (μ e))
    (hIntY : ∀ e : ι, Integrable (fun z : Eucl p × ℝ => z.2) (μ e))
    (hcond : ∀ e : ι,
      (fun z : Eucl p × ℝ =>
          condExp (sigmaSub S_star) (μ e) (fun z : Eucl p × ℝ => z.2) z)
        =ᵐ[μ e] (fun z : Eucl p × ℝ => dot βstar z.1))
    (hIntX : ∀ (e : ι) (j : Fin p),
      Integrable (fun z : Eucl p × ℝ => residAt βstar z * z.1 j) (μ e)),
    (∀ (e : ι) (j : Fin p), j ∈ S_star →
        ∫ z, residAt βstar z * z.1 j ∂(μ e) = 0) ∧
    (∀ j : Fin p, j ∈ S_star →
        (Fintype.card ι : ℝ)⁻¹ * ∑ e, ∫ z, residAt βstar z * z.1 j ∂(μ e) = 0) ∧
    (∀ S : Finset (Fin p),
        bCoeff μ βstar S =
          ∑ j ∈ S ∪ S_star,
            ((Fintype.card ι : ℝ)⁻¹ * ∑ e, ∫ z, residAt βstar z * z.1 j ∂(μ e)) ^ 2) := by
  /- @proof-region region.target-node.session.2ae4ec71b366b61d begin -/
  intro p ι _ _ μ βstar S_star hS_star hProb hIntY hcond hIntCross
  classical
  have hmain : ∀ (e : ι) (j : Fin p), j ∈ S_star →
      ∫ z : Eucl p × ℝ, residAt βstar z * z.1 j ∂(μ e) = 0 := by
    intro e j hj
    haveI hprobE : IsProbabilityMeasure (μ e) := hProb e
    have hcoord_meas : ∀ i : Fin p, Measurable (fun z : Eucl p × ℝ => z.1 i) := by
      intro i
      fun_prop
    have hΦ : Measurable (fun z : Eucl p × ℝ => fun k : ↥S_star => z.1 (k : Fin p)) := by
      refine measurable_pi_iff.mpr (fun k => ?_)
      exact hcoord_meas k
    have hle : sigmaSub S_star ≤ (inferInstance : MeasurableSpace (Eucl p × ℝ)) := by
      simp only [sigmaSub]
      exact measurable_iff_comap_le.mp hΦ
    haveI hsf : SigmaFinite ((μ e).trim hle) := inferInstance
    have hdot_int : Integrable (fun z : Eucl p × ℝ => dot βstar z.1) (μ e) := by
      refine (integrable_condExp (m := sigmaSub S_star) (μ := μ e)
        (f := fun z : Eucl p × ℝ => z.2)).congr ?_
      exact hcond e
    have hres_int : Integrable (fun z : Eucl p × ℝ => residAt βstar z) (μ e) := by
      have h := (hIntY e).sub hdot_int
      simpa [residAt] using h
    have hΦm : Measurable[sigmaSub S_star]
        (fun z : Eucl p × ℝ => fun k : ↥S_star => z.1 (k : Fin p)) :=
      measurable_iff_comap_le.mpr le_rfl
    have hSM : ∀ i : Fin p, i ∈ S_star → Measurable[sigmaSub S_star] (fun z : Eucl p × ℝ => z.1 i) := by
      intro i hi
      have hproj : Measurable (fun v : ↥S_star → ℝ => v ⟨i, hi⟩) := by
        have hc : Continuous (fun v : ↥S_star → ℝ => v ⟨i, hi⟩) :=
          continuous_apply (⟨i, hi⟩ : ↥S_star)
        exact hc.measurable
      exact hproj.comp hΦm
    have hsm_coord : StronglyMeasurable[sigmaSub S_star] (fun z : Eucl p × ℝ => z.1 j) :=
      (hSM j hj).stronglyMeasurable
    have hsm_dot : StronglyMeasurable[sigmaSub S_star] (fun z : Eucl p × ℝ => dot βstar z.1) := by
      have hdot_eq : (fun z : Eucl p × ℝ => dot βstar z.1)
          = fun z => ∑ i ∈ S_star, βstar i * z.1 i := by
        funext z
        simp only [dot]
        exact (Finset.sum_subset (Finset.subset_univ S_star) (fun i _ hi => by
          have h0 : βstar i = 0 := by
            by_contra hc
            exact hi ((hS_star i).mpr hc)
          simp [h0])).symm
      rw [hdot_eq]
      exact (Finset.measurable_sum S_star (f := fun i (z : Eucl p × ℝ) => βstar i * z.1 i)
        (fun i hi => (measurable_const (a := βstar i)).mul (hSM i hi))).stronglyMeasurable
    have hce_dot : condExp (sigmaSub S_star) (μ e) (fun z : Eucl p × ℝ => dot βstar z.1)
        = fun z => dot βstar z.1 :=
      condExp_of_stronglyMeasurable hle hsm_dot hdot_int
    have hce_res : condExp (sigmaSub S_star) (μ e) (fun z : Eucl p × ℝ => residAt βstar z) =ᵐ[μ e] 0 := by
      have hsub : condExp (sigmaSub S_star) (μ e)
          ((fun z : Eucl p × ℝ => z.2) - fun z => dot βstar z.1) =ᵐ[μ e] 0 := by
        have hlin := condExp_sub (m := sigmaSub S_star) (μ := μ e) (hIntY e) hdot_int
        have h3 : ∀ᵐ z ∂(μ e),
            condExp (sigmaSub S_star) (μ e) (fun z : Eucl p × ℝ => dot βstar z.1) z = dot βstar z.1 :=
          Filter.Eventually.of_forall (fun z => congrFun hce_dot z)
        filter_upwards [hlin, hcond e, h3] with z hz hz2 hz3
        simp only [Pi.sub_apply, hz, hz2, hz3, sub_self, Pi.zero_apply]
      exact hsub
    have hmul : condExp (sigmaSub S_star) (μ e)
          ((fun z : Eucl p × ℝ => z.1 j) * fun z => residAt βstar z)
        =ᵐ[μ e] (fun z : Eucl p × ℝ => z.1 j) *
          condExp (sigmaSub S_star) (μ e) (fun z => residAt βstar z) :=
      condExp_mul_of_stronglyMeasurable_left hsm_coord
        (by simpa [Pi.mul_apply, mul_comm] using hIntCross e j) hres_int
    have hmul' : condExp (sigmaSub S_star) (μ e) (fun z : Eucl p × ℝ => residAt βstar z * z.1 j)
        =ᵐ[μ e] (fun z : Eucl p × ℝ => z.1 j) *
          condExp (sigmaSub S_star) (μ e) (fun z => residAt βstar z) :=
      (condExp_congr_ae (Filter.Eventually.of_forall
        (fun z : Eucl p × ℝ => mul_comm (residAt βstar z) (z.1 j)))).trans hmul
    calc ∫ z, residAt βstar z * z.1 j ∂(μ e)
        = ∫ z, condExp (sigmaSub S_star) (μ e) (fun z => residAt βstar z * z.1 j) z ∂(μ e) :=
          (integral_condExp (m := sigmaSub S_star) (μ := μ e)
            (f := fun z : Eucl p × ℝ => residAt βstar z * z.1 j) hle).symm
      _ = ∫ z, z.1 j * condExp (sigmaSub S_star) (μ e) (fun z => residAt βstar z) z ∂(μ e) := by
          refine integral_congr_ae ?_
          filter_upwards [hmul'] with z hz
          simpa using hz
      _ = 0 := by
          have hz : (fun z : Eucl p × ℝ => z.1 j *
              condExp (sigmaSub S_star) (μ e) (fun z => residAt βstar z) z) =ᵐ[μ e] 0 := by
            filter_upwards [hce_res] with z hz
            simp [hz]
          rw [integral_congr_ae hz]
          simp
  refine ⟨hmain, ?_, ?_⟩
  · intro j hj
    have hsum : ∑ e, ∫ z : Eucl p × ℝ, residAt βstar z * z.1 j ∂(μ e) = 0 :=
      Finset.sum_eq_zero (fun e _ => hmain e j hj)
    rw [hsum, mul_zero]
  · intro S
    have hzero : ∀ j ∈ S ∪ S_star, j ∉ S →
        ((Fintype.card ι : ℝ)⁻¹ * ∑ e, ∫ z : Eucl p × ℝ, residAt βstar z * z.1 j ∂(μ e)) ^ 2 = 0 := by
      intro j hjU hjS
      have hj' : j ∈ S_star := (Finset.mem_union.mp hjU).resolve_left hjS
      have hsum : (Fintype.card ι : ℝ)⁻¹ * ∑ e, ∫ z : Eucl p × ℝ, residAt βstar z * z.1 j ∂(μ e) = 0 := by
        have h0 : ∑ e, ∫ z : Eucl p × ℝ, residAt βstar z * z.1 j ∂(μ e) = 0 :=
          Finset.sum_eq_zero (fun e _ => hmain e j hj')
        rw [h0, mul_zero]
      rw [hsum]
      ring
    unfold bCoeff
    exact Finset.sum_subset Finset.subset_union_left hzero
  /- @proof-region region.target-node.session.2ae4ec71b366b61d end -/

end Statlib.Imported

