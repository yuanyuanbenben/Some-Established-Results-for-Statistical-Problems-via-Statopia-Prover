import ProverJobs.paper_fresh_20261028t224543381z_eills.Vocabulary
import ProverJobs.paper_fresh_20261028t224543381z_eills.Base

namespace PaperProofTasks.paper_fresh_20261028t224543381z_eills

open _root_.PaperProofTasks.paper_fresh_20261028t224543381z_eills.Statlib.Imported
open _root_.PaperProofTasks.paper_fresh_20261028t224543381z_eills.Statlib.Imported.StrongConvexityMain
open MeasureTheory ProbabilityTheory
open StrongConvexityMain

namespace Statlib.Imported
open _root_.Statlib
open MeasureTheory ProbabilityTheory
open _root_.PaperProofTasks.paper_fresh_20261028t224543381z_eills.Statlib.Imported.StrongConvexityMain

set_option autoImplicit false in
theorem statopia_math_node_358034260_300c6b38 : ∀ (p : ℕ) (μ : Measure (Eucl p × ℝ)) [IsProbabilityMeasure μ]
    (β : Eucl p) (j : Fin p)
    (h_resid_sq : Integrable (fun z : Eucl p × ℝ => (z.2 - dot β z.1) ^ 2) μ)
    (h_cross : Integrable (fun z : Eucl p × ℝ => (z.2 - dot β z.1) * z.1 j) μ)
    (h_coord_sq : Integrable (fun z : Eucl p × ℝ => (z.1 j) ^ 2) μ),
    partDeriv μ β j = -2 * ∫ z, (z.2 - dot β z.1) * z.1 j ∂μ := by
  /- @proof-region region.target-node.session.56d09d1db5b744b1 begin -/
  intro p μ _ β j h1 h2 h3
  have hdot : ∀ (t : ℝ) (z : Eucl p × ℝ),
      dot (β + t • EuclideanSpace.single j (1:ℝ)) z.1 = dot β z.1 + t * z.1 j := by
    intro t z
    have hcoord : ∀ i : Fin p, (β + t • EuclideanSpace.single j (1:ℝ) : Eucl p) i
        = β i + t * (if i = j then (1:ℝ) else 0) := by
      intro i
      simp [EuclideanSpace.single_apply]
    simp only [dot]
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => by rw [hcoord i])]
    simp only [add_mul, Finset.sum_add_distrib]
    have hsum : (∑ i, (t * (if i = j then (1:ℝ) else 0)) * z.1 i) = t * z.1 j := by
      rw [show (∑ i, (t * (if i = j then (1:ℝ) else 0)) * z.1 i)
          = t * (∑ i, (if i = j then z.1 i else 0)) by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        by_cases h : i = j <;> simp [h]]
      rw [Finset.sum_ite_eq']
      simp
    rw [hsum]
  have hpt : ∀ (t : ℝ) (z : Eucl p × ℝ),
      (z.2 - dot (β + t • EuclideanSpace.single j (1:ℝ)) z.1) ^ 2
        = (z.2 - dot β z.1) ^ 2 - 2 * t * ((z.2 - dot β z.1) * z.1 j)
            + t ^ 2 * (z.1 j) ^ 2 := by
    intro t z
    rw [hdot t z]
    ring
  have hint : ∀ t : ℝ,
      (∫ z, (z.2 - dot (β + t • EuclideanSpace.single j (1:ℝ)) z.1) ^ 2 ∂μ)
        = (∫ z, (z.2 - dot β z.1) ^ 2 ∂μ)
            - 2 * t * (∫ z, (z.2 - dot β z.1) * z.1 j ∂μ)
            + t ^ 2 * (∫ z, (z.1 j) ^ 2 ∂μ) := by
    intro t
    rw [show (fun z : Eucl p × ℝ => (z.2 - dot (β + t • EuclideanSpace.single j (1:ℝ)) z.1) ^ 2)
        = (fun z : Eucl p × ℝ => (z.2 - dot β z.1) ^ 2
            - 2 * t * ((z.2 - dot β z.1) * z.1 j) + t ^ 2 * (z.1 j) ^ 2)
        from funext (hpt t)]
    have hI2 : Integrable (fun z : Eucl p × ℝ => 2 * t * ((z.2 - dot β z.1) * z.1 j)) μ :=
      h2.const_mul (2 * t)
    have hI3 : Integrable (fun z : Eucl p × ℝ => t ^ 2 * ((z.1 j) ^ 2)) μ :=
      h3.const_mul (t ^ 2)
    have hIsub : Integrable (fun z : Eucl p × ℝ =>
        (z.2 - dot β z.1) ^ 2 - 2 * t * ((z.2 - dot β z.1) * z.1 j)) μ := h1.sub hI2
    rw [integral_add hIsub hI3, integral_sub h1 hI2, integral_const_mul, integral_const_mul]
  have hderiv : HasDerivAt
      (fun t : ℝ => (∫ z, (z.2 - dot β z.1) ^ 2 ∂μ)
          - 2 * t * (∫ z, (z.2 - dot β z.1) * z.1 j ∂μ)
          + t ^ 2 * (∫ z, (z.1 j) ^ 2 ∂μ))
      (-2 * (∫ z, (z.2 - dot β z.1) * z.1 j ∂μ)) 0 := by
    have h1' : HasDerivAt (fun _ : ℝ => (∫ z, (z.2 - dot β z.1) ^ 2 ∂μ)) 0 0 :=
      hasDerivAt_const _ _
    have h2' : HasDerivAt (fun t : ℝ => 2 * t * (∫ z, (z.2 - dot β z.1) * z.1 j ∂μ))
        (2 * (∫ z, (z.2 - dot β z.1) * z.1 j ∂μ)) 0 := by
      simpa using (hasDerivAt_const_mul (2:ℝ)).mul_const (∫ z, (z.2 - dot β z.1) * z.1 j ∂μ)
    have h3' : HasDerivAt (fun t : ℝ => t ^ 2 * (∫ z, (z.1 j) ^ 2 ∂μ)) 0 0 := by
      simpa using (hasDerivAt_pow 2 (0:ℝ)).mul_const (∫ z, (z.1 j) ^ 2 ∂μ)
    have hcomb := (h1'.sub h2').add h3'
    simpa using hcomb
  have hfun : (fun t : ℝ => risk μ (β + t • EuclideanSpace.single j (1:ℝ)))
      = (fun t : ℝ => (∫ z, (z.2 - dot β z.1) ^ 2 ∂μ)
          - 2 * t * (∫ z, (z.2 - dot β z.1) * z.1 j ∂μ)
          + t ^ 2 * (∫ z, (z.1 j) ^ 2 ∂μ)) := by
    funext t
    show (∫ z, (z.2 - dot (β + t • EuclideanSpace.single j (1:ℝ)) z.1) ^ 2 ∂μ)
        = (∫ z, (z.2 - dot β z.1) ^ 2 ∂μ)
            - 2 * t * (∫ z, (z.2 - dot β z.1) * z.1 j ∂μ)
            + t ^ 2 * (∫ z, (z.1 j) ^ 2 ∂μ)
    exact hint t
  show deriv (fun t : ℝ => risk μ (β + t • EuclideanSpace.single j (1:ℝ))) 0
      = -2 * ∫ z, (z.2 - dot β z.1) * z.1 j ∂μ
  rw [hfun]
  rw [hderiv.deriv]
  /- @proof-region region.target-node.session.56d09d1db5b744b1 end -/

end Statlib.Imported

