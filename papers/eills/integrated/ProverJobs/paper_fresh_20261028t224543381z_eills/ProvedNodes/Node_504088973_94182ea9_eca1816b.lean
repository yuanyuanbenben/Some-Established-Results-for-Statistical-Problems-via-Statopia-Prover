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
theorem statopia_math_node_504088973_94182ea9 : ∀ (p : ℕ) {ι : Type*} [Fintype ι] [Nonempty ι]
    (μ : ι → Measure (Eucl p × ℝ))
    (hmu_prob : ∀ e : ι, IsProbabilityMeasure (μ e))
    (β : Eucl p) (βstar : Eucl p)
    (ω : ι → ℝ) (homega : ∀ e : ι, ω e = (Fintype.card ι : ℝ)⁻¹)
    (hint_star : ∀ e : ι,
      Integrable (fun z : Eucl p × ℝ => (z.2 - dot βstar z.1) ^ 2) (μ e))
    (hint_beta : ∀ e : ι,
      Integrable (fun z : Eucl p × ℝ => (z.2 - dot β z.1) ^ 2) (μ e))
    (hint_cross : ∀ (e : ι) (j : Fin p),
      Integrable (fun z : Eucl p × ℝ => residAt βstar z * z.1 j) (μ e))
    (hint_cov : ∀ (e : ι) (i j : Fin p),
      Integrable (fun z : Eucl p × ℝ => z.1 i * z.1 j) (μ e)),
    pooledRisk μ ω β - pooledRisk μ ω βstar =
      quad (pooledCov μ) (β - βstar) -
        2 * dot (β - βstar)
          (WithLp.toLp 2 (fun j : Fin p =>
            ∑ e : ι, ω e * ∫ z, residAt βstar z * z.1 j ∂(μ e))) := by
  /- @proof-region region.target-node.session.75d7c0f275d99266 begin -/
  intro p ι _ _ μ hμ β βstar ω hω hint_star hint_beta hint_cross hint_prod
  have hper : ∀ e : ι,
      risk (μ e) β - risk (μ e) βstar
        = quad (covMat (μ e)) (β - βstar)
          - 2 * ∑ j : Fin p, (β - βstar) j * ∫ z : Eucl p × ℝ, residAt βstar z * z.1 j ∂(μ e) := by
    intro e
    have hcoord : ∀ j : Fin p, (β - βstar) j = β j - βstar j := by
      intro j; rfl
    have hd_eq : ∀ z : Eucl p × ℝ, dot β z.1 - dot βstar z.1 = ∑ j : Fin p, (β - βstar) j * z.1 j := by
      intro z
      simp only [dot]
      have hterm : ∀ j : Fin p, (β - βstar) j * z.1 j = β j * z.1 j - βstar j * z.1 j := by
        intro j
        rw [hcoord j, sub_mul]
      simp only [hterm, Finset.sum_sub_distrib]
    have hd_sq : ∀ z : Eucl p × ℝ, (dot β z.1 - dot βstar z.1) ^ 2
        = ∑ i : Fin p, ∑ j : Fin p, (β - βstar) i * (β - βstar) j * (z.1 i * z.1 j) := by
      intro z
      rw [hd_eq z, pow_two, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hpt : ∀ z : Eucl p × ℝ, (z.2 - dot β z.1) ^ 2 - (z.2 - dot βstar z.1) ^ 2
        = (dot β z.1 - dot βstar z.1) ^ 2
          - 2 * ((z.2 - dot βstar z.1) * (dot β z.1 - dot βstar z.1)) := by
      intro z; ring
    have hcd_pt : ∀ z : Eucl p × ℝ, (z.2 - dot βstar z.1) * (dot β z.1 - dot βstar z.1)
        = ∑ j : Fin p, (β - βstar) j * ((z.2 - dot βstar z.1) * z.1 j) := by
      intro z
      rw [hd_eq z, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hI3 : Integrable (fun z : Eucl p × ℝ => (dot β z.1 - dot βstar z.1) ^ 2) (μ e) := by
      rw [show (fun z : Eucl p × ℝ => (dot β z.1 - dot βstar z.1) ^ 2)
            = (fun z => ∑ i : Fin p, ∑ j : Fin p, (β - βstar) i * (β - βstar) j * (z.1 i * z.1 j)) from funext hd_sq]
      exact integrable_finset_sum Finset.univ (fun i _ => integrable_finset_sum Finset.univ (fun j _ => (hint_prod e i j).const_mul _))
    have hI2 : Integrable (fun z : Eucl p × ℝ => (z.2 - dot βstar z.1) * (dot β z.1 - dot βstar z.1)) (μ e) := by
      rw [show (fun z : Eucl p × ℝ => (z.2 - dot βstar z.1) * (dot β z.1 - dot βstar z.1))
            = (fun z => ∑ j : Fin p, (β - βstar) j * ((z.2 - dot βstar z.1) * z.1 j)) from funext hcd_pt]
      exact integrable_finset_sum Finset.univ (fun j _ => (hint_cross e j).const_mul _)
    have hI1 : Integrable (fun z : Eucl p × ℝ => (z.2 - dot βstar z.1) ^ 2) (μ e) := hint_star e
    have hB : Integrable (fun z : Eucl p × ℝ => 2 * ((z.2 - dot βstar z.1) * (dot β z.1 - dot βstar z.1))) (μ e) :=
      hI2.const_mul 2
    have hd2int : ∫ z, (dot β z.1 - dot βstar z.1) ^ 2 ∂(μ e)
        = ∑ i : Fin p, ∑ j : Fin p, (β - βstar) i * (β - βstar) j * (∫ z, z.1 i * z.1 j ∂(μ e)) := by
      calc ∫ z, (dot β z.1 - dot βstar z.1) ^ 2 ∂(μ e)
          = ∫ z, ∑ i : Fin p, ∑ j : Fin p, (β - βstar) i * (β - βstar) j * (z.1 i * z.1 j) ∂(μ e) := by
              rw [integral_congr_ae (Filter.Eventually.of_forall hd_sq)]
        _ = ∑ i : Fin p, ∫ z, ∑ j : Fin p, (β - βstar) i * (β - βstar) j * (z.1 i * z.1 j) ∂(μ e) := by
              rw [integral_finset_sum]
              intro i _
              exact integrable_finset_sum Finset.univ (fun j _ => (hint_prod e i j).const_mul _)
        _ = ∑ i : Fin p, ∑ j : Fin p, ∫ z, (β - βstar) i * (β - βstar) j * (z.1 i * z.1 j) ∂(μ e) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [integral_finset_sum]
              intro j _
              exact (hint_prod e i j).const_mul _
        _ = ∑ i : Fin p, ∑ j : Fin p, (β - βstar) i * (β - βstar) j * (∫ z, z.1 i * z.1 j ∂(μ e)) := by
              apply Finset.sum_congr rfl
              intro i _
              apply Finset.sum_congr rfl
              intro j _
              rw [integral_const_mul]
    have hcdint : ∫ z, (z.2 - dot βstar z.1) * (dot β z.1 - dot βstar z.1) ∂(μ e)
        = ∑ j : Fin p, (β - βstar) j * ∫ z, residAt βstar z * z.1 j ∂(μ e) := by
      calc ∫ z, (z.2 - dot βstar z.1) * (dot β z.1 - dot βstar z.1) ∂(μ e)
          = ∫ z, ∑ j : Fin p, (β - βstar) j * ((z.2 - dot βstar z.1) * z.1 j) ∂(μ e) := by
              rw [integral_congr_ae (Filter.Eventually.of_forall hcd_pt)]
        _ = ∑ j : Fin p, ∫ z, (β - βstar) j * ((z.2 - dot βstar z.1) * z.1 j) ∂(μ e) := by
              rw [integral_finset_sum]
              intro j _
              exact (hint_cross e j).const_mul _
        _ = ∑ j : Fin p, (β - βstar) j * ∫ z, (z.2 - dot βstar z.1) * z.1 j ∂(μ e) := by
              apply Finset.sum_congr rfl
              intro j _
              rw [integral_const_mul]
        _ = ∑ j : Fin p, (β - βstar) j * ∫ z, residAt βstar z * z.1 j ∂(μ e) := by
              exact rfl
    have hquad : quad (covMat (μ e)) (β - βstar)
        = ∑ i : Fin p, ∑ j : Fin p, (β - βstar) i * (β - βstar) j * (∫ z, z.1 i * z.1 j ∂(μ e)) := by
      simp only [quad, covMat]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hsub : risk (μ e) β - risk (μ e) βstar
        = ∫ z, (z.2 - dot β z.1) ^ 2 ∂(μ e) - ∫ z, (z.2 - dot βstar z.1) ^ 2 ∂(μ e) := rfl
    calc risk (μ e) β - risk (μ e) βstar
        = ∫ z, ((z.2 - dot β z.1) ^ 2 - (z.2 - dot βstar z.1) ^ 2) ∂(μ e) := by
            rw [hsub, ← integral_sub (hint_beta e) hI1]
      _ = ∫ z, ((dot β z.1 - dot βstar z.1) ^ 2 - 2 * ((z.2 - dot βstar z.1) * (dot β z.1 - dot βstar z.1))) ∂(μ e) := by
            rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
      _ = ∫ z, (dot β z.1 - dot βstar z.1) ^ 2 ∂(μ e)
            - ∫ z, 2 * ((z.2 - dot βstar z.1) * (dot β z.1 - dot βstar z.1)) ∂(μ e) := by
            rw [integral_sub hI3 hB]
      _ = ∫ z, (dot β z.1 - dot βstar z.1) ^ 2 ∂(μ e)
            - 2 * ∫ z, (z.2 - dot βstar z.1) * (dot β z.1 - dot βstar z.1) ∂(μ e) := by
            rw [integral_const_mul]
      _ = quad (covMat (μ e)) (β - βstar)
            - 2 * ∑ j : Fin p, (β - βstar) j * ∫ z, residAt βstar z * z.1 j ∂(μ e) := by
            rw [hd2int, ← hquad, hcdint]
  have hpooled : pooledRisk μ ω β - pooledRisk μ ω βstar
      = ∑ e : ι, ω e * (quad (covMat (μ e)) (β - βstar)
          - 2 * ∑ j : Fin p, (β - βstar) j * ∫ z : Eucl p × ℝ, residAt βstar z * z.1 j ∂(μ e)) := by
    simp only [pooledRisk]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e _
    rw [← mul_sub, hper e]
  have h1 : pooledRisk μ ω β - pooledRisk μ ω βstar
      = (∑ e : ι, ω e * quad (covMat (μ e)) (β - βstar))
        - 2 * ∑ e : ι, ω e * ∑ j : Fin p, (β - βstar) j * ∫ z : Eucl p × ℝ, residAt βstar z * z.1 j ∂(μ e) := by
    rw [hpooled]
    have hstep : ∀ e : ι, ω e * (quad (covMat (μ e)) (β - βstar)
          - 2 * ∑ j : Fin p, (β - βstar) j * ∫ z : Eucl p × ℝ, residAt βstar z * z.1 j ∂(μ e))
        = ω e * quad (covMat (μ e)) (β - βstar)
          - 2 * (ω e * ∑ j : Fin p, (β - βstar) j * ∫ z : Eucl p × ℝ, residAt βstar z * z.1 j ∂(μ e)) := by
      intro e; ring
    simp only [hstep, Finset.sum_sub_distrib]
    congr 1
    rw [Finset.mul_sum]
  have hA : (∑ e : ι, ω e * quad (covMat (μ e)) (β - βstar)) = quad (pooledCov μ) (β - βstar) := by
    have hquad_smul : ∀ (c : ℝ) (M : Matrix (Fin p) (Fin p) ℝ) (v : Eucl p),
        quad (c • M) v = c * quad M v := by
      intro c M v
      simp only [quad, Matrix.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hquad_sum : ∀ (M : ι → Matrix (Fin p) (Fin p) ℝ) (v : Eucl p),
        quad (∑ e, M e) v = ∑ e, quad (M e) v := by
      intro M v
      have hmat : ∀ i j : Fin p, (∑ e : ι, M e) i j = ∑ e : ι, M e i j := by
        intro i j
        exact Matrix.sum_apply i j Finset.univ M
      have h1 : ∀ i j : Fin p, (∑ e : ι, M e i j) * v i * v j = ∑ e : ι, (M e i j * v i) * v j := by
        intro i j; rw [Finset.sum_mul, Finset.sum_mul]
      have hcomm3 : (∑ i : Fin p, ∑ j : Fin p, ∑ e : ι, (M e i j * v i) * v j)
          = ∑ e : ι, ∑ i : Fin p, ∑ j : Fin p, (M e i j * v i) * v j := by
        rw [show (∑ i : Fin p, ∑ j : Fin p, ∑ e : ι, (M e i j * v i) * v j)
              = ∑ i : Fin p, ∑ e : ι, ∑ j : Fin p, (M e i j * v i) * v j from
              Finset.sum_congr rfl (fun i _ => Finset.sum_comm)]
        rw [Finset.sum_comm]
      simp only [quad, hmat, h1, hcomm3]
    calc (∑ e : ι, ω e * quad (covMat (μ e)) (β - βstar))
        = ∑ e : ι, (Fintype.card ι : ℝ)⁻¹ * quad (covMat (μ e)) (β - βstar) := by
            apply Finset.sum_congr rfl
            intro e _
            rw [hω e]
      _ = (Fintype.card ι : ℝ)⁻¹ * ∑ e : ι, quad (covMat (μ e)) (β - βstar) := by
            rw [Finset.mul_sum]
      _ = (Fintype.card ι : ℝ)⁻¹ * quad (∑ e : ι, covMat (μ e)) (β - βstar) := by
            rw [← hquad_sum]
      _ = quad ((Fintype.card ι : ℝ)⁻¹ • ∑ e : ι, covMat (μ e)) (β - βstar) := by
            rw [← hquad_smul]
      _ = quad (pooledCov μ) (β - βstar) := by
            simp only [pooledCov]
  have hB : (∑ e : ι, ω e * ∑ j : Fin p, (β - βstar) j * ∫ z : Eucl p × ℝ, residAt βstar z * z.1 j ∂(μ e))
      = dot (β - βstar) (WithLp.toLp 2 (fun j : Fin p => ∑ e : ι, ω e * ∫ z : Eucl p × ℝ, residAt βstar z * z.1 j ∂(μ e))) := by
    simp only [dot, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [h1, hA, hB]
  /- @proof-region region.target-node.session.75d7c0f275d99266 end -/

end Statlib.Imported

