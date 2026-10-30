import ProverJobs.paper_fresh_20261028t224543381z_eills.Vocabulary
import ProverJobs.paper_fresh_20261028t224543381z_eills.Base
import ProverJobs.paper_fresh_20261028t224543381z_eills.ProvedNodes.Node_3875025507_3baf775f_b5f784cb
import ProverJobs.paper_fresh_20261028t224543381z_eills.ExternalNodes.Node_6515c10a3b2a6920f75d

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
theorem statopia_math_node_3737555372_fcbbc30d : ∀ (p : ℕ) {ι : Type*} [Fintype ι] [Nonempty ι]
    (μ : ι → Measure (Eucl p × ℝ))
    (βstar : Eucl p) (S_star : Finset (Fin p))
    (hS_star : ∀ j : Fin p, j ∈ S_star ↔ βstar j ≠ 0)
    (hProb : ∀ e : ι, IsProbabilityMeasure (μ e))
    (hIntX : ∀ (e : ι) (j : Fin p),
      Integrable (fun z : Eucl p × ℝ => residAt βstar z * z.1 j) (μ e))
    (β : Eucl p)
    (hDelta_supp : ∀ j : Fin p, j ∉ suppVec β ∪ S_star → (β - βstar) j = 0)
    (hUbar_zero : ∀ j : Fin p, j ∈ S_star →
      (Fintype.card ι : ℝ)⁻¹ * ∑ e, ∫ z, residAt βstar z * z.1 j ∂(μ e) = 0)
    (kappaL : ℝ) (hkappaL_pos : 0 < kappaL)
    (hLoewner : ∀ v : Eucl p, kappaL * ‖v‖ ^ 2 ≤ quad (pooledCov μ) v),
      ∀ eps : ℝ, 0 < eps →
        2 * dot (β - βstar)
            (WithLp.toLp 2 (fun j : Fin p =>
              (Fintype.card ι : ℝ)⁻¹ * ∑ e, ∫ z, residAt βstar z * z.1 j ∂(μ e)))
          ≤ eps * quad (pooledCov μ) (β - βstar)
                      + eps⁻¹ * kappaL⁻¹ * bCoeff μ βstar (suppVec β) := by
  /- @proof-region region.target-node.session.0cb4fd3873d39d04 begin -/
  classical
  intro p ι hfintype hnonempty μ βstar S_star hS_star hProb hIntX β hDelta_supp hUbar_zero
    kappaL hkappaL_pos hLoewner eps heps
  set F : Fin p → ℝ := fun j : Fin p =>
    (Fintype.card ι : ℝ)⁻¹ * ∑ e, ∫ z : Eucl p × ℝ, residAt βstar z * z.1 j ∂(μ e) with hF
  have hFzero : ∀ j : Fin p, j ∈ S_star → F j = 0 := by
    intro j hj
    simpa only [hF] using hUbar_zero j hj
  have hdot : dot (β - βstar) (WithLp.toLp 2 F) = ∑ j : Fin p, (β - βstar) j * F j := by
    simp [dot]
  have ht : (0 : ℝ) < eps * kappaL := mul_pos heps hkappaL_pos
  have hT : (0 : ℝ) ≤ (eps * kappaL)⁻¹ := (inv_pos.mpr ht).le
  have hTt : (eps * kappaL)⁻¹ * (eps * kappaL) = 1 := inv_mul_cancel₀ ht.ne'
  have hzero : ∀ j : Fin p, j ∉ suppVec β → (β - βstar) j * F j = 0 := by
    intro j hj
    by_cases hjs : j ∈ S_star
    · rw [hFzero j hjs, mul_zero]
    · have hx : j ∉ suppVec β ∪ S_star := by simp [hj, hjs]
      rw [hDelta_supp j hx, zero_mul]
  have hsum_main : (∑ j : Fin p, (β - βstar) j * F j)
      = ∑ j ∈ suppVec β, (β - βstar) j * F j :=
    (Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => hzero x hx)).symm
  have hbc : bCoeff μ βstar (suppVec β) = ∑ j ∈ suppVec β, (F j) ^ 2 := by
    simp only [bCoeff, hF]
  have hsq_le : (∑ j ∈ suppVec β, ((β - βstar) j) ^ 2) ≤ ‖(β - βstar : Eucl p)‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    have hcongr : ∀ j : Fin p,
        ‖((β - βstar : Eucl p)).ofLp j‖ ^ 2 = ((β - βstar) j) ^ 2 := by
      intro j
      rw [Real.norm_eq_abs, sq_abs]
    calc ∑ j ∈ suppVec β, ((β - βstar) j) ^ 2
        = ∑ j ∈ suppVec β, ‖((β - βstar : Eucl p)).ofLp j‖ ^ 2 :=
          Finset.sum_congr rfl (fun j _ => (hcongr j).symm)
      _ ≤ ∑ j : Fin p, ‖((β - βstar : Eucl p)).ofLp j‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun x _ _ => by positivity)
  have key : ∀ a b : ℝ,
      2 * (a * b) ≤ (eps * kappaL) * a ^ 2 + (eps * kappaL)⁻¹ * b ^ 2 := by
    intro a b
    have hbase : 2 * ((eps * kappaL) * a) * b ≤ ((eps * kappaL) * a) ^ 2 + b ^ 2 :=
      two_mul_le_add_sq _ _
    have hmul : (eps * kappaL)⁻¹ * (2 * ((eps * kappaL) * a) * b)
        ≤ (eps * kappaL)⁻¹ * (((eps * kappaL) * a) ^ 2 + b ^ 2) :=
      mul_le_mul_of_nonneg_left hbase hT
    have hlt : (eps * kappaL)⁻¹ * (2 * ((eps * kappaL) * a) * b) = 2 * (a * b) := by
      have h1 : (eps * kappaL)⁻¹ * (2 * ((eps * kappaL) * a) * b)
          = 2 * ((eps * kappaL)⁻¹ * (eps * kappaL)) * (a * b) := by ring
      rw [h1, hTt]
      ring
    have hrt : (eps * kappaL)⁻¹ * (((eps * kappaL) * a) ^ 2 + b ^ 2)
        = (eps * kappaL) * a ^ 2 + (eps * kappaL)⁻¹ * b ^ 2 := by
      have h1 : (eps * kappaL)⁻¹ * (((eps * kappaL) * a) ^ 2 + b ^ 2)
          = ((eps * kappaL)⁻¹ * (eps * kappaL)) * ((eps * kappaL) * a ^ 2)
            + (eps * kappaL)⁻¹ * b ^ 2 := by ring
      rw [h1, hTt]
      ring
    linarith [hmul, hlt, hrt]
  have h1 : 2 * (∑ j ∈ suppVec β, (β - βstar) j * F j)
      ≤ (eps * kappaL) * (∑ j ∈ suppVec β, ((β - βstar) j) ^ 2)
        + (eps * kappaL)⁻¹ * (∑ j ∈ suppVec β, (F j) ^ 2) := by
    have hA : 2 * (∑ j ∈ suppVec β, (β - βstar) j * F j)
        ≤ ∑ j ∈ suppVec β,
            ((eps * kappaL) * ((β - βstar) j) ^ 2 + (eps * kappaL)⁻¹ * (F j) ^ 2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun j _ => key ((β - βstar) j) (F j))
    have hB : ∑ j ∈ suppVec β,
          ((eps * kappaL) * ((β - βstar) j) ^ 2 + (eps * kappaL)⁻¹ * (F j) ^ 2)
        = (eps * kappaL) * (∑ j ∈ suppVec β, ((β - βstar) j) ^ 2)
          + (eps * kappaL)⁻¹ * (∑ j ∈ suppVec β, (F j) ^ 2) := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]
    linarith [hA, hB]
  have h2 : (eps * kappaL) * (∑ j ∈ suppVec β, ((β - βstar) j) ^ 2)
      ≤ (eps * kappaL) * ‖(β - βstar : Eucl p)‖ ^ 2 :=
    mul_le_mul_of_nonneg_left hsq_le ht.le
  have h3 : (eps * kappaL) * ‖(β - βstar : Eucl p)‖ ^ 2
      = eps * (kappaL * ‖(β - βstar : Eucl p)‖ ^ 2) := by ring
  have h4 : eps * (kappaL * ‖(β - βstar : Eucl p)‖ ^ 2)
      ≤ eps * quad (pooledCov μ) (β - βstar) :=
    mul_le_mul_of_nonneg_left (hLoewner (β - βstar)) heps.le
  have h5 : (eps * kappaL)⁻¹ = eps⁻¹ * kappaL⁻¹ := mul_inv eps kappaL
  rw [hdot]
  calc 2 * (∑ j : Fin p, (β - βstar) j * F j)
      = 2 * (∑ j ∈ suppVec β, (β - βstar) j * F j) := by rw [hsum_main]
    _ ≤ (eps * kappaL) * (∑ j ∈ suppVec β, ((β - βstar) j) ^ 2)
          + (eps * kappaL)⁻¹ * (∑ j ∈ suppVec β, (F j) ^ 2) := h1
    _ ≤ (eps * kappaL) * ‖(β - βstar : Eucl p)‖ ^ 2
          + (eps * kappaL)⁻¹ * (∑ j ∈ suppVec β, (F j) ^ 2) := by linarith [h2]
    _ = eps * (kappaL * ‖(β - βstar : Eucl p)‖ ^ 2)
          + (eps * kappaL)⁻¹ * (∑ j ∈ suppVec β, (F j) ^ 2) := by rw [h3]
    _ ≤ eps * quad (pooledCov μ) (β - βstar)
          + (eps * kappaL)⁻¹ * (∑ j ∈ suppVec β, (F j) ^ 2) := by linarith [h4]
    _ = eps * quad (pooledCov μ) (β - βstar)
          + eps⁻¹ * kappaL⁻¹ * (∑ j ∈ suppVec β, (F j) ^ 2) := by rw [h5]
    _ = eps * quad (pooledCov μ) (β - βstar)
          + eps⁻¹ * kappaL⁻¹ * bCoeff μ βstar (suppVec β) := by rw [hbc]
  /- @proof-region region.target-node.session.0cb4fd3873d39d04 end -/

end Statlib.Imported

