import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.Definitions
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M031_Vocabulary
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M032_Base
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M033_Node_1445702134_3c8d3810_8f7a15fe
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M048_Node_2166343247_005d03d5_e190fc11
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M049_Node_2170215388_e7c55f79_ebbe8cb6
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M034_Node_3224678180_5a630a9f_7124eef7

/- Original module ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.ProvedNodes.Node_2202358284_edd9d5c8_284d2a8b; genuine source relocated, namespace-isolated only. -/
namespace DPCompletedProof
open _root_.Statlib.Imported




open MeasureTheory
open Statlib.Imported

noncomputable section
open MeasureTheory
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_2202358284_edd9d5c8 : ∀ (t eps beta : ℝ) (n s : ℕ)
    (ht : 1 ≤ t) (heps_pos : 0 < eps) (heps_lt_one : eps < 1) (hbeta : 0 < beta)
    (hs : 1 ≤ s) (hns : t + (s : ℝ) ≤ (n : ℝ)),
    (∫ alpha in Set.Ioo (0 : ℝ) eps, alpha ^ (t + (s : ℝ) + beta) / risingFac alpha n) /
        (∫ alpha in Set.Ioo (0 : ℝ) eps, alpha ^ (t + beta) / risingFac alpha n) ≤
      (Real.log ((n : ℝ) / (1 + eps))) ^ (-(s : ℝ)) *
        (lowerGamma (t + (s : ℝ) + beta) (eps * Real.log ((n : ℝ) / (1 + eps))) /
          lowerGamma (t + beta) (eps * Real.log ((n : ℝ) / (1 + eps)))) := by
  /- @proof-region region.target-node.session.84e3fb704a600876 begin -/
  intro t eps beta n s ht heps_pos heps_lt_one hbeta hs hns
  have hsR : (1:ℝ) ≤ (s:ℝ) := by exact_mod_cast hs
  have hts : (2:ℝ) ≤ t + (s:ℝ) := by linarith
  have hn2 : (2:ℝ) ≤ (n:ℝ) := le_trans hts hns
  have hL : 0 < Real.log ((n:ℝ) / (1 + eps)) := by
    apply Real.log_pos
    rw [lt_div_iff₀ (by linarith : (0:ℝ) < 1 + eps)]
    linarith
  have hNL : 0 < eps * Real.log ((n:ℝ) / (1 + eps)) := mul_pos heps_pos hL
  have hgamma_pos : ∀ x y : ℝ, 0 < x → 0 < y → 0 < lowerGamma x y :=
    statopia_math_node_3224678180_5a630a9f.1
  have hnum : (∫ x in Set.Ioo (0:ℝ) eps, x ^ (t + (s:ℝ) + beta) / risingFac x n)
      = ∫ x in Set.Ioo (0:ℝ) eps, x ^ (s:ℝ) * (x ^ (t + beta) / risingFac x n) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    have hx0 : 0 < x := hx.1
    rw [show t + (s:ℝ) + beta = (s:ℝ) + (t + beta) by ring, Real.rpow_add hx0]
    ring
  have hsubst : ∀ M : ℝ, 0 < M →
      (∫ x in Set.Ioo (0:ℝ) eps, Real.exp (-(Real.log ((n:ℝ) / (1 + eps)) * x)) * x ^ (M - 1))
        = (Real.log ((n:ℝ) / (1 + eps))) ^ (-M) *
            lowerGamma M (eps * Real.log ((n:ℝ) / (1 + eps))) := by
    intro M hM
    set L := Real.log ((n:ℝ) / (1 + eps)) with hLdef
    have hLpos : 0 < L := hL
    have hLG : 0 < eps * L := hNL
    have hG : lowerGamma M (eps * L) = ∫ z in Set.Ioc (0:ℝ) (eps * L), z ^ (M - 1) * Real.exp (-z) := by
      rw [show lowerGamma M (eps * L) = ∫ z in (0:ℝ)..(eps * L), z ^ (M - 1) * Real.exp (-z) from rfl,
        intervalIntegral.integral_of_le (le_of_lt hLG)]
    rw [hG]
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo]
    have hstep : (∫ x in Set.Ioc (0:ℝ) eps, (L * x) ^ (M - 1) * Real.exp (-(L * x)))
        = L ^ (M - 1) * ∫ x in Set.Ioc (0:ℝ) eps, Real.exp (-(L * x)) * x ^ (M - 1) := by
      rw [show (∫ x in Set.Ioc (0:ℝ) eps, (L * x) ^ (M - 1) * Real.exp (-(L * x)))
          = ∫ x in Set.Ioc (0:ℝ) eps, L ^ (M - 1) * (Real.exp (-(L * x)) * x ^ (M - 1)) from by
        apply MeasureTheory.setIntegral_congr_ae measurableSet_Ioc
        exact Filter.Eventually.of_forall (fun x hx => by
          rw [Real.mul_rpow (le_of_lt hLpos) (le_of_lt hx.1)]
          ring)]
      rw [MeasureTheory.integral_const_mul]
    have hsub : (∫ z in Set.Ioc (0:ℝ) (eps * L), z ^ (M - 1) * Real.exp (-z))
        = L * ∫ x in Set.Ioc (0:ℝ) eps, (L * x) ^ (M - 1) * Real.exp (-(L * x)) := by
      rw [← intervalIntegral.integral_of_le (le_of_lt hLG),
        ← intervalIntegral.integral_of_le heps_pos.le]
      have h := intervalIntegral.mul_integral_comp_mul_left (a := (0:ℝ)) (b := eps)
        (f := fun z : ℝ => z ^ (M - 1) * Real.exp (-z)) L
      rw [mul_zero, mul_comm L eps] at h
      exact h.symm
    rw [hsub, hstep]
    have hp1 : L ^ (-M) * L ^ M = 1 := by
      rw [← Real.rpow_add hLpos, neg_add_cancel, Real.rpow_zero]
    have hp2 : L * L ^ (M - 1) = L ^ M := by
      rw [mul_comm L, ← Real.rpow_add_one (ne_of_gt hLpos)]
      congr 1
      ring
    calc (∫ x in Set.Ioc (0:ℝ) eps, Real.exp (-(L * x)) * x ^ (M - 1))
        = 1 * (∫ x in Set.Ioc (0:ℝ) eps, Real.exp (-(L * x)) * x ^ (M - 1)) := by ring
      _ = (L ^ (-M) * L ^ M) *
            (∫ x in Set.Ioc (0:ℝ) eps, Real.exp (-(L * x)) * x ^ (M - 1)) := by rw [hp1]
      _ = L ^ (-M) *
            (L ^ M * (∫ x in Set.Ioc (0:ℝ) eps, Real.exp (-(L * x)) * x ^ (M - 1))) := by ring
      _ = L ^ (-M) *
            ((L * L ^ (M - 1)) *
              (∫ x in Set.Ioc (0:ℝ) eps, Real.exp (-(L * x)) * x ^ (M - 1))) := by
            rw [hp2]
      _ = L ^ (-M) *
            (L * (L ^ (M - 1) *
              (∫ x in Set.Ioc (0:ℝ) eps, Real.exp (-(L * x)) * x ^ (M - 1)))) := by
            ring
  have hmlr : ∀ (p W u : ℝ → ℝ),
      (∀ x ∈ Set.Ioo (0:ℝ) eps, 0 < p x) →
      MonotoneOn W (Set.Ioo (0:ℝ) eps) →
      MonotoneOn u (Set.Ioo (0:ℝ) eps) →
      IntegrableOn p (Set.Ioo (0:ℝ) eps) →
      IntegrableOn (fun x => W x * p x) (Set.Ioo (0:ℝ) eps) →
      IntegrableOn (fun x => u x * p x) (Set.Ioo (0:ℝ) eps) →
      IntegrableOn (fun x => u x * (W x * p x)) (Set.Ioo (0:ℝ) eps) →
      0 < ∫ x in Set.Ioo (0:ℝ) eps, p x →
      0 < ∫ x in Set.Ioo (0:ℝ) eps, W x * p x →
      (∫ x in Set.Ioo (0:ℝ) eps, u x * p x) / (∫ x in Set.Ioo (0:ℝ) eps, p x)
        ≤ (∫ x in Set.Ioo (0:ℝ) eps, u x * (W x * p x)) /
            (∫ x in Set.Ioo (0:ℝ) eps, W x * p x) := by
    intro p W u hp hW hu hIp hIWp hIup hIuWp hPpos hWpos
    have hinner : ∀ x : ℝ, (∫ y in Set.Ioo (0:ℝ) eps, (u x - u y) * (W x - W y) * p x * p y)
        = (u x * (W x * p x)) * (∫ y in Set.Ioo (0:ℝ) eps, p y)
            - (u x * p x) * (∫ y in Set.Ioo (0:ℝ) eps, W y * p y)
            - (W x * p x) * (∫ y in Set.Ioo (0:ℝ) eps, u y * p y)
            + p x * (∫ y in Set.Ioo (0:ℝ) eps, u y * (W y * p y)) := by
      intro x
      have hi1 : Integrable (fun y : ℝ => (u x * (W x * p x)) * p y) (volume.restrict (Set.Ioo (0:ℝ) eps)) :=
        hIp.const_mul _
      have hi2 : Integrable (fun y : ℝ => (u x * p x) * (W y * p y)) (volume.restrict (Set.Ioo (0:ℝ) eps)) :=
        hIWp.const_mul _
      have hi3 : Integrable (fun y : ℝ => (W x * p x) * (u y * p y)) (volume.restrict (Set.Ioo (0:ℝ) eps)) :=
        hIup.const_mul _
      have hi4 : Integrable (fun y : ℝ => p x * (u y * (W y * p y))) (volume.restrict (Set.Ioo (0:ℝ) eps)) :=
        hIuWp.const_mul _
      have hi12 := hi1.sub hi2
      have hi123 := hi12.sub hi3
      have hc : (∫ y in Set.Ioo (0:ℝ) eps, (u x - u y) * (W x - W y) * p x * p y)
          = ∫ y in Set.Ioo (0:ℝ) eps, ((u x * (W x * p x)) * p y - (u x * p x) * (W y * p y)
              - (W x * p x) * (u y * p y) + p x * (u y * (W y * p y))) := by
        apply MeasureTheory.setIntegral_congr_ae measurableSet_Ioo
        exact Filter.Eventually.of_forall (fun y _ => by ring)
      rw [hc]
      have e1 : (∫ y in Set.Ioo (0:ℝ) eps, ((u x * (W x * p x)) * p y - (u x * p x) * (W y * p y)
              - (W x * p x) * (u y * p y) + p x * (u y * (W y * p y))))
          = (∫ y in Set.Ioo (0:ℝ) eps, ((u x * (W x * p x)) * p y - (u x * p x) * (W y * p y)
              - (W x * p x) * (u y * p y))) + ∫ y in Set.Ioo (0:ℝ) eps, p x * (u y * (W y * p y)) :=
        MeasureTheory.integral_add hi123 hi4
      rw [e1]
      have e2 : (∫ y in Set.Ioo (0:ℝ) eps, ((u x * (W x * p x)) * p y - (u x * p x) * (W y * p y)
              - (W x * p x) * (u y * p y)))
          = (∫ y in Set.Ioo (0:ℝ) eps, ((u x * (W x * p x)) * p y - (u x * p x) * (W y * p y)))
              - ∫ y in Set.Ioo (0:ℝ) eps, (W x * p x) * (u y * p y) :=
        MeasureTheory.integral_sub hi12 hi3
      rw [e2]
      have e3 : (∫ y in Set.Ioo (0:ℝ) eps, ((u x * (W x * p x)) * p y - (u x * p x) * (W y * p y)))
          = (∫ y in Set.Ioo (0:ℝ) eps, (u x * (W x * p x)) * p y)
              - ∫ y in Set.Ioo (0:ℝ) eps, (u x * p x) * (W y * p y) :=
        MeasureTheory.integral_sub hi1 hi2
      rw [e3]
      have g1 : (∫ y in Set.Ioo (0:ℝ) eps, (u x * (W x * p x)) * p y)
          = (u x * (W x * p x)) * ∫ y in Set.Ioo (0:ℝ) eps, p y :=
        MeasureTheory.integral_const_mul _ _
      have g2 : (∫ y in Set.Ioo (0:ℝ) eps, (u x * p x) * (W y * p y))
          = (u x * p x) * ∫ y in Set.Ioo (0:ℝ) eps, W y * p y :=
        MeasureTheory.integral_const_mul _ _
      have g3 : (∫ y in Set.Ioo (0:ℝ) eps, (W x * p x) * (u y * p y))
          = (W x * p x) * ∫ y in Set.Ioo (0:ℝ) eps, u y * p y :=
        MeasureTheory.integral_const_mul _ _
      have g4 : (∫ y in Set.Ioo (0:ℝ) eps, p x * (u y * (W y * p y)))
          = p x * ∫ y in Set.Ioo (0:ℝ) eps, u y * (W y * p y) :=
        MeasureTheory.integral_const_mul _ _
      rw [g1, g2, g3, g4]
    have hT_nonneg : 0 ≤ ∫ x in Set.Ioo (0:ℝ) eps, ∫ y in Set.Ioo (0:ℝ) eps, (u x - u y) * (W x - W y) * p x * p y := by
      apply MeasureTheory.setIntegral_nonneg measurableSet_Ioo
      intro x hx
      apply MeasureTheory.setIntegral_nonneg measurableSet_Ioo
      intro y hy
      have h1 : 0 ≤ (u x - u y) * (W x - W y) := by
        rcases le_total x y with hxy | hyx
        · have a : u x ≤ u y := hu hx hy hxy
          have b : W x ≤ W y := hW hx hy hxy
          have e : (u x - u y) * (W x - W y) = (u y - u x) * (W y - W x) := by ring
          rw [e]
          exact mul_nonneg (by linarith) (by linarith)
        · have a : u y ≤ u x := hu hy hx hyx
          have b : W y ≤ W x := hW hy hx hyx
          exact mul_nonneg (by linarith : (0:ℝ) ≤ u x - u y) (by linarith : (0:ℝ) ≤ W x - W y)
      exact mul_nonneg (mul_nonneg h1 (le_of_lt (hp x hx))) (le_of_lt (hp y hy))
    have hval : (∫ x in Set.Ioo (0:ℝ) eps, ∫ y in Set.Ioo (0:ℝ) eps, (u x - u y) * (W x - W y) * p x * p y)
        = 2 * ((∫ y in Set.Ioo (0:ℝ) eps, u y * (W y * p y)) * (∫ y in Set.Ioo (0:ℝ) eps, p y)
            - (∫ y in Set.Ioo (0:ℝ) eps, u y * p y) * (∫ y in Set.Ioo (0:ℝ) eps, W y * p y)) := by
      have g0 : (∫ x in Set.Ioo (0:ℝ) eps, ∫ y in Set.Ioo (0:ℝ) eps, (u x - u y) * (W x - W y) * p x * p y)
          = ∫ x in Set.Ioo (0:ℝ) eps, ((u x * (W x * p x)) * (∫ y in Set.Ioo (0:ℝ) eps, p y)
              - (u x * p x) * (∫ y in Set.Ioo (0:ℝ) eps, W y * p y)
              - (W x * p x) * (∫ y in Set.Ioo (0:ℝ) eps, u y * p y)
              + p x * (∫ y in Set.Ioo (0:ℝ) eps, u y * (W y * p y))) := by
        apply MeasureTheory.setIntegral_congr_ae measurableSet_Ioo
        exact Filter.Eventually.of_forall (fun x _ => hinner x)
      rw [g0]
      have gi1 : Integrable (fun x : ℝ => (u x * (W x * p x)) * (∫ y in Set.Ioo (0:ℝ) eps, p y))
          (volume.restrict (Set.Ioo (0:ℝ) eps)) := hIuWp.mul_const _
      have gi2 : Integrable (fun x : ℝ => (u x * p x) * (∫ y in Set.Ioo (0:ℝ) eps, W y * p y))
          (volume.restrict (Set.Ioo (0:ℝ) eps)) := hIup.mul_const _
      have gi3 : Integrable (fun x : ℝ => (W x * p x) * (∫ y in Set.Ioo (0:ℝ) eps, u y * p y))
          (volume.restrict (Set.Ioo (0:ℝ) eps)) := hIWp.mul_const _
      have gi4 : Integrable (fun x : ℝ => p x * (∫ y in Set.Ioo (0:ℝ) eps, u y * (W y * p y)))
          (volume.restrict (Set.Ioo (0:ℝ) eps)) := hIp.mul_const _
      have gi12 := gi1.sub gi2
      have gi123 := gi12.sub gi3
      have gj1 : (∫ x in Set.Ioo (0:ℝ) eps, ((u x * (W x * p x)) * (∫ y in Set.Ioo (0:ℝ) eps, p y)
              - (u x * p x) * (∫ y in Set.Ioo (0:ℝ) eps, W y * p y)
              - (W x * p x) * (∫ y in Set.Ioo (0:ℝ) eps, u y * p y)
              + p x * (∫ y in Set.Ioo (0:ℝ) eps, u y * (W y * p y))))
          = (∫ x in Set.Ioo (0:ℝ) eps, ((u x * (W x * p x)) * (∫ y in Set.Ioo (0:ℝ) eps, p y)
              - (u x * p x) * (∫ y in Set.Ioo (0:ℝ) eps, W y * p y)
              - (W x * p x) * (∫ y in Set.Ioo (0:ℝ) eps, u y * p y)))
            + ∫ x in Set.Ioo (0:ℝ) eps, p x * (∫ y in Set.Ioo (0:ℝ) eps, u y * (W y * p y)) :=
        MeasureTheory.integral_add gi123 gi4
      rw [gj1]
      have gj2 : (∫ x in Set.Ioo (0:ℝ) eps, ((u x * (W x * p x)) * (∫ y in Set.Ioo (0:ℝ) eps, p y)
              - (u x * p x) * (∫ y in Set.Ioo (0:ℝ) eps, W y * p y)
              - (W x * p x) * (∫ y in Set.Ioo (0:ℝ) eps, u y * p y)))
          = (∫ x in Set.Ioo (0:ℝ) eps, ((u x * (W x * p x)) * (∫ y in Set.Ioo (0:ℝ) eps, p y)
              - (u x * p x) * (∫ y in Set.Ioo (0:ℝ) eps, W y * p y)))
            - ∫ x in Set.Ioo (0:ℝ) eps, (W x * p x) * (∫ y in Set.Ioo (0:ℝ) eps, u y * p y) :=
        MeasureTheory.integral_sub gi12 gi3
      rw [gj2]
      have gj3 : (∫ x in Set.Ioo (0:ℝ) eps, ((u x * (W x * p x)) * (∫ y in Set.Ioo (0:ℝ) eps, p y)
              - (u x * p x) * (∫ y in Set.Ioo (0:ℝ) eps, W y * p y)))
          = (∫ x in Set.Ioo (0:ℝ) eps, (u x * (W x * p x)) * (∫ y in Set.Ioo (0:ℝ) eps, p y))
            - ∫ x in Set.Ioo (0:ℝ) eps, (u x * p x) * (∫ y in Set.Ioo (0:ℝ) eps, W y * p y) :=
        MeasureTheory.integral_sub gi1 gi2
      rw [gj3]
      have gk1 : (∫ x in Set.Ioo (0:ℝ) eps, (u x * (W x * p x)) * (∫ y in Set.Ioo (0:ℝ) eps, p y))
          = (∫ y in Set.Ioo (0:ℝ) eps, p y) * (∫ x in Set.Ioo (0:ℝ) eps, u x * (W x * p x)) := by
        rw [show (∫ x in Set.Ioo (0:ℝ) eps, (u x * (W x * p x)) * (∫ y in Set.Ioo (0:ℝ) eps, p y))
            = ∫ x in Set.Ioo (0:ℝ) eps, (∫ y in Set.Ioo (0:ℝ) eps, p y) * (u x * (W x * p x)) from
          MeasureTheory.setIntegral_congr_ae measurableSet_Ioo
            (Filter.Eventually.of_forall (fun x _ => mul_comm _ _))]
        exact MeasureTheory.integral_const_mul _ _
      have gk2 : (∫ x in Set.Ioo (0:ℝ) eps, (u x * p x) * (∫ y in Set.Ioo (0:ℝ) eps, W y * p y))
          = (∫ y in Set.Ioo (0:ℝ) eps, W y * p y) * (∫ x in Set.Ioo (0:ℝ) eps, u x * p x) := by
        rw [show (∫ x in Set.Ioo (0:ℝ) eps, (u x * p x) * (∫ y in Set.Ioo (0:ℝ) eps, W y * p y))
            = ∫ x in Set.Ioo (0:ℝ) eps, (∫ y in Set.Ioo (0:ℝ) eps, W y * p y) * (u x * p x) from
          MeasureTheory.setIntegral_congr_ae measurableSet_Ioo
            (Filter.Eventually.of_forall (fun x _ => mul_comm _ _))]
        exact MeasureTheory.integral_const_mul _ _
      have gk3 : (∫ x in Set.Ioo (0:ℝ) eps, (W x * p x) * (∫ y in Set.Ioo (0:ℝ) eps, u y * p y))
          = (∫ y in Set.Ioo (0:ℝ) eps, u y * p y) * (∫ x in Set.Ioo (0:ℝ) eps, W x * p x) := by
        rw [show (∫ x in Set.Ioo (0:ℝ) eps, (W x * p x) * (∫ y in Set.Ioo (0:ℝ) eps, u y * p y))
            = ∫ x in Set.Ioo (0:ℝ) eps, (∫ y in Set.Ioo (0:ℝ) eps, u y * p y) * (W x * p x) from
          MeasureTheory.setIntegral_congr_ae measurableSet_Ioo
            (Filter.Eventually.of_forall (fun x _ => mul_comm _ _))]
        exact MeasureTheory.integral_const_mul _ _
      have gk4 : (∫ x in Set.Ioo (0:ℝ) eps, p x * (∫ y in Set.Ioo (0:ℝ) eps, u y * (W y * p y)))
          = (∫ y in Set.Ioo (0:ℝ) eps, u y * (W y * p y)) * (∫ x in Set.Ioo (0:ℝ) eps, p x) := by
        rw [show (∫ x in Set.Ioo (0:ℝ) eps, p x * (∫ y in Set.Ioo (0:ℝ) eps, u y * (W y * p y)))
            = ∫ x in Set.Ioo (0:ℝ) eps, (∫ y in Set.Ioo (0:ℝ) eps, u y * (W y * p y)) * p x from
          MeasureTheory.setIntegral_congr_ae measurableSet_Ioo
            (Filter.Eventually.of_forall (fun x _ => mul_comm _ _))]
        exact MeasureTheory.integral_const_mul _ _
      rw [gk1, gk2, gk3, gk4]
      ring
    have hcrossY : (∫ y in Set.Ioo (0:ℝ) eps, u y * p y) * (∫ y in Set.Ioo (0:ℝ) eps, W y * p y)
        ≤ (∫ y in Set.Ioo (0:ℝ) eps, u y * (W y * p y)) * (∫ y in Set.Ioo (0:ℝ) eps, p y) := by
      have h2 : 0 ≤ 2 * ((∫ y in Set.Ioo (0:ℝ) eps, u y * (W y * p y)) * (∫ y in Set.Ioo (0:ℝ) eps, p y)
            - (∫ y in Set.Ioo (0:ℝ) eps, u y * p y) * (∫ y in Set.Ioo (0:ℝ) eps, W y * p y)) := by
        rw [← hval]
        exact hT_nonneg
      linarith
    have hcross : (∫ x in Set.Ioo (0:ℝ) eps, u x * p x) * (∫ x in Set.Ioo (0:ℝ) eps, W x * p x)
        ≤ (∫ x in Set.Ioo (0:ℝ) eps, u x * (W x * p x)) * (∫ x in Set.Ioo (0:ℝ) eps, p x) := hcrossY
    have hB : (∫ x in Set.Ioo (0:ℝ) eps, p x) ≠ 0 := ne_of_gt hPpos
    have hD : (∫ x in Set.Ioo (0:ℝ) eps, W x * p x) ≠ 0 := ne_of_gt hWpos
    have hcross2 : (∫ x in Set.Ioo (0:ℝ) eps, u x * p x) * (∫ x in Set.Ioo (0:ℝ) eps, W x * p x)
        ≤ (∫ x in Set.Ioo (0:ℝ) eps, p x) * (∫ x in Set.Ioo (0:ℝ) eps, u x * W x * p x) := by
      have hEq : (∫ x in Set.Ioo (0:ℝ) eps, u x * W x * p x)
          = ∫ x in Set.Ioo (0:ℝ) eps, u x * (W x * p x) := by
        apply MeasureTheory.setIntegral_congr_ae measurableSet_Ioo
        exact Filter.Eventually.of_forall (fun x _ => by ring)
      calc (∫ x in Set.Ioo (0:ℝ) eps, u x * p x) * (∫ x in Set.Ioo (0:ℝ) eps, W x * p x)
          ≤ (∫ x in Set.Ioo (0:ℝ) eps, u x * (W x * p x)) * (∫ x in Set.Ioo (0:ℝ) eps, p x) := hcross
        _ = (∫ x in Set.Ioo (0:ℝ) eps, p x) * (∫ x in Set.Ioo (0:ℝ) eps, u x * W x * p x) := by
            rw [hEq]
            ring
    field_simp
    linarith [hcross2]
  have hpt : ∀ x ∈ Set.Ioo (0:ℝ) eps,
      (Real.exp (-(Real.log ((n:ℝ) / (1 + eps)) * x)) * risingFac x n / x) *
          (x ^ (t + beta) / risingFac x n)
        = Real.exp (-(Real.log ((n:ℝ) / (1 + eps)) * x)) * x ^ (t + beta - 1) := by
    intro x hx
    have hx0 : 0 < x := hx.1
    have hfac : risingFac x n ≠ 0 :=
      ne_of_gt (statopia_math_node_1445702134_3c8d3810.1 x n hx0)
    have hxne : x ≠ 0 := ne_of_gt hx0
    rw [Real.rpow_sub_one hxne]
    field_simp
  have hgen_den : (∫ x in Set.Ioo (0:ℝ) eps,
        (Real.exp (-(Real.log ((n:ℝ) / (1 + eps)) * x)) * risingFac x n / x) *
          (x ^ (t + beta) / risingFac x n))
      = ∫ x in Set.Ioo (0:ℝ) eps,
          Real.exp (-(Real.log ((n:ℝ) / (1 + eps)) * x)) * x ^ (t + beta - 1) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    exact hpt x hx
  have hgen_num : (∫ x in Set.Ioo (0:ℝ) eps, x ^ (s:ℝ) *
        ((Real.exp (-(Real.log ((n:ℝ) / (1 + eps)) * x)) * risingFac x n / x) *
          (x ^ (t + beta) / risingFac x n)))
      = ∫ x in Set.Ioo (0:ℝ) eps, x ^ (s:ℝ) *
          (Real.exp (-(Real.log ((n:ℝ) / (1 + eps)) * x)) * x ^ (t + beta - 1)) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    rw [hpt x hx]
  have hgen_num2 : (∫ x in Set.Ioo (0:ℝ) eps, x ^ (s:ℝ) *
        (Real.exp (-(Real.log ((n:ℝ) / (1 + eps)) * x)) * x ^ (t + beta - 1)))
      = ∫ x in Set.Ioo (0:ℝ) eps,
          Real.exp (-(Real.log ((n:ℝ) / (1 + eps)) * x)) * x ^ (t + (s:ℝ) + beta - 1) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    have hx0 : 0 < x := hx.1
    rw [show t + (s:ℝ) + beta - 1 = (s:ℝ) + (t + beta - 1) by ring, Real.rpow_add hx0]
    ring
  have key : (∫ x in Set.Ioo (0:ℝ) eps, x ^ (s:ℝ) * (x ^ (t + beta) / risingFac x n)) /
        (∫ x in Set.Ioo (0:ℝ) eps, x ^ (t + beta) / risingFac x n)
      ≤ (∫ x in Set.Ioo (0:ℝ) eps, x ^ (s:ℝ) *
            ((Real.exp (-(Real.log ((n:ℝ) / (1 + eps)) * x)) * risingFac x n / x) *
              (x ^ (t + beta) / risingFac x n))) /
          (∫ x in Set.Ioo (0:ℝ) eps,
            (Real.exp (-(Real.log ((n:ℝ) / (1 + eps)) * x)) * risingFac x n / x) *
              (x ^ (t + beta) / risingFac x n)) :=
    hmlr (fun x => x ^ (t + beta) / risingFac x n)
      (fun x => Real.exp (-(Real.log ((n:ℝ) / (1 + eps)) * x)) * risingFac x n / x)
      (fun x => x ^ (s:ℝ))
      (by
        intro x hx
        exact div_pos (Real.rpow_pos_of_pos hx.1 _)
          (statopia_math_node_1445702134_3c8d3810.1 x n hx.1))
      (statopia_math_node_2170215388_e7c55f79 eps n heps_pos heps_lt_one (by exact_mod_cast hn2))
      (by
        have h := Real.monotoneOn_rpow_Ici_of_exponent_nonneg (show (0:ℝ) ≤ (s:ℝ) by positivity)
        exact h.mono (fun x hx => le_of_lt hx.1))
      (by
        have hbase : IntegrableOn (fun x : ℝ => x ^ (t + beta - 1)) (Set.Ioo (0:ℝ) eps) :=
          (intervalIntegral.integrableOn_Ioo_rpow_iff (s := t + beta - 1) heps_pos).mpr (by linarith)
        have hdom : IntegrableOn (fun x : ℝ => x ^ (t + beta - 1) * (1 / ((n - 1).factorial : ℝ)))
            (Set.Ioo (0:ℝ) eps) := hbase.mul_const _
        have hmeas : AEStronglyMeasurable (fun x : ℝ => x ^ (t + beta) / risingFac x n)
            (volume.restrict (Set.Ioo (0:ℝ) eps)) := by
          refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
          intro x hx
          have h1 : ContinuousAt (fun y : ℝ => y ^ (t + beta)) x :=
            (Real.hasDerivAt_rpow_const (Or.inr (by linarith : (1:ℝ) ≤ t + beta))).continuousAt
          have h2 : ContinuousAt (fun y : ℝ => risingFac y n) x := by
            unfold risingFac
            fun_prop
          exact (h1.div h2 (ne_of_gt (statopia_math_node_1445702134_3c8d3810.1 x n hx.1))).continuousWithinAt
        have hbdd : ∀ᵐ x ∂(volume.restrict (Set.Ioo (0:ℝ) eps)),
            ‖x ^ (t + beta) / risingFac x n‖ ≤
              x ^ (t + beta - 1) * (1 / ((n - 1).factorial : ℝ)) := by
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
          have hx0 : 0 < x := hx.1
          have hx1 : x ≤ 1 := le_of_lt (lt_trans hx.2 heps_lt_one)
          have hn1 : 1 ≤ n := by
            have h1 : (1:ℝ) ≤ (n:ℝ) := by linarith
            exact_mod_cast h1
          have hCpos : (0:ℝ) < ((n - 1).factorial : ℝ) := by
            have h := Nat.factorial_pos (n - 1)
            exact_mod_cast h
          have hCne : ((n - 1).factorial : ℝ) ≠ 0 := ne_of_gt hCpos
          have hfac : 0 < risingFac x n := statopia_math_node_1445702134_3c8d3810.1 x n hx0
          have hle : x * ((n - 1).factorial : ℝ) ≤ risingFac x n :=
            statopia_math_node_1445702134_3c8d3810.2.2.1 x n hx0 hx1 hn1
          have hxne : x ≠ 0 := ne_of_gt hx0
          have hpos : 0 < x ^ (t + beta) / risingFac x n :=
            div_pos (Real.rpow_pos_of_pos hx0 _) hfac
          rw [Real.norm_eq_abs, abs_of_pos hpos]
          have hstep1 : x ^ (t + beta) / risingFac x n ≤
              x ^ (t + beta) / (x * ((n - 1).factorial : ℝ)) :=
            div_le_div_of_nonneg_left (Real.rpow_nonneg (le_of_lt hx0) _) (mul_pos hx0 hCpos) hle
          have hpow : x ^ (t + beta) = x ^ (t + beta - 1) * x := by
            rw [← Real.rpow_add_one hxne]
            congr 1
            ring
          calc x ^ (t + beta) / risingFac x n
              ≤ x ^ (t + beta) / (x * ((n - 1).factorial : ℝ)) := hstep1
            _ = x ^ (t + beta - 1) * (1 / ((n - 1).factorial : ℝ)) := by
                rw [hpow]
                field_simp
        exact hdom.mono' hmeas hbdd)
      (by
        have hbase : IntegrableOn (fun x : ℝ => x ^ (t + beta - 1)) (Set.Ioo (0:ℝ) eps) :=
          (intervalIntegral.integrableOn_Ioo_rpow_iff (s := t + beta - 1) heps_pos).mpr (by linarith)
        have hmeasW : AEStronglyMeasurable (fun x : ℝ =>
            (Real.exp (-(Real.log ((n:ℝ) / (1 + eps)) * x)) * risingFac x n / x) *
              (x ^ (t + beta) / risingFac x n)) (volume.restrict (Set.Ioo (0:ℝ) eps)) := by
          refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
          intro x hx
          have hfacc : ContinuousAt (fun y : ℝ => risingFac y n) x := by
            unfold risingFac
            fun_prop
          have he : ContinuousAt
              (fun y : ℝ => Real.exp (-(Real.log ((n:ℝ) / (1 + eps)) * y))) x := by
            fun_prop
          have h1 : ContinuousAt
              (fun y : ℝ => Real.exp (-(Real.log ((n:ℝ) / (1 + eps)) * y)) * risingFac y n / y) x :=
            (he.mul hfacc).div continuousAt_id (ne_of_gt hx.1)
          have h2 : ContinuousAt (fun y : ℝ => y ^ (t + beta)) x :=
            (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hx.1))).continuousAt
          have h3 : ContinuousAt (fun y : ℝ => y ^ (t + beta) / risingFac y n) x :=
            h2.div hfacc (ne_of_gt (statopia_math_node_1445702134_3c8d3810.1 x n hx.1))
          exact (h1.mul h3).continuousWithinAt
        have hbddW : ∀ᵐ x ∂(volume.restrict (Set.Ioo (0:ℝ) eps)),
            ‖(Real.exp (-(Real.log ((n:ℝ) / (1 + eps)) * x)) * risingFac x n / x) *
              (x ^ (t + beta) / risingFac x n)‖ ≤ x ^ (t + beta - 1) := by
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
          have hx0 : 0 < x := hx.1
          have hxne : x ≠ 0 := ne_of_gt hx0
          rw [hpt x hx, Real.norm_eq_abs]
          have hxpow : 0 ≤ x ^ (t + beta - 1) := Real.rpow_nonneg (le_of_lt hx0) _
          have hexp_le : Real.exp (-(Real.log ((n:ℝ) / (1 + eps)) * x)) ≤ 1 := by
            have hl : -(Real.log ((n:ℝ) / (1 + eps)) * x) ≤ 0 := by
              have hp : 0 < Real.log ((n:ℝ) / (1 + eps)) * x := mul_pos hL hx0
              linarith
            have h := Real.exp_le_exp.mpr hl
            simpa using h
          rw [abs_of_nonneg (mul_nonneg (le_of_lt (Real.exp_pos _)) hxpow)]
          calc Real.exp (-(Real.log ((n:ℝ) / (1 + eps)) * x)) * x ^ (t + beta - 1)
              ≤ 1 * x ^ (t + beta - 1) := mul_le_mul_of_nonneg_right hexp_le hxpow
            _ = x ^ (t + beta - 1) := by ring
        exact hbase.mono' hmeasW hbddW)
      (by
        have hbase : IntegrableOn (fun x : ℝ => x ^ (t + (s:ℝ) + beta - 1)) (Set.Ioo (0:ℝ) eps) :=
          (intervalIntegral.integrableOn_Ioo_rpow_iff (s := t + (s:ℝ) + beta - 1) heps_pos).mpr
            (by linarith)
        have hdom : IntegrableOn
            (fun x : ℝ => x ^ (t + (s:ℝ) + beta - 1) * (1 / ((n - 1).factorial : ℝ)))
            (Set.Ioo (0:ℝ) eps) := hbase.mul_const _
        have hmeasu : AEStronglyMeasurable (fun x : ℝ => x ^ (s:ℝ) * (x ^ (t + beta) / risingFac x n))
            (volume.restrict (Set.Ioo (0:ℝ) eps)) := by
          refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
          intro x hx
          have hfacc : ContinuousAt (fun y : ℝ => risingFac y n) x := by
            unfold risingFac
            fun_prop
          have h1 : ContinuousAt (fun y : ℝ => y ^ (s:ℝ)) x :=
            (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hx.1))).continuousAt
          have h2 : ContinuousAt (fun y : ℝ => y ^ (t + beta)) x :=
            (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hx.1))).continuousAt
          have h3 : ContinuousAt (fun y : ℝ => y ^ (t + beta) / risingFac y n) x :=
            h2.div hfacc (ne_of_gt (statopia_math_node_1445702134_3c8d3810.1 x n hx.1))
          exact (h1.mul h3).continuousWithinAt
        have hbddu : ∀ᵐ x ∂(volume.restrict (Set.Ioo (0:ℝ) eps)),
            ‖x ^ (s:ℝ) * (x ^ (t + beta) / risingFac x n)‖ ≤
              x ^ (t + (s:ℝ) + beta - 1) * (1 / ((n - 1).factorial : ℝ)) := by
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
          have hx0 : 0 < x := hx.1
          have hx1 : x ≤ 1 := le_of_lt (lt_trans hx.2 heps_lt_one)
          have hxne : x ≠ 0 := ne_of_gt hx0
          have hn1 : 1 ≤ n := by
            have h1 : (1:ℝ) ≤ (n:ℝ) := by linarith
            exact_mod_cast h1
          have hCpos : (0:ℝ) < ((n - 1).factorial : ℝ) := by
            have h := Nat.factorial_pos (n - 1)
            exact_mod_cast h
          have hfac : 0 < risingFac x n := statopia_math_node_1445702134_3c8d3810.1 x n hx0
          have hle : x * ((n - 1).factorial : ℝ) ≤ risingFac x n :=
            statopia_math_node_1445702134_3c8d3810.2.2.1 x n hx0 hx1 hn1
          have hpos : 0 < x ^ (s:ℝ) * (x ^ (t + beta) / risingFac x n) :=
            mul_pos (Real.rpow_pos_of_pos hx0 _) (div_pos (Real.rpow_pos_of_pos hx0 _) hfac)
          rw [Real.norm_eq_abs, abs_of_pos hpos]
          have h1mul : x ^ (s:ℝ) * x ^ (t + beta) = x ^ (t + (s:ℝ) + beta) := by
            rw [← Real.rpow_add hx0]
            congr 1
            ring
          have hcomb : x ^ (s:ℝ) * (x ^ (t + beta) / risingFac x n)
              = x ^ (t + (s:ℝ) + beta) / risingFac x n := by
            rw [← h1mul]
            ring
          rw [hcomb]
          have hstep1 : x ^ (t + (s:ℝ) + beta) / risingFac x n ≤
              x ^ (t + (s:ℝ) + beta) / (x * ((n - 1).factorial : ℝ)) :=
            div_le_div_of_nonneg_left (Real.rpow_nonneg (le_of_lt hx0) _) (mul_pos hx0 hCpos) hle
          have hpow : x ^ (t + (s:ℝ) + beta) = x ^ (t + (s:ℝ) + beta - 1) * x := by
            rw [← Real.rpow_add_one hxne]
            congr 1
            ring
          calc x ^ (t + (s:ℝ) + beta) / risingFac x n
              ≤ x ^ (t + (s:ℝ) + beta) / (x * ((n - 1).factorial : ℝ)) := hstep1
            _ = x ^ (t + (s:ℝ) + beta - 1) * (1 / ((n - 1).factorial : ℝ)) := by
                rw [hpow]
                field_simp
        exact hdom.mono' hmeasu hbddu)
      (by
        have hbase : IntegrableOn (fun x : ℝ => x ^ (t + (s:ℝ) + beta - 1)) (Set.Ioo (0:ℝ) eps) :=
          (intervalIntegral.integrableOn_Ioo_rpow_iff (s := t + (s:ℝ) + beta - 1) heps_pos).mpr
            (by linarith)
        have hmeasUW : AEStronglyMeasurable (fun x : ℝ =>
            x ^ (s:ℝ) * ((Real.exp (-(Real.log ((n:ℝ) / (1 + eps)) * x)) * risingFac x n / x) *
              (x ^ (t + beta) / risingFac x n))) (volume.restrict (Set.Ioo (0:ℝ) eps)) := by
          refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
          intro x hx
          have hfacc : ContinuousAt (fun y : ℝ => risingFac y n) x := by
            unfold risingFac
            fun_prop
          have h1 : ContinuousAt (fun y : ℝ => y ^ (s:ℝ)) x :=
            (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hx.1))).continuousAt
          have he : ContinuousAt
              (fun y : ℝ => Real.exp (-(Real.log ((n:ℝ) / (1 + eps)) * y))) x := by
            fun_prop
          have h2 : ContinuousAt (fun y : ℝ => y ^ (t + beta)) x :=
            (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hx.1))).continuousAt
          have h3 : ContinuousAt (fun y : ℝ => y ^ (t + beta) / risingFac y n) x :=
            h2.div hfacc (ne_of_gt (statopia_math_node_1445702134_3c8d3810.1 x n hx.1))
          have h4 : ContinuousAt
              (fun y : ℝ => Real.exp (-(Real.log ((n:ℝ) / (1 + eps)) * y)) * risingFac y n / y) x :=
            (he.mul hfacc).div continuousAt_id (ne_of_gt hx.1)
          exact (h1.mul (h4.mul h3)).continuousWithinAt
        have hbddUW : ∀ᵐ x ∂(volume.restrict (Set.Ioo (0:ℝ) eps)),
            ‖x ^ (s:ℝ) * ((Real.exp (-(Real.log ((n:ℝ) / (1 + eps)) * x)) * risingFac x n / x) *
              (x ^ (t + beta) / risingFac x n))‖ ≤ x ^ (t + (s:ℝ) + beta - 1) := by
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
          have hx0 : 0 < x := hx.1
          rw [hpt x hx]
          have hxspos : 0 ≤ x ^ (s:ℝ) := Real.rpow_nonneg (le_of_lt hx0) _
          have hep : 0 < Real.exp (-(Real.log ((n:ℝ) / (1 + eps)) * x)) := Real.exp_pos _
          have hpowmul : x ^ (s:ℝ) * x ^ (t + beta - 1) = x ^ (t + (s:ℝ) + beta - 1) := by
            rw [← Real.rpow_add hx0]
            congr 1
            ring
          have hexp_le : Real.exp (-(Real.log ((n:ℝ) / (1 + eps)) * x)) ≤ 1 := by
            have hl : -(Real.log ((n:ℝ) / (1 + eps)) * x) ≤ 0 := by
              have hp : 0 < Real.log ((n:ℝ) / (1 + eps)) * x := mul_pos hL hx0
              linarith
            have h := Real.exp_le_exp.mpr hl
            simpa using h
          rw [Real.norm_eq_abs]
          rw [abs_of_nonneg (mul_nonneg hxspos (mul_nonneg (le_of_lt hep) (Real.rpow_nonneg (le_of_lt hx0) _)))]
          calc x ^ (s:ℝ) * (Real.exp (-(Real.log ((n:ℝ) / (1 + eps)) * x)) * x ^ (t + beta - 1))
              = Real.exp (-(Real.log ((n:ℝ) / (1 + eps)) * x)) *
                  (x ^ (s:ℝ) * x ^ (t + beta - 1)) := by ring
            _ = Real.exp (-(Real.log ((n:ℝ) / (1 + eps)) * x)) *
                  x ^ (t + (s:ℝ) + beta - 1) := by rw [hpowmul]
            _ ≤ 1 * x ^ (t + (s:ℝ) + beta - 1) :=
                mul_le_mul_of_nonneg_right hexp_le (Real.rpow_nonneg (le_of_lt hx0) _)
            _ = x ^ (t + (s:ℝ) + beta - 1) := by ring
        exact hbase.mono' hmeasUW hbddUW)
      (by
        have hp_int : IntegrableOn (fun x : ℝ => x ^ (t + beta) / risingFac x n)
            (Set.Ioo (0:ℝ) eps) := by
          have hbase : IntegrableOn (fun x : ℝ => x ^ (t + beta - 1)) (Set.Ioo (0:ℝ) eps) :=
            (intervalIntegral.integrableOn_Ioo_rpow_iff (s := t + beta - 1) heps_pos).mpr (by linarith)
          have hdom : IntegrableOn (fun x : ℝ => x ^ (t + beta - 1) * (1 / ((n - 1).factorial : ℝ)))
              (Set.Ioo (0:ℝ) eps) := hbase.mul_const _
          have hmeas : AEStronglyMeasurable (fun x : ℝ => x ^ (t + beta) / risingFac x n)
              (volume.restrict (Set.Ioo (0:ℝ) eps)) := by
            refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
            intro x hx
            have h1 : ContinuousAt (fun y : ℝ => y ^ (t + beta)) x :=
              (Real.hasDerivAt_rpow_const (Or.inr (by linarith : (1:ℝ) ≤ t + beta))).continuousAt
            have h2 : ContinuousAt (fun y : ℝ => risingFac y n) x := by
              unfold risingFac
              fun_prop
            exact (h1.div h2 (ne_of_gt (statopia_math_node_1445702134_3c8d3810.1 x n hx.1))).continuousWithinAt
          have hbdd : ∀ᵐ x ∂(volume.restrict (Set.Ioo (0:ℝ) eps)),
              ‖x ^ (t + beta) / risingFac x n‖ ≤
                x ^ (t + beta - 1) * (1 / ((n - 1).factorial : ℝ)) := by
            filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
            have hx0 : 0 < x := hx.1
            have hx1 : x ≤ 1 := le_of_lt (lt_trans hx.2 heps_lt_one)
            have hn1 : 1 ≤ n := by
              have h1 : (1:ℝ) ≤ (n:ℝ) := by linarith
              exact_mod_cast h1
            have hCpos : (0:ℝ) < ((n - 1).factorial : ℝ) := by
              have h := Nat.factorial_pos (n - 1)
              exact_mod_cast h
            have hfac : 0 < risingFac x n := statopia_math_node_1445702134_3c8d3810.1 x n hx0
            have hle : x * ((n - 1).factorial : ℝ) ≤ risingFac x n :=
              statopia_math_node_1445702134_3c8d3810.2.2.1 x n hx0 hx1 hn1
            have hxne : x ≠ 0 := ne_of_gt hx0
            have hpos : 0 < x ^ (t + beta) / risingFac x n :=
              div_pos (Real.rpow_pos_of_pos hx0 _) hfac
            rw [Real.norm_eq_abs, abs_of_pos hpos]
            have hstep1 : x ^ (t + beta) / risingFac x n ≤
                x ^ (t + beta) / (x * ((n - 1).factorial : ℝ)) :=
              div_le_div_of_nonneg_left (Real.rpow_nonneg (le_of_lt hx0) _) (mul_pos hx0 hCpos) hle
            have hpow : x ^ (t + beta) = x ^ (t + beta - 1) * x := by
              rw [← Real.rpow_add_one hxne]
              congr 1
              ring
            calc x ^ (t + beta) / risingFac x n
                ≤ x ^ (t + beta) / (x * ((n - 1).factorial : ℝ)) := hstep1
              _ = x ^ (t + beta - 1) * (1 / ((n - 1).factorial : ℝ)) := by
                  rw [hpow]
                  field_simp
          exact hdom.mono' hmeas hbdd
        have hnn : 0 ≤ᶠ[ae (volume.restrict (Set.Ioo (0:ℝ) eps))]
            (fun x : ℝ => x ^ (t + beta) / risingFac x n) := by
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
          exact le_of_lt (div_pos (Real.rpow_pos_of_pos hx.1 _)
            (statopia_math_node_1445702134_3c8d3810.1 x n hx.1))
        rw [MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae hnn hp_int]
        have hset : Function.support (fun x : ℝ => x ^ (t + beta) / risingFac x n) ∩
              Set.Ioo (0:ℝ) eps = Set.Ioo (0:ℝ) eps := by
          apply Set.inter_eq_right.mpr
          intro x hx
          have hne : x ^ (t + beta) / risingFac x n ≠ 0 :=
            ne_of_gt (div_pos (Real.rpow_pos_of_pos hx.1 _)
              (statopia_math_node_1445702134_3c8d3810.1 x n hx.1))
          simpa [Function.mem_support] using hne
        rw [hset, Real.volume_Ioo]
        simpa using (ENNReal.ofReal_pos.mpr heps_pos))
      (by
        rw [hgen_den, hsubst (t + beta) (by linarith)]
        exact mul_pos (Real.rpow_pos_of_pos hL _) (hgamma_pos _ _ (by linarith) hNL))
  have hLne : Real.log ((n:ℝ) / (1 + eps)) ≠ 0 := ne_of_gt hL
  have hg1 : 0 < lowerGamma (t + (s:ℝ) + beta) (eps * Real.log ((n:ℝ) / (1 + eps))) :=
    hgamma_pos _ _ (by linarith) hNL
  have hg0 : 0 < lowerGamma (t + beta) (eps * Real.log ((n:ℝ) / (1 + eps))) :=
    hgamma_pos _ _ (by linarith) hNL
  have hp1ne : Real.log ((n:ℝ) / (1 + eps)) ^ (-(t + beta)) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hL _)
  have hpsne : Real.log ((n:ℝ) / (1 + eps)) ^ (-(s:ℝ)) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hL _)
  have hg1ne : lowerGamma (t + (s:ℝ) + beta) (eps * Real.log ((n:ℝ) / (1 + eps))) ≠ 0 :=
    ne_of_gt hg1
  have hg0ne : lowerGamma (t + beta) (eps * Real.log ((n:ℝ) / (1 + eps))) ≠ 0 := ne_of_gt hg0
  calc (∫ x in Set.Ioo (0:ℝ) eps, x ^ (t + (s:ℝ) + beta) / risingFac x n) /
        (∫ x in Set.Ioo (0:ℝ) eps, x ^ (t + beta) / risingFac x n)
      = (∫ x in Set.Ioo (0:ℝ) eps, x ^ (s:ℝ) * (x ^ (t + beta) / risingFac x n)) /
          (∫ x in Set.Ioo (0:ℝ) eps, x ^ (t + beta) / risingFac x n) := by rw [hnum]
    _ ≤ (∫ x in Set.Ioo (0:ℝ) eps, x ^ (s:ℝ) *
            ((Real.exp (-(Real.log ((n:ℝ) / (1 + eps)) * x)) * risingFac x n / x) *
              (x ^ (t + beta) / risingFac x n))) /
          (∫ x in Set.Ioo (0:ℝ) eps,
            (Real.exp (-(Real.log ((n:ℝ) / (1 + eps)) * x)) * risingFac x n / x) *
              (x ^ (t + beta) / risingFac x n)) := key
    _ = (∫ x in Set.Ioo (0:ℝ) eps,
            x ^ (s:ℝ) * (Real.exp (-(Real.log ((n:ℝ) / (1 + eps)) * x)) * x ^ (t + beta - 1))) /
          (∫ x in Set.Ioo (0:ℝ) eps,
            Real.exp (-(Real.log ((n:ℝ) / (1 + eps)) * x)) * x ^ (t + beta - 1)) := by
        rw [hgen_num, hgen_den]
    _ = (∫ x in Set.Ioo (0:ℝ) eps,
            Real.exp (-(Real.log ((n:ℝ) / (1 + eps)) * x)) * x ^ (t + (s:ℝ) + beta - 1)) /
          (∫ x in Set.Ioo (0:ℝ) eps,
            Real.exp (-(Real.log ((n:ℝ) / (1 + eps)) * x)) * x ^ (t + beta - 1)) := by
        rw [hgen_num2]
    _ = (Real.log ((n:ℝ) / (1 + eps)) ^ (-(t + (s:ℝ) + beta)) *
            lowerGamma (t + (s:ℝ) + beta) (eps * Real.log ((n:ℝ) / (1 + eps)))) /
          (Real.log ((n:ℝ) / (1 + eps)) ^ (-(t + beta)) *
            lowerGamma (t + beta) (eps * Real.log ((n:ℝ) / (1 + eps)))) := by
        rw [hsubst (t + (s:ℝ) + beta) (by linarith), hsubst (t + beta) (by linarith)]
    _ = Real.log ((n:ℝ) / (1 + eps)) ^ (-(s:ℝ)) *
          (lowerGamma (t + (s:ℝ) + beta) (eps * Real.log ((n:ℝ) / (1 + eps))) /
            lowerGamma (t + beta) (eps * Real.log ((n:ℝ) / (1 + eps)))) := by
        have hpow : Real.log ((n:ℝ) / (1 + eps)) ^ (-(t + (s:ℝ) + beta))
            = Real.log ((n:ℝ) / (1 + eps)) ^ (-(s:ℝ)) *
                Real.log ((n:ℝ) / (1 + eps)) ^ (-(t + beta)) := by
          rw [← Real.rpow_add hL]
          congr 1
          ring
        rw [hpow]
        field_simp
  /- @proof-region region.target-node.session.84e3fb704a600876 end -/

end Statlib.Imported
end
end DPCompletedProof
