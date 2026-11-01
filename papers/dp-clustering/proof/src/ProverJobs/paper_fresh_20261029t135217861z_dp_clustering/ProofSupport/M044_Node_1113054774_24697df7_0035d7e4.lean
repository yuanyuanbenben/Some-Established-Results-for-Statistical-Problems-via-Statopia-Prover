import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.Definitions
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M031_Vocabulary
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M032_Base
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M033_Node_1445702134_3c8d3810_8f7a15fe
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M034_Node_3224678180_5a630a9f_7124eef7

/- Original module ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.ProvedNodes.Node_1113054774_24697df7_0035d7e4; genuine source relocated, namespace-isolated only. -/
namespace DPCompletedProof
open _root_.Statlib.Imported


open MeasureTheory
open Statlib.Imported

noncomputable section
open MeasureTheory
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_1113054774_24697df7 : ∀ (t eps beta : ℝ) (n s : ℕ)
    (ht : 1 ≤ t) (heps : 0 < eps) (heps1 : eps < 1) (hbeta : 0 < beta)
    (hs : 1 ≤ s) (hts : t + (s : ℝ) ≤ (n : ℝ)),
    (∫ a in Set.Ioo (0 : ℝ) eps,
        a ^ (s : ℝ) * ((Real.exp 1 * (n : ℝ)) ^ (-a) * a ^ (t + beta - 1))) /
      (∫ a in Set.Ioo (0 : ℝ) eps,
        (Real.exp 1 * (n : ℝ)) ^ (-a) * a ^ (t + beta - 1)) ≤
    (∫ a in Set.Ioo (0 : ℝ) eps, a ^ (t + (s : ℝ) + beta) / risingFac a n) /
      (∫ a in Set.Ioo (0 : ℝ) eps, a ^ (t + beta) / risingFac a n) := by
  /- @proof-region region.target-node.session.84bcf97541d850b6 begin -/
  intro t eps beta n s ht heps heps1 hbeta hs hts
  have hs1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hspos : (0 : ℝ) < (s : ℝ) := by linarith
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by linarith
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by linarith
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hexp1 : (1 : ℝ) < Real.exp 1 := by
    have h := Real.add_one_le_exp 1
    linarith
  have hbasepos : (0 : ℝ) < Real.exp 1 * (n : ℝ) := by
    have h := Real.exp_pos 1
    nlinarith
  have hbase1 : (1 : ℝ) < Real.exp 1 * (n : ℝ) := by nlinarith
  set S : Set ℝ := Set.Ioo (0 : ℝ) eps with hS
  set w1 : ℝ → ℝ := fun a => (Real.exp 1 * (n : ℝ)) ^ (-a) * a ^ (t + beta - 1) with hw1
  set w2 : ℝ → ℝ := fun a => a ^ (t + beta) / risingFac a n with hw2
  set g : ℝ → ℝ := fun a => a ^ (s : ℝ) with hg
  set hh : ℝ → ℝ := fun a => (Real.exp 1 * (n : ℝ)) ^ a * a / risingFac a n with hhd
  have hSmeas : MeasurableSet S := measurableSet_Ioo
  obtain ⟨hfpos, hfge, hfbd, hfmono, hfmono2, hfpos2, hfrest⟩ :=
    statopia_math_node_1445702134_3c8d3810
  have hRpos : ∀ a ∈ S, 0 < risingFac a n := fun a ha => hfpos a n ha.1
  have hw1pos : ∀ a ∈ S, 0 < w1 a := by
    intro a ha
    have ha0 : 0 < a := ha.1
    simp only [hw1]
    exact mul_pos (Real.rpow_pos_of_pos hbasepos _) (Real.rpow_pos_of_pos ha0 _)
  have hw1nonneg : ∀ a ∈ S, 0 ≤ w1 a := fun a ha => le_of_lt (hw1pos a ha)
  have hw2pos : ∀ a ∈ S, 0 < w2 a := by
    intro a ha
    have ha0 : 0 < a := ha.1
    simp only [hw2]
    exact div_pos (Real.rpow_pos_of_pos ha0 _) (hRpos a ha)
  have hw2nonneg : ∀ a ∈ S, 0 ≤ w2 a := fun a ha => le_of_lt (hw2pos a ha)
  have hrec : ∀ a ∈ S, w2 a = hh a * w1 a := by
    intro a ha
    have ha0 : 0 < a := ha.1
    have hane : a ≠ 0 := ne_of_gt ha0
    have hT1 : a ^ (t + beta) = a ^ (t + beta - 1) * a := by
      rw [← Real.rpow_add_one hane (t + beta - 1)]
      ring_nf
    have hbe : (Real.exp 1 * (n : ℝ)) ^ a * (Real.exp 1 * (n : ℝ)) ^ (-a) = 1 := by
      rw [← Real.rpow_add hbasepos a (-a)]
      simp
    have hmain : a ^ (t + beta) =
        ((Real.exp 1 * (n : ℝ)) ^ a * a) * ((Real.exp 1 * (n : ℝ)) ^ (-a) * a ^ (t + beta - 1)) := by
      rw [hT1]
      rw [show ((Real.exp 1 * (n : ℝ)) ^ a * a) * ((Real.exp 1 * (n : ℝ)) ^ (-a) * a ^ (t + beta - 1))
            = (a * a ^ (t + beta - 1)) * ((Real.exp 1 * (n : ℝ)) ^ a * (Real.exp 1 * (n : ℝ)) ^ (-a)) by
              ring]
      rw [hbe, mul_one]
      ring
    simp only [hw2, hhd, hw1]
    rw [hmain, div_mul_eq_mul_div]
  have hA2 : ∀ a ∈ S, g a * w2 a = a ^ (t + (s : ℝ) + beta) / risingFac a n := by
    intro a ha
    have ha0 : 0 < a := ha.1
    simp only [hg, hw2]
    rw [← mul_div_assoc, ← Real.rpow_add ha0]
    congr 1
    ring
  have hgmono : ∀ x ∈ S, ∀ y ∈ S, x ≤ y → g x ≤ g y := by
    intro x hx y hy hxy
    have hx0 : (0 : ℝ) ≤ x := le_of_lt hx.1
    simp only [hg]
    exact Real.rpow_le_rpow hx0 hxy (le_of_lt hspos)
  have hn1' : 1 ≤ n := by exact_mod_cast hn1
  have hn1' : 1 ≤ n := by exact_mod_cast hn1
  have hn2' : 2 ≤ n := by exact_mod_cast hn2
  have hsum : ∀ a : ℝ, 0 < a → a ≤ 1 →
      ∑ j ∈ Finset.range (n - 1), (a + ((j : ℝ) + 1))⁻¹ ≤ 1 + Real.log n := by
    intro a ha0 ha1
    have hmain : ∀ m : ℕ, 1 ≤ m →
        ∑ j ∈ Finset.range m, (a + ((j : ℝ) + 1))⁻¹
          ≤ 1 / (a + 1) + Real.log (a + (m : ℝ)) - Real.log (a + 1) := by
      intro m
      induction m with
      | zero => intro h; omega
      | succ k ih =>
        intro _
        rcases Nat.eq_zero_or_pos k with hk | hk
        · subst hk
          simp
        · have hstep := ih (by omega : 1 ≤ k)
          have hkey : (a + ((k : ℝ) + 1))⁻¹
              ≤ Real.log (a + ((k : ℝ) + 1)) - Real.log (a + (k : ℝ)) := by
            have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
            have hp1 : (0 : ℝ) < a + (k : ℝ) := by linarith
            have hp2 : (0 : ℝ) < a + ((k : ℝ) + 1) := by linarith
            have hratio : Real.log ((a + (k : ℝ)) / (a + ((k : ℝ) + 1)))
                ≤ (a + (k : ℝ)) / (a + ((k : ℝ) + 1)) - 1 :=
              Real.log_le_sub_one_of_pos (div_pos hp1 hp2)
            have hlog : Real.log ((a + (k : ℝ)) / (a + ((k : ℝ) + 1)))
                = Real.log (a + (k : ℝ)) - Real.log (a + ((k : ℝ) + 1)) :=
              Real.log_div (ne_of_gt hp1) (ne_of_gt hp2)
            have hdiff : (a + (k : ℝ)) / (a + ((k : ℝ) + 1)) - 1
                = -((a + ((k : ℝ) + 1))⁻¹) := by
              field_simp
              ring
            rw [hlog, hdiff] at hratio
            linarith
          rw [Finset.sum_range_succ]
          have hcast' : a + (((k + 1 : ℕ)) : ℝ) = a + ((k : ℝ) + 1) := by
            push_cast
            ring
          rw [hcast']
          linarith
    have hstep := hmain (n - 1) (by omega)
    have hcastn : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      have h1n : 1 ≤ n := by omega
      rw [Nat.cast_sub h1n]
      norm_num
    rw [hcastn] at hstep
    have hfin1 : 1 / (a + 1) ≤ 1 := by
      have h := one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num)
        (show (1 : ℝ) ≤ a + 1 by linarith)
      simpa using h
    have hfin2 : Real.log (a + ((n : ℝ) - 1)) ≤ Real.log n := by
      apply Real.log_le_log (by linarith)
      linarith
    have hlogpos : 0 ≤ Real.log (a + 1) := Real.log_nonneg (by linarith)
    linarith
  have hhmono : ∀ x ∈ S, ∀ y ∈ S, x ≤ y → hh x ≤ hh y := by
    have hPpos : ∀ a ∈ S, 0 < ∏ j ∈ Finset.range (n - 1), (a + ((j : ℝ) + 1)) := by
      intro a ha
      apply Finset.prod_pos
      intro j hj
      have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith [ha.1]
    have hh_eq : ∀ a ∈ S, hh a
        = (Real.exp 1 * (n : ℝ)) ^ a
          / ∏ j ∈ Finset.range (n - 1), (a + ((j : ℝ) + 1)) := by
      intro a ha
      have ha0 : 0 < a := ha.1
      have hratio : a / risingFac a n = 1 / ∏ j ∈ Finset.range (n - 1), (a + ((j : ℝ) + 1)) :=
        (hfrest n hn1').2.2 a ha0
      simp only [hhd]
      rw [mul_div_assoc, hratio, one_div, ← div_eq_mul_inv]
    intro x hx y hy hxy
    have hx0 : 0 < x := hx.1
    have hx1 : x ≤ 1 := le_of_lt (lt_trans hx.2 heps1)
    set d : ℝ := y - x with hd
    have hd0 : 0 ≤ d := by rw [hd]; linarith
    have hxy' : x + d = y := by rw [hd]; ring
    have hsigma : ∑ j ∈ Finset.range (n - 1), d / (x + ((j : ℝ) + 1)) ≤ d * (1 + Real.log n) := by
      have h1 : d * (∑ j ∈ Finset.range (n - 1), (x + ((j : ℝ) + 1))⁻¹) ≤ d * (1 + Real.log n) :=
        mul_le_mul_of_nonneg_left (hsum x hx0 hx1) hd0
      have h2 : ∑ j ∈ Finset.range (n - 1), d / (x + ((j : ℝ) + 1))
          = d * (∑ j ∈ Finset.range (n - 1), (x + ((j : ℝ) + 1))⁻¹) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [div_eq_mul_inv]
      rw [h2]
      exact h1
    have hstep1 : ∏ j ∈ Finset.range (n - 1), (y + ((j : ℝ) + 1))
        ≤ ∏ j ∈ Finset.range (n - 1),
            ((x + ((j : ℝ) + 1)) * Real.exp (d / (x + ((j : ℝ) + 1)))) := by
      apply Finset.prod_le_prod
      · intro j hj
        have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
        linarith [hx0]
      · intro j hj
        have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
        have hxj : (0 : ℝ) < x + ((j : ℝ) + 1) := by linarith
        have hyj : y + ((j : ℝ) + 1) = (x + ((j : ℝ) + 1)) + d := by
          rw [← hxy']
          ring
        have hexp : 1 + d / (x + ((j : ℝ) + 1)) ≤ Real.exp (d / (x + ((j : ℝ) + 1))) := by
          have h := Real.add_one_le_exp (d / (x + ((j : ℝ) + 1)))
          linarith
        rw [hyj]
        calc (x + ((j : ℝ) + 1)) + d
            = (x + ((j : ℝ) + 1)) * (1 + d / (x + ((j : ℝ) + 1))) := by
              field_simp
          _ ≤ (x + ((j : ℝ) + 1)) * Real.exp (d / (x + ((j : ℝ) + 1))) :=
              mul_le_mul_of_nonneg_left hexp (le_of_lt hxj)
    have hsplit : ∏ j ∈ Finset.range (n - 1),
          ((x + ((j : ℝ) + 1)) * Real.exp (d / (x + ((j : ℝ) + 1))))
        = (∏ j ∈ Finset.range (n - 1), (x + ((j : ℝ) + 1)))
          * Real.exp (∑ j ∈ Finset.range (n - 1), d / (x + ((j : ℝ) + 1))) := by
      rw [Finset.prod_mul_distrib, ← Real.exp_sum]
    have hper : ∏ j ∈ Finset.range (n - 1), (y + ((j : ℝ) + 1))
        ≤ Real.exp (d * (1 + Real.log n))
          * ∏ j ∈ Finset.range (n - 1), (x + ((j : ℝ) + 1)) := by
      calc ∏ j ∈ Finset.range (n - 1), (y + ((j : ℝ) + 1))
          ≤ ∏ j ∈ Finset.range (n - 1),
              ((x + ((j : ℝ) + 1)) * Real.exp (d / (x + ((j : ℝ) + 1)))) := hstep1
        _ = (∏ j ∈ Finset.range (n - 1), (x + ((j : ℝ) + 1)))
            * Real.exp (∑ j ∈ Finset.range (n - 1), d / (x + ((j : ℝ) + 1))) := hsplit
        _ ≤ (∏ j ∈ Finset.range (n - 1), (x + ((j : ℝ) + 1)))
            * Real.exp (d * (1 + Real.log n)) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsigma) (le_of_lt (hPpos x hx))
        _ = Real.exp (d * (1 + Real.log n))
            * ∏ j ∈ Finset.range (n - 1), (x + ((j : ℝ) + 1)) := by ring
    have hbase_eq : (Real.exp 1 * (n : ℝ)) ^ d = Real.exp (d * (1 + Real.log n)) := by
      rw [Real.rpow_def_of_pos hbasepos]
      congr 1
      rw [Real.log_mul (ne_of_gt (Real.exp_pos 1)) (ne_of_gt hnpos), Real.log_exp]
      ring
    have hkey : ∏ j ∈ Finset.range (n - 1), (y + ((j : ℝ) + 1))
        ≤ (Real.exp 1 * (n : ℝ)) ^ d * ∏ j ∈ Finset.range (n - 1), (x + ((j : ℝ) + 1)) := by
      rw [hbase_eq]
      exact hper
    have hmul : (Real.exp 1 * (n : ℝ)) ^ x * ∏ j ∈ Finset.range (n - 1), (y + ((j : ℝ) + 1))
        ≤ (Real.exp 1 * (n : ℝ)) ^ y
          * ∏ j ∈ Finset.range (n - 1), (x + ((j : ℝ) + 1)) := by
      have h1 : (Real.exp 1 * (n : ℝ)) ^ x * ∏ j ∈ Finset.range (n - 1), (y + ((j : ℝ) + 1))
          ≤ (Real.exp 1 * (n : ℝ)) ^ x
            * ((Real.exp 1 * (n : ℝ)) ^ d
              * ∏ j ∈ Finset.range (n - 1), (x + ((j : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left hkey (le_of_lt (Real.rpow_pos_of_pos hbasepos x))
      have h2 : (Real.exp 1 * (n : ℝ)) ^ x
            * ((Real.exp 1 * (n : ℝ)) ^ d
              * ∏ j ∈ Finset.range (n - 1), (x + ((j : ℝ) + 1)))
          = (Real.exp 1 * (n : ℝ)) ^ y
            * ∏ j ∈ Finset.range (n - 1), (x + ((j : ℝ) + 1)) := by
        rw [← mul_assoc, ← Real.rpow_add hbasepos, hxy']
      exact h1.trans h2.le
    rw [hh_eq x hx, hh_eq y hy]
    have hdiff : 0 ≤ (Real.exp 1 * (n : ℝ)) ^ y / ∏ j ∈ Finset.range (n - 1), (y + ((j : ℝ) + 1))
        - (Real.exp 1 * (n : ℝ)) ^ x / ∏ j ∈ Finset.range (n - 1), (x + ((j : ℝ) + 1)) := by
      have hPy : (∏ j ∈ Finset.range (n - 1), (y + ((j : ℝ) + 1))) ≠ 0 := ne_of_gt (hPpos y hy)
      have hPx : (∏ j ∈ Finset.range (n - 1), (x + ((j : ℝ) + 1))) ≠ 0 := ne_of_gt (hPpos x hx)
      have hsp : (Real.exp 1 * (n : ℝ)) ^ y / ∏ j ∈ Finset.range (n - 1), (y + ((j : ℝ) + 1))
          - (Real.exp 1 * (n : ℝ)) ^ x / ∏ j ∈ Finset.range (n - 1), (x + ((j : ℝ) + 1))
          = ((Real.exp 1 * (n : ℝ)) ^ y * ∏ j ∈ Finset.range (n - 1), (x + ((j : ℝ) + 1))
              - (Real.exp 1 * (n : ℝ)) ^ x * ∏ j ∈ Finset.range (n - 1), (y + ((j : ℝ) + 1)))
            / ((∏ j ∈ Finset.range (n - 1), (y + ((j : ℝ) + 1)))
              * ∏ j ∈ Finset.range (n - 1), (x + ((j : ℝ) + 1))) := by
        field_simp
        try ring
      rw [hsp]
      apply div_nonneg
      · linarith
      · exact le_of_lt (mul_pos (hPpos y hy) (hPpos x hx))
    linarith
  have hb1 : IntegrableOn (fun a : ℝ => a ^ (t + beta - 1)) S := by
    have h := (intervalIntegral.integrableOn_Ioo_rpow_iff heps).mpr
      (show (-1 : ℝ) < t + beta - 1 by linarith)
    rwa [hS]
  have hb3 : IntegrableOn (fun a : ℝ => a ^ (s + (t + beta - 1))) S := by
    have h := (intervalIntegral.integrableOn_Ioo_rpow_iff heps).mpr
      (show (-1 : ℝ) < s + (t + beta - 1) by linarith)
    rwa [hS]
  have hw1le : ∀ a ∈ S, w1 a ≤ a ^ (t + beta - 1) := by
    intro a ha
    have hcoef : (Real.exp 1 * (n : ℝ)) ^ (-a) ≤ 1 := by
      have h := Real.rpow_le_rpow_of_nonpos (show (0 : ℝ) < 1 by norm_num)
        (le_of_lt hbase1) (show -a ≤ 0 by linarith [ha.1])
      simpa using h
    have hnn : 0 ≤ a ^ (t + beta - 1) := Real.rpow_nonneg (le_of_lt ha.1) _
    simp only [hw1]
    calc (Real.exp 1 * (n : ℝ)) ^ (-a) * a ^ (t + beta - 1)
        ≤ 1 * a ^ (t + beta - 1) := mul_le_mul_of_nonneg_right hcoef hnn
      _ = a ^ (t + beta - 1) := one_mul _
  have hcontR : Continuous fun a : ℝ => risingFac a n := by
    have hall : ∀ m : ℕ, Continuous fun a : ℝ => risingFac a m := by
      intro m
      induction m with
      | zero =>
        have h0 : (fun a : ℝ => risingFac a 0) = fun _ => (1 : ℝ) := by
          funext a
          simp [risingFac]
        rw [h0]
        exact continuous_const
      | succ k ih =>
        have hstep : (fun a : ℝ => risingFac a (k + 1))
            = fun a => risingFac a k * (a + (k : ℝ)) := by
          funext a
          simp only [risingFac, Finset.prod_range_succ]
        rw [hstep]
        exact ih.mul (continuous_id.add continuous_const)
    exact hall n
  have hw2le : ∀ a ∈ S, w2 a ≤ a ^ (t + beta - 1) := by
    intro a ha
    have ha0 : 0 < a := ha.1
    have hratio : a / risingFac a n = 1 / ∏ j ∈ Finset.range (n - 1), (a + ((j : ℝ) + 1)) :=
      (hfrest n hn1').2.2 a ha0
    have hprod1 : 1 ≤ ∏ j ∈ Finset.range (n - 1), (a + ((j : ℝ) + 1)) := by
      have h : ∏ j ∈ Finset.range (n - 1), (1 : ℝ)
          ≤ ∏ j ∈ Finset.range (n - 1), (a + ((j : ℝ) + 1)) := by
        apply Finset.prod_le_prod
        · intro i hi
          norm_num
        · intro i hi
          have hj : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
          linarith [ha0.le]
      simpa using h
    have hinv : 1 / (∏ j ∈ Finset.range (n - 1), (a + ((j : ℝ) + 1))) ≤ 1 := by
      have h := one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num) hprod1
      simpa using h
    have hT1' : a ^ (t + beta) = a ^ (t + beta - 1) * a := by
      rw [← Real.rpow_add_one (ne_of_gt ha0) (t + beta - 1)]
      ring_nf
    have hstep : w2 a
        = a ^ (t + beta - 1) * (1 / ∏ j ∈ Finset.range (n - 1), (a + ((j : ℝ) + 1))) := by
      simp only [hw2]
      rw [hT1', mul_div_assoc, hratio]
    rw [hstep]
    calc a ^ (t + beta - 1) * (1 / ∏ j ∈ Finset.range (n - 1), (a + ((j : ℝ) + 1)))
        ≤ a ^ (t + beta - 1) * 1 :=
          mul_le_mul_of_nonneg_left hinv (Real.rpow_nonneg (le_of_lt ha0) _)
      _ = a ^ (t + beta - 1) := mul_one _
  have hcontc : Continuous fun a : ℝ => (Real.exp 1 * (n : ℝ)) ^ (-a) := by
    have heq : (fun a : ℝ => (Real.exp 1 * (n : ℝ)) ^ (-a))
        = fun a => Real.exp (Real.log (Real.exp 1 * (n : ℝ)) * (-a)) := by
      funext a
      exact Real.rpow_def_of_pos hbasepos (-a)
    rw [heq]
    exact Real.continuous_exp.comp (continuous_const.mul continuous_neg)
  have hpowA : ContinuousOn (fun a : ℝ => a ^ (t + beta - 1)) S :=
    ContinuousOn.rpow_const continuous_id.continuousOn
      (fun x hx => Or.inr (by linarith : (0 : ℝ) ≤ t + beta - 1))
  have hpowS : ContinuousOn (fun a : ℝ => a ^ (s : ℝ)) S :=
    ContinuousOn.rpow_const continuous_id.continuousOn
      (fun x hx => Or.inr (by linarith : (0 : ℝ) ≤ (s : ℝ)))
  have hinvR : ContinuousOn (fun a : ℝ => (risingFac a n)⁻¹) S :=
    ContinuousOn.inv₀ hcontR.continuousOn (fun x hx => ne_of_gt (hRpos x hx))
  have hmeas_w1 : AEStronglyMeasurable w1 ((volume : Measure ℝ).restrict S) :=
    (hcontc.continuousOn.mul hpowA).aestronglyMeasurable hSmeas
  have hmeas_w2 : AEStronglyMeasurable w2 ((volume : Measure ℝ).restrict S) := by
    have hbase : AEStronglyMeasurable
        (fun a : ℝ => a ^ (t + beta - 1) * a * (risingFac a n)⁻¹)
        ((volume : Measure ℝ).restrict S) :=
      ((hpowA.mul continuous_id.continuousOn).mul hinvR).aestronglyMeasurable hSmeas
    refine hbase.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hSmeas] with a ha
    have hT1' : a ^ (t + beta) = a ^ (t + beta - 1) * a := by
      rw [← Real.rpow_add_one (ne_of_gt ha.1) (t + beta - 1)]
      ring_nf
    simp only [hw2]
    rw [hT1', div_eq_mul_inv]
  have hmeas_g : AEStronglyMeasurable g ((volume : Measure ℝ).restrict S) :=
    hpowS.aestronglyMeasurable hSmeas
  have hint1 : IntegrableOn w1 S := by
    refine MeasureTheory.Integrable.mono' hb1 hmeas_w1 ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hSmeas] with a ha
    rw [Real.norm_eq_abs, abs_of_nonneg (hw1nonneg a ha)]
    exact hw1le a ha
  have hint2 : IntegrableOn w2 S := by
    refine MeasureTheory.Integrable.mono' hb1 hmeas_w2 ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hSmeas] with a ha
    rw [Real.norm_eq_abs, abs_of_nonneg (hw2nonneg a ha)]
    exact hw2le a ha
  have hint3 : IntegrableOn (fun a => g a * w1 a) S := by
    refine MeasureTheory.Integrable.mono' hb3 (hmeas_g.mul hmeas_w1) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hSmeas] with a ha
    have hgle : g a = a ^ (s : ℝ) := by simp only [hg]
    have hnn : 0 ≤ g a * w1 a := by
      rw [hgle]
      exact mul_nonneg (Real.rpow_nonneg (le_of_lt ha.1) _) (hw1nonneg a ha)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    calc g a * w1 a ≤ a ^ (s : ℝ) * a ^ (t + beta - 1) := by
          rw [hgle]
          exact mul_le_mul_of_nonneg_left (hw1le a ha) (Real.rpow_nonneg (le_of_lt ha.1) _)
      _ = a ^ (s + (t + beta - 1)) := by rw [Real.rpow_add ha.1]
  have hint4 : IntegrableOn (fun a => g a * w2 a) S := by
    refine MeasureTheory.Integrable.mono' hb3 (hmeas_g.mul hmeas_w2) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hSmeas] with a ha
    have hgle : g a = a ^ (s : ℝ) := by simp only [hg]
    have hnn : 0 ≤ g a * w2 a := by
      rw [hgle]
      exact mul_nonneg (Real.rpow_nonneg (le_of_lt ha.1) _) (hw2nonneg a ha)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    calc g a * w2 a ≤ a ^ (s : ℝ) * a ^ (t + beta - 1) := by
          rw [hgle]
          exact mul_le_mul_of_nonneg_left (hw2le a ha) (Real.rpow_nonneg (le_of_lt ha.1) _)
      _ = a ^ (s + (t + beta - 1)) := by rw [Real.rpow_add ha.1]
  have hvol : 0 < (volume : Measure ℝ) S := by
    rw [hS, Real.volume_Ioo]
    simpa using ENNReal.ofReal_pos.mpr heps
  have hW1 : 0 < ∫ a in S, w1 a := by
    have hae : 0 ≤ᶠ[ae ((volume : Measure ℝ).restrict S)] w1 := by
      filter_upwards [MeasureTheory.ae_restrict_mem hSmeas] with a ha
      exact hw1nonneg a ha
    have hsupp : Function.support w1 ∩ S = S := by
      apply Set.Subset.antisymm
      · exact Set.inter_subset_right
      · intro a ha
        exact ⟨ne_of_gt (hw1pos a ha), ha⟩
    rw [MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae hae hint1, hsupp]
    exact hvol
  have hW2 : 0 < ∫ a in S, w2 a := by
    have hae : 0 ≤ᶠ[ae ((volume : Measure ℝ).restrict S)] w2 := by
      filter_upwards [MeasureTheory.ae_restrict_mem hSmeas] with a ha
      exact hw2nonneg a ha
    have hsupp : Function.support w2 ∩ S = S := by
      apply Set.Subset.antisymm
      · exact Set.inter_subset_right
      · intro a ha
        exact ⟨ne_of_gt (hw2pos a ha), ha⟩
    rw [MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae hae hint2, hsupp]
    exact hvol
  have hdouble : 0 ≤ ∫ x in S, ∫ y in S, (g x - g y) * (w2 x * w1 y - w2 y * w1 x) := by
    apply MeasureTheory.setIntegral_nonneg hSmeas
    intro x hx
    apply MeasureTheory.setIntegral_nonneg hSmeas
    intro y hy
    have hw1xy : 0 ≤ w1 x * w1 y := mul_nonneg (hw1nonneg x hx) (hw1nonneg y hy)
    rcases le_total x y with hxy | hyx
    · have hg' : g x - g y ≤ 0 := by
        have h := hgmono x hx y hy hxy
        linarith
      have hw' : w2 x * w1 y - w2 y * w1 x ≤ 0 := by
        rw [hrec x hx, hrec y hy]
        have hkey : hh x * w1 x * w1 y - hh y * w1 y * w1 x
            = (hh x - hh y) * (w1 x * w1 y) := by ring
        rw [hkey]
        have h := hhmono x hx y hy hxy
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hw1xy
      exact mul_nonneg_of_nonpos_of_nonpos hg' hw'
    · have hg' : 0 ≤ g x - g y := by
        have h := hgmono y hy x hx hyx
        linarith
      have hw' : 0 ≤ w2 x * w1 y - w2 y * w1 x := by
        rw [hrec x hx, hrec y hy]
        have hkey : hh x * w1 x * w1 y - hh y * w1 y * w1 x
            = (hh x - hh y) * (w1 x * w1 y) := by ring
        rw [hkey]
        have h := hhmono y hy x hx hyx
        exact mul_nonneg (by linarith) hw1xy
      exact mul_nonneg hg' hw'
  have hexpand : (∫ x in S, ∫ y in S, (g x - g y) * (w2 x * w1 y - w2 y * w1 x))
      = 2 * ((∫ a in S, g a * w2 a) * (∫ a in S, w1 a)
        - (∫ a in S, g a * w1 a) * (∫ a in S, w2 a)) := by
    have hinner : ∀ x : ℝ, (∫ y in S, (g x - g y) * (w2 x * w1 y - w2 y * w1 x))
        = ((∫ a in S, w1 a) * (g x * w2 x) - (∫ a in S, w2 a) * (g x * w1 x))
          - ((∫ a in S, g a * w1 a) * w2 x - (∫ a in S, g a * w2 a) * w1 x) := by
      intro x
      have e1 : IntegrableOn (fun y : ℝ => (g x * w2 x) * w1 y) S := hint1.const_mul _
      have e2 : IntegrableOn (fun y : ℝ => (g x * w1 x) * w2 y) S := hint2.const_mul _
      have e3 : IntegrableOn (fun y : ℝ => w2 x * (g y * w1 y)) S := hint3.const_mul _
      have e4 : IntegrableOn (fun y : ℝ => w1 x * (g y * w2 y)) S := hint4.const_mul _
      have e12 : IntegrableOn
          (fun y : ℝ => (g x * w2 x) * w1 y - (g x * w1 x) * w2 y) S := e1.sub e2
      have e34 : IntegrableOn
          (fun y : ℝ => w2 x * (g y * w1 y) - w1 x * (g y * w2 y)) S := e3.sub e4
      have congr1 : (∫ y in S, (g x - g y) * (w2 x * w1 y - w2 y * w1 x))
          = ∫ y in S, (((g x * w2 x) * w1 y - (g x * w1 x) * w2 y)
              - (w2 x * (g y * w1 y) - w1 x * (g y * w2 y))) := by
        apply MeasureTheory.setIntegral_congr_fun hSmeas
        intro y hy
        ring
      rw [congr1, MeasureTheory.integral_sub e12 e34, MeasureTheory.integral_sub e1 e2,
        MeasureTheory.integral_sub e3 e4, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul]
      ring
    simp only [hinner]
    have p1 : IntegrableOn (fun x : ℝ => (∫ a in S, w1 a) * (g x * w2 x)) S := hint4.const_mul _
    have p2 : IntegrableOn (fun x : ℝ => (∫ a in S, w2 a) * (g x * w1 x)) S := hint3.const_mul _
    have p3 : IntegrableOn (fun x : ℝ => (∫ a in S, g a * w1 a) * w2 x) S := hint2.const_mul _
    have p4 : IntegrableOn (fun x : ℝ => (∫ a in S, g a * w2 a) * w1 x) S := hint1.const_mul _
    have p12 : IntegrableOn
        (fun x : ℝ => (∫ a in S, w1 a) * (g x * w2 x) - (∫ a in S, w2 a) * (g x * w1 x)) S :=
      p1.sub p2
    have p34 : IntegrableOn
        (fun x : ℝ => (∫ a in S, g a * w1 a) * w2 x - (∫ a in S, g a * w2 a) * w1 x) S :=
      p3.sub p4
    rw [MeasureTheory.integral_sub p12 p34, MeasureTheory.integral_sub p1 p2,
      MeasureTheory.integral_sub p3 p4, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul]
    ring
  have hcross : (∫ a in S, g a * w1 a) * (∫ a in S, w2 a)
      ≤ (∫ a in S, g a * w2 a) * (∫ a in S, w1 a) := by
    nlinarith [hdouble, hexpand]
  have hnum1 : (∫ a in S, a ^ (s : ℝ) * w1 a) = ∫ a in S, g a * w1 a := by
    refine MeasureTheory.setIntegral_congr_fun hSmeas ?_
    intro a ha
    simp only [hg]
  have hnum2 : (∫ a in S, a ^ (t + (s : ℝ) + beta) / risingFac a n) = ∫ a in S, g a * w2 a := by
    refine MeasureTheory.setIntegral_congr_fun hSmeas ?_
    intro a ha
    exact (hA2 a ha).symm
  rw [hnum1, hnum2]
  have hd : 0 ≤ (∫ a in S, g a * w2 a) / (∫ a in S, w2 a)
      - (∫ a in S, g a * w1 a) / (∫ a in S, w1 a) := by
    have hsplit : (∫ a in S, g a * w2 a) / (∫ a in S, w2 a)
          - (∫ a in S, g a * w1 a) / (∫ a in S, w1 a)
        = ((∫ a in S, g a * w2 a) * (∫ a in S, w1 a)
            - (∫ a in S, g a * w1 a) * (∫ a in S, w2 a))
          / ((∫ a in S, w2 a) * (∫ a in S, w1 a)) := by
      field_simp
    rw [hsplit]
    apply div_nonneg
    · linarith
    · exact le_of_lt (mul_pos hW2 hW1)
  linarith
  /- @proof-region region.target-node.session.84bcf97541d850b6 end -/

end Statlib.Imported
end
end DPCompletedProof
