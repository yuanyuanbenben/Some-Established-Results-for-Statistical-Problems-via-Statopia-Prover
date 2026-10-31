import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.Vocabulary
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.Base
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.ProvedNodes.Node_1445702134_3c8d3810_8f7a15fe
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.ProvedNodes.Node_3224678180_5a630a9f_7124eef7
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.ProvedNodes.Node_3788355289_2a3e6b7e_b3f2870a



open MeasureTheory
open Statlib.Imported

noncomputable section
open MeasureTheory
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_3843288360_478d1772 : ∀ (t : ℝ) (ht : 1 ≤ t)
    (eps : ℝ) (h_eps_pos : 0 < eps) (h_eps_lt : eps < 1 / 2)
    (delta beta : ℝ) (h_delta : 0 < delta) (h_beta : 0 < beta)
    (prior : ℝ → ℝ) (hprior_meas : Measurable prior)
    (hprior_nonneg : ∀ a ∈ Set.Ioi (0 : ℝ), 0 ≤ prior a)
    (hprior_prob : ∫⁻ a in Set.Ioi (0 : ℝ), ENNReal.ofReal (prior a) = 1)
    (hA2 : ∀ a ∈ Set.Ioo (0 : ℝ) eps,
      delta⁻¹ * a ^ beta ≤ prior a ∧ prior a ≤ delta * a ^ beta)
    (K : ℝ) (hK : K = t + beta + 1) (n : ℕ) (hn : t + 1 ≤ (n : ℝ)),
    (delta * 2 ^ K * Real.exp 3)⁻¹ * (min eps (1 / Real.log (n : ℝ))) ^ K /
        ((n - 1).factorial : ℝ)
      ≤ ∫ a in Set.Ioo (0 : ℝ) eps, a ^ t / risingFac a n * prior a := by
  /- @proof-region region.target-node.session.40445d2214e58c1a begin -/
  intro t ht eps h_eps_pos h_eps_lt delta beta h_delta h_beta prior hprior_meas hprior_nonneg hprior_prob hA2 K hK n hn
  have ht0 : (0:ℝ) < t := by linarith
  have hn2 : (2:ℝ) ≤ (n:ℝ) := by linarith
  have hn2n : 2 ≤ n := by exact_mod_cast hn2
  have hn1n : 1 ≤ n := by omega
  have hnpos : (0:ℝ) < (n:ℝ) := by linarith
  have hLpos0 : 0 < Real.log (n:ℝ) := Real.log_pos (by linarith)
  have hfac : (0:ℝ) < ((n - 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (n - 1)
  set s : ℝ := t + beta with hsdef
  have hs1 : (1:ℝ) ≤ s := by rw [hsdef]; linarith
  have hs0 : (0:ℝ) < s := by linarith
  have hKs : K = s + 1 := by rw [hK, hsdef]
  set L : ℝ := Real.log (n:ℝ) with hLdef
  have hLpos : 0 < L := by rw [hLdef]; exact hLpos0
  set m : ℝ := min eps (1 / L) with hmdef
  have hm0 : 0 < m := by
    rw [hmdef]
    exact lt_min h_eps_pos (div_pos one_pos hLpos)
  have hm_eps : m ≤ eps := by rw [hmdef]; exact min_le_left _ _
  have hm_inv : m ≤ 1 / L := by rw [hmdef]; exact min_le_right _ _
  have hmL : m * L ≤ 1 := by
    have h1 : m * L ≤ (1 / L) * L := mul_le_mul_of_nonneg_right hm_inv (le_of_lt hLpos)
    have h2 : (1 / L) * L = 1 := by field_simp
    linarith
  have hm_half : m ≤ 1 / 2 := le_trans hm_eps (le_of_lt h_eps_lt)
  have hClaimC : ∀ m : ℕ, (∑ k ∈ Finset.range m, (1:ℝ)/((k:ℝ)+2)) ≤ Real.log ((m:ℝ)+1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ]
      rw [show ((↑(m + 1) : ℝ) + 1) = (↑m : ℝ) + 2 by push_cast; ring]
      have hstep : (1:ℝ)/((m:ℝ)+2) ≤ Real.log ((m:ℝ)+2) - Real.log ((m:ℝ)+1) := by
        have h1 : (0:ℝ) < (m:ℝ)+1 := by positivity
        have h2 : (0:ℝ) < (m:ℝ)+2 := by positivity
        have hle := Real.log_le_sub_one_of_pos (show (0:ℝ) < ((m:ℝ)+1)/((m:ℝ)+2) by positivity)
        rw [Real.log_div (ne_of_gt h1) (ne_of_gt h2)] at hle
        have heq : ((m:ℝ)+1)/((m:ℝ)+2) - 1 = -((1:ℝ)/((m:ℝ)+2)) := by field_simp; ring
        linarith
      linarith
  have hHarm : (∑ k ∈ Finset.range (n - 1), (1:ℝ)/((k:ℝ)+1)) ≤ 1 + Real.log (n:ℝ) := by
    have hsplit : (∑ k ∈ Finset.range (n - 1), (1:ℝ)/((k:ℝ)+1))
        = 1 + ∑ k ∈ Finset.range (n - 2), (1:ℝ)/((k:ℝ)+2) := by
      conv_lhs => rw [show n - 1 = (n - 2) + 1 from by omega]
      rw [Finset.sum_range_succ']
      have hbody : (∑ k ∈ Finset.range (n - 2), (1:ℝ)/(((k + 1 : ℕ) : ℝ)+1))
          = ∑ k ∈ Finset.range (n - 2), (1:ℝ)/((k:ℝ)+2) := by
        apply Finset.sum_congr rfl
        intro k hk
        push_cast
        ring
      rw [hbody]
      have hone : (1:ℝ)/(((0:ℕ):ℝ)+1) = 1 := by norm_num
      rw [hone]
      ring
    rw [hsplit]
    have h1 := hClaimC (n - 2)
    have hcast : ((↑(n - 2) : ℝ) + 1) = (n:ℝ) - 1 := by
      have h2 : ((n - 2 : ℕ) : ℝ) = (n:ℝ) - 2 := by
        rw [Nat.cast_sub (by omega : 2 ≤ n)]
        push_cast
        ring
      linarith
    rw [hcast] at h1
    have hlogmono : Real.log ((n:ℝ) - 1) ≤ Real.log (n:ℝ) := by
      apply Real.log_le_log
      · linarith
      · linarith
    linarith
  have hrise : ∀ a ∈ Set.Ioo (0:ℝ) eps,
      risingFac a n ≤ Real.exp 2 * a * (n:ℝ) ^ a * ((n - 1).factorial : ℝ) := by
    intro a ha
    obtain ⟨ha0, ha_eps⟩ := ha
    have ha1 : a ≤ 1 := by linarith
    have hstep : risingFac a n = a * ∏ k ∈ Finset.range (n - 1), (a + ((k:ℝ) + 1)) := by
      rw [risingFac]
      conv_lhs => rw [show n = (n - 1) + 1 from (Nat.sub_add_cancel hn1n).symm]
      rw [Finset.prod_range_succ']
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero]
      ring
    have hfacprod : (∏ k ∈ Finset.range (n - 1), ((k:ℝ) + 1)) = ((n - 1).factorial : ℝ) := by
      have h := Finset.prod_range_add_one_eq_factorial (n - 1)
      rw [← h, Nat.cast_prod]
      simp
    have hterm : ∀ k ∈ Finset.range (n - 1),
        a + ((k:ℝ) + 1) ≤ ((k:ℝ) + 1) * Real.exp (a / ((k:ℝ) + 1)) := by
      intro k hk
      have hk1 : (0:ℝ) < (k:ℝ) + 1 := by positivity
      have hexp := Real.add_one_le_exp (a / ((k:ℝ) + 1))
      have hmul := mul_le_mul_of_nonneg_left hexp (le_of_lt hk1)
      have heq : ((k:ℝ) + 1) * (a / ((k:ℝ) + 1) + 1) = a + ((k:ℝ) + 1) := by field_simp
      linarith
    have hprod1 : (∏ k ∈ Finset.range (n - 1), (a + ((k:ℝ) + 1)))
        ≤ ∏ k ∈ Finset.range (n - 1), (((k:ℝ) + 1) * Real.exp (a / ((k:ℝ) + 1))) :=
      Finset.prod_le_prod (fun k hk =>
        add_nonneg (le_of_lt ha0) (by positivity : (0:ℝ) ≤ (k:ℝ) + 1)) hterm
    have hprod2 : (∏ k ∈ Finset.range (n - 1), (((k:ℝ) + 1) * Real.exp (a / ((k:ℝ) + 1))))
        = ((n - 1).factorial : ℝ) *
            ∏ k ∈ Finset.range (n - 1), Real.exp (a / ((k:ℝ) + 1)) := by
      rw [Finset.prod_mul_distrib, hfacprod]
    have hprod3 : (∏ k ∈ Finset.range (n - 1), Real.exp (a / ((k:ℝ) + 1)))
        = Real.exp (∑ k ∈ Finset.range (n - 1), a / ((k:ℝ) + 1)) := by
      rw [Real.exp_sum]
    have hsum1 : (∑ k ∈ Finset.range (n - 1), a / ((k:ℝ) + 1))
        = a * ∑ k ∈ Finset.range (n - 1), (1:ℝ)/((k:ℝ) + 1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    have hsum : (∑ k ∈ Finset.range (n - 1), a / ((k:ℝ) + 1)) ≤ a * (1 + Real.log (n:ℝ)) := by
      rw [hsum1]
      exact mul_le_mul_of_nonneg_left hHarm (le_of_lt ha0)
    have hexp_bound : Real.exp (∑ k ∈ Finset.range (n - 1), a / ((k:ℝ) + 1))
        ≤ Real.exp (a * (1 + Real.log (n:ℝ))) := Real.exp_le_exp.mpr hsum
    have hexpval : Real.exp (a * (1 + Real.log (n:ℝ))) = Real.exp a * (n:ℝ) ^ a := by
      rw [Real.rpow_def_of_pos hnpos a, ← Real.exp_add]
      congr 1
      ring
    have hprodall : (∏ k ∈ Finset.range (n - 1), (a + ((k:ℝ) + 1)))
        ≤ Real.exp 1 * (n:ℝ) ^ a * ((n - 1).factorial : ℝ) := by
      have hfacnn : (0:ℝ) ≤ ((n - 1).factorial : ℝ) := le_of_lt hfac
      have hn1 : (0:ℝ) ≤ (n:ℝ) ^ a := le_of_lt (Real.rpow_pos_of_pos hnpos a)
      calc (∏ k ∈ Finset.range (n - 1), (a + ((k:ℝ) + 1)))
          ≤ ((n - 1).factorial : ℝ) *
              ∏ k ∈ Finset.range (n - 1), Real.exp (a / ((k:ℝ) + 1)) := by
            rw [← hprod2]
            exact hprod1
        _ = ((n - 1).factorial : ℝ) *
              Real.exp (∑ k ∈ Finset.range (n - 1), a / ((k:ℝ) + 1)) := by
            rw [hprod3]
        _ ≤ ((n - 1).factorial : ℝ) * Real.exp (a * (1 + Real.log (n:ℝ))) :=
            mul_le_mul_of_nonneg_left hexp_bound hfacnn
        _ = ((n - 1).factorial : ℝ) * (Real.exp a * (n:ℝ) ^ a) := by rw [hexpval]
        _ ≤ ((n - 1).factorial : ℝ) * (Real.exp 1 * (n:ℝ) ^ a) := by
            have hexpa : Real.exp a ≤ Real.exp 1 := Real.exp_le_exp.mpr ha1
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hexpa hn1) hfacnn
        _ = Real.exp 1 * (n:ℝ) ^ a * ((n - 1).factorial : ℝ) := by ring
    rw [hstep]
    have he : Real.exp 1 ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num)
    calc a * (∏ k ∈ Finset.range (n - 1), (a + ((k:ℝ) + 1)))
        ≤ a * (Real.exp 1 * (n:ℝ) ^ a * ((n - 1).factorial : ℝ)) :=
          mul_le_mul_of_nonneg_left hprodall (le_of_lt ha0)
      _ = Real.exp 1 * a * (n:ℝ) ^ a * ((n - 1).factorial : ℝ) := by ring
      _ ≤ Real.exp 2 * a * (n:ℝ) ^ a * ((n - 1).factorial : ℝ) := by
          have hn1 : (0:ℝ) ≤ (n:ℝ) ^ a := le_of_lt (Real.rpow_pos_of_pos hnpos a)
          have hfacnn : (0:ℝ) ≤ ((n - 1).factorial : ℝ) := le_of_lt hfac
          have ha' : (0:ℝ) ≤ a := le_of_lt ha0
          have h1 : Real.exp 1 * a ≤ Real.exp 2 * a := mul_le_mul_of_nonneg_right he ha'
          have h2 : Real.exp 1 * a * (n:ℝ) ^ a ≤ Real.exp 2 * a * (n:ℝ) ^ a :=
            mul_le_mul_of_nonneg_right h1 hn1
          exact mul_le_mul_of_nonneg_right h2 hfacnn
  have hpoint : ∀ a ∈ Set.Ioo (0:ℝ) eps,
      delta⁻¹ * (Real.exp 2)⁻¹ * ((n - 1).factorial : ℝ)⁻¹ * (a ^ (s - 1) * Real.exp (-(a * L)))
        ≤ a ^ t / risingFac a n * prior a := by
    intro a ha
    obtain ⟨ha0, ha_eps⟩ := ha
    have hane0 : a ≠ 0 := ne_of_gt ha0
    have hrFacts := statopia_math_node_1445702134_3c8d3810
    have hrFpos : (0:ℝ) < risingFac a n := hrFacts.1 a n ha0
    set big : ℝ := Real.exp 2 * a * (n:ℝ) ^ a * ((n - 1).factorial : ℝ) with hbigdef
    have hbigpos : (0:ℝ) < big := by
      rw [hbigdef]
      exact mul_pos (mul_pos (mul_pos (Real.exp_pos 2) ha0) (Real.rpow_pos_of_pos hnpos a)) hfac
    have hrFle : risingFac a n ≤ big := by
      rw [hbigdef]
      exact hrise a ⟨ha0, ha_eps⟩
    have ha_t : a ^ t = a ^ (t - 1) * a := by
      rw [show t = (t - 1) + ((1:ℕ) : ℝ) by push_cast; ring,
        Real.rpow_add_natCast hane0 (t - 1) 1]
      simp
    have ha_split : a ^ (s - 1) = a ^ (t - 1) * a ^ beta := by
      rw [hsdef]
      rw [show t + beta - 1 = (t - 1) + beta by ring, Real.rpow_add ha0 (t - 1) beta]
    have hpow_inv : ((n:ℝ) ^ a)⁻¹ = Real.exp (-(a * L)) := by
      have h1 : (n:ℝ) ^ a = Real.exp (Real.log (n:ℝ) * a) := Real.rpow_def_of_pos hnpos a
      rw [h1, ← Real.exp_neg, hLdef]
      congr 1
      ring
    have hkey : (a ^ t / big) * (delta⁻¹ * a ^ beta)
        = delta⁻¹ * (Real.exp 2)⁻¹ * ((n - 1).factorial : ℝ)⁻¹ *
            (a ^ (s - 1) * Real.exp (-(a * L))) := by
      rw [ha_split, ha_t, ← hpow_inv, hbigdef]
      field_simp
    have hAt : (0:ℝ) ≤ a ^ t := le_of_lt (Real.rpow_pos_of_pos ha0 t)
    have hstep1 : a ^ t / big ≤ a ^ t / risingFac a n := by
      gcongr
    have hDb : (0:ℝ) ≤ delta⁻¹ * a ^ beta := by
      have h1 : (0:ℝ) < a ^ beta := Real.rpow_pos_of_pos ha0 beta
      have h2 : (0:ℝ) < delta⁻¹ := inv_pos.mpr h_delta
      exact mul_nonneg (le_of_lt h2) (le_of_lt h1)
    have hstep2 : (a ^ t / big) * (delta⁻¹ * a ^ beta) ≤ (a ^ t / risingFac a n) * (delta⁻¹ * a ^ beta) :=
      mul_le_mul_of_nonneg_right hstep1 hDb
    have hstep3 : (a ^ t / risingFac a n) * (delta⁻¹ * a ^ beta) ≤ (a ^ t / risingFac a n) * prior a := by
      have h3 : (0:ℝ) ≤ a ^ t / risingFac a n := div_nonneg hAt (le_of_lt hrFpos)
      exact mul_le_mul_of_nonneg_left (hA2 a ⟨ha0, ha_eps⟩).1 h3
    calc delta⁻¹ * (Real.exp 2)⁻¹ * ((n - 1).factorial : ℝ)⁻¹ *
            (a ^ (s - 1) * Real.exp (-(a * L)))
        = (a ^ t / big) * (delta⁻¹ * a ^ beta) := hkey.symm
      _ ≤ (a ^ t / risingFac a n) * (delta⁻¹ * a ^ beta) := hstep2
      _ ≤ (a ^ t / risingFac a n) * prior a := hstep3
  have hInt : delta⁻¹ * (Real.exp 3)⁻¹ * ((n - 1).factorial : ℝ)⁻¹ * (m ^ s / s)
      ≤ ∫ a in Set.Ioo (0:ℝ) eps, a ^ t / risingFac a n * prior a := by
    have hFint : IntegrableOn (fun a : ℝ => a ^ t / risingFac a n * prior a) (Set.Ioo (0:ℝ) eps) :=
      (statopia_math_node_3788355289_2a3e6b7e t ht prior hprior_meas hprior_nonneg hprior_prob eps delta
        beta h_eps_pos h_delta h_beta hA2 n 1 le_rfl (by push_cast; linarith)).2.2.1
    have hmono : ∫ a in Set.Ioo (0:ℝ) eps, (delta⁻¹ * (Real.exp 2)⁻¹ * ((n - 1).factorial : ℝ)⁻¹) *
          (a ^ (s - 1) * Real.exp (-(a * L)))
        ≤ ∫ a in Set.Ioo (0:ℝ) eps, a ^ t / risingFac a n * prior a := by
      have hCptpos : (0:ℝ) < delta⁻¹ * (Real.exp 2)⁻¹ * ((n - 1).factorial : ℝ)⁻¹ := by positivity
      have hnn : (fun _ : ℝ => (0:ℝ)) ≤ᶠ[ae (volume.restrict (Set.Ioo (0:ℝ) eps))] (fun a =>
          (delta⁻¹ * (Real.exp 2)⁻¹ * ((n - 1).factorial : ℝ)⁻¹) *
            (a ^ (s - 1) * Real.exp (-(a * L)))) := by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with a ha
        exact mul_nonneg (le_of_lt hCptpos)
          (mul_nonneg (le_of_lt (Real.rpow_pos_of_pos ha.1 (s - 1))) (le_of_lt (Real.exp_pos _)))
      have hle : (fun a => (delta⁻¹ * (Real.exp 2)⁻¹ * ((n - 1).factorial : ℝ)⁻¹) *
            (a ^ (s - 1) * Real.exp (-(a * L))))
          ≤ᶠ[ae (volume.restrict (Set.Ioo (0:ℝ) eps))] (fun a => a ^ t / risingFac a n * prior a) := by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with a ha
        exact hpoint a ha
      exact MeasureTheory.integral_mono_of_nonneg hnn hFint hle
    have hae : Set.Ioo (0:ℝ) eps =ᵐ[volume] Set.Ioc (0:ℝ) eps := by
      have hz : volume ({eps} : Set ℝ) = 0 := by simp
      have hne : ∀ᵐ x : ℝ ∂volume, x ≠ eps := by
        rw [MeasureTheory.ae_iff]
        simpa using hz
      filter_upwards [hne] with x hx
      exact propext ⟨fun h => ⟨h.1, le_of_lt h.2⟩, fun h => ⟨h.1, lt_of_le_of_ne h.2 hx⟩⟩
    have hbridge : ∫ a in Set.Ioo (0:ℝ) eps, (a ^ (s - 1) * Real.exp (-(a * L)))
        = ∫ a in (0:ℝ)..eps, (a ^ (s - 1) * Real.exp (-(a * L))) := by
      rw [intervalIntegral.integral_of_le (le_of_lt h_eps_pos),
        MeasureTheory.Measure.restrict_congr_set hae]
    have hcomp : L * ∫ x in (0:ℝ)..eps, ((L * x) ^ (s - 1) * Real.exp (-(L * x)))
        = lowerGamma s (eps * L) := by
      have h := intervalIntegral.mul_integral_comp_mul_left
        (a := (0:ℝ)) (b := eps) (f := fun y : ℝ => y ^ (s - 1) * Real.exp (-y)) L
      rw [mul_zero, show L * eps = eps * L by ring] at h
      exact h
    have hcongr : ∫ x in (0:ℝ)..eps, ((L * x) ^ (s - 1) * Real.exp (-(L * x)))
        = ∫ x in (0:ℝ)..eps, (L ^ (s - 1) * (x ^ (s - 1) * Real.exp (-(x * L)))) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le (le_of_lt h_eps_pos)] at hx
      show (L * x) ^ (s - 1) * Real.exp (-(L * x))
          = L ^ (s - 1) * (x ^ (s - 1) * Real.exp (-(x * L)))
      rw [Real.mul_rpow (le_of_lt hLpos) hx.1, show -(L * x) = -(x * L) by ring]
      ring
    have hcore : (Real.exp 1)⁻¹ * (m ^ s / s) ≤ L ^ (-s) * lowerGamma s (eps * L) := by
      have hLs : (0:ℝ) < L ^ s := Real.rpow_pos_of_pos hLpos s
      have hmain : m ^ s * L ^ s ≤ Real.exp 1 * s * lowerGamma s (eps * L) := by
        by_cases hge : 1 ≤ eps * L
        · have h1L : 1 / L ≤ eps := by
            rw [one_div, show eps = (eps * L) * L⁻¹ by field_simp]
            simpa using mul_le_mul_of_nonneg_right hge (le_of_lt (inv_pos.mpr hLpos))
          have hm_eq : m = 1 / L := by
            rw [hmdef]
            exact min_eq_right h1L
          have hγ : Real.exp (-1) / s ≤ lowerGamma s (eps * L) :=
            (statopia_math_node_3224678180_5a630a9f).2.2.2.1 s (eps * L) hs0 hge
          have hLmul : (1 / L) ^ s * L ^ s = 1 := by
            rw [← Real.mul_rpow (le_of_lt (div_pos one_pos hLpos)) (le_of_lt hLpos)]
            have h1 : (1 / L) * L = 1 := by field_simp
            rw [h1]
            simp
          rw [hm_eq, hLmul]
          have h1 : Real.exp (-1) ≤ s * lowerGamma s (eps * L) := by
            have h2 := mul_le_mul_of_nonneg_right hγ (le_of_lt hs0)
            have h3 : Real.exp (-1) / s * s = Real.exp (-1) := by field_simp
            rw [h3] at h2
            linarith [h2, mul_comm (lowerGamma s (eps * L)) s]
          have h5 : Real.exp 1 * Real.exp (-1) = 1 := by
            rw [← Real.exp_add]; norm_num
          have h8 := mul_le_mul_of_nonneg_left h1 (le_of_lt (Real.exp_pos 1))
          rw [h5] at h8
          nlinarith [h8]
        · push_neg at hge
          have hle1 : eps ≤ 1 / L := by
            rw [one_div, show eps = (eps * L) * L⁻¹ by field_simp]
            simpa using mul_le_mul_of_nonneg_right (le_of_lt hge) (le_of_lt (inv_pos.mpr hLpos))
          have hm_eq : m = eps := by
            rw [hmdef]
            exact min_eq_left hle1
          have hγ : Real.exp (-(eps * L)) * (eps * L) ^ s / s ≤ lowerGamma s (eps * L) :=
            (statopia_math_node_3224678180_5a630a9f).2.2.1 s (eps * L) hs0 (by positivity)
          have hexp1 : Real.exp (-1) ≤ Real.exp (-(eps * L)) := by
            apply Real.exp_le_exp.mpr
            linarith
          have hstep : Real.exp (-1) * (eps * L) ^ s / s
              ≤ Real.exp (-(eps * L)) * (eps * L) ^ s / s := by
            gcongr
          have hγ' : Real.exp (-1) * (eps * L) ^ s / s ≤ lowerGamma s (eps * L) := le_trans hstep hγ
          have h1 : Real.exp (-1) * (eps * L) ^ s ≤ s * lowerGamma s (eps * L) := by
            have h2 := mul_le_mul_of_nonneg_right hγ' (le_of_lt hs0)
            have h3 : (Real.exp (-1) * (eps * L) ^ s / s) * s = Real.exp (-1) * (eps * L) ^ s := by
              field_simp
            rw [h3] at h2
            linarith [h2, mul_comm (lowerGamma s (eps * L)) s]
          have h6 : (eps * L) ^ s = eps ^ s * L ^ s :=
            Real.mul_rpow (le_of_lt h_eps_pos) (le_of_lt hLpos)
          rw [h6] at h1
          rw [hm_eq]
          have h5 : Real.exp 1 * Real.exp (-1) = 1 := by
            rw [← Real.exp_add]; norm_num
          have h8 := mul_le_mul_of_nonneg_left h1 (le_of_lt (Real.exp_pos 1))
          have h10 : Real.exp 1 * (Real.exp (-1) * (eps ^ s * L ^ s)) = eps ^ s * L ^ s := by
            rw [← mul_assoc, h5, one_mul]
          have h11 : Real.exp 1 * (s * lowerGamma s (eps * L))
              = Real.exp 1 * s * lowerGamma s (eps * L) := by ring
          rw [h10, h11] at h8
          exact h8
      have hLsne : L ^ s ≠ 0 := ne_of_gt hLs
      have hexpne : Real.exp 1 ≠ 0 := ne_of_gt (Real.exp_pos 1)
      have hsne : s ≠ 0 := ne_of_gt hs0
      have hnn2 : (0:ℝ) ≤ (Real.exp 1 * s * L ^ s)⁻¹ :=
        le_of_lt (inv_pos.mpr (mul_pos (mul_pos (Real.exp_pos 1) hs0) hLs))
      calc (Real.exp 1)⁻¹ * (m ^ s / s)
          = (m ^ s * L ^ s) * (Real.exp 1 * s * L ^ s)⁻¹ := by
            field_simp
        _ ≤ (Real.exp 1 * s * lowerGamma s (eps * L)) * (Real.exp 1 * s * L ^ s)⁻¹ :=
            mul_le_mul_of_nonneg_right hmain hnn2
        _ = L ^ (-s) * lowerGamma s (eps * L) := by
            rw [Real.rpow_neg (le_of_lt hLpos)]
            field_simp
    have hI : ∫ x in (0:ℝ)..eps, (x ^ (s - 1) * Real.exp (-(x * L)))
        = L ^ (-s) * lowerGamma s (eps * L) := by
      have hLinv : L ^ (-s) * L ^ s = 1 := by
        rw [Real.rpow_neg (le_of_lt hLpos)]
        field_simp
      have hLpow : L * L ^ (s - 1) = L ^ s := by
        conv_rhs => rw [show s = (s - 1) + ((1:ℕ) : ℝ) by push_cast; ring]
        rw [Real.rpow_add_natCast (ne_of_gt hLpos) (s - 1) 1, pow_one, mul_comm]
      have hpull : ∫ x in (0:ℝ)..eps, L ^ (s - 1) * (x ^ (s - 1) * Real.exp (-(x * L)))
          = L ^ (s - 1) * ∫ x in (0:ℝ)..eps, (x ^ (s - 1) * Real.exp (-(x * L))) := by
        have h1 : ∫ x in (0:ℝ)..eps, L ^ (s - 1) * (x ^ (s - 1) * Real.exp (-(x * L)))
            = ∫ x in Set.Ioc (0:ℝ) eps, L ^ (s - 1) * (x ^ (s - 1) * Real.exp (-(x * L))) :=
          intervalIntegral.integral_of_le (le_of_lt h_eps_pos)
        have h2 : ∫ x in Set.Ioc (0:ℝ) eps, L ^ (s - 1) * (x ^ (s - 1) * Real.exp (-(x * L)))
            = L ^ (s - 1) * ∫ x in Set.Ioc (0:ℝ) eps, (x ^ (s - 1) * Real.exp (-(x * L))) := by
          rw [MeasureTheory.integral_const_mul]
        have h3 : L ^ (s - 1) * ∫ x in Set.Ioc (0:ℝ) eps, (x ^ (s - 1) * Real.exp (-(x * L)))
            = L ^ (s - 1) * ∫ x in (0:ℝ)..eps, (x ^ (s - 1) * Real.exp (-(x * L))) := by
          rw [intervalIntegral.integral_of_le (le_of_lt h_eps_pos)]
        exact h1.trans (h2.trans h3)
      have hLG : lowerGamma s (eps * L)
          = L ^ s * ∫ x in (0:ℝ)..eps, (x ^ (s - 1) * Real.exp (-(x * L))) := by
        rw [← hcomp, hcongr, hpull, ← mul_assoc, hLpow]
      rw [hLG, ← mul_assoc, hLinv, one_mul]
    have hval : ∫ a in Set.Ioo (0:ℝ) eps, ((delta⁻¹ * (Real.exp 2)⁻¹ * ((n - 1).factorial : ℝ)⁻¹) *
          (a ^ (s - 1) * Real.exp (-(a * L))))
        = (delta⁻¹ * (Real.exp 2)⁻¹ * ((n - 1).factorial : ℝ)⁻¹) *
            (L ^ (-s) * lowerGamma s (eps * L)) := by
      rw [MeasureTheory.integral_const_mul, hbridge, hI]
    have hexp3 : (Real.exp 3)⁻¹ = (Real.exp 2)⁻¹ * (Real.exp 1)⁻¹ := by
      calc (Real.exp 3)⁻¹ = Real.exp (-3) := by rw [Real.exp_neg]
        _ = Real.exp ((-2) + (-1)) := by norm_num
        _ = Real.exp (-2) * Real.exp (-1) := Real.exp_add _ _
        _ = (Real.exp 2)⁻¹ * (Real.exp 1)⁻¹ := by rw [Real.exp_neg, Real.exp_neg]
    have hCptnn : (0:ℝ) ≤ delta⁻¹ * (Real.exp 2)⁻¹ * ((n - 1).factorial : ℝ)⁻¹ := by positivity
    calc delta⁻¹ * (Real.exp 3)⁻¹ * ((n - 1).factorial : ℝ)⁻¹ * (m ^ s / s)
        = (delta⁻¹ * (Real.exp 2)⁻¹ * ((n - 1).factorial : ℝ)⁻¹) * (Real.exp 1)⁻¹ * (m ^ s / s) := by
          rw [hexp3]
          ring
      _ = (delta⁻¹ * (Real.exp 2)⁻¹ * ((n - 1).factorial : ℝ)⁻¹) *
            ((Real.exp 1)⁻¹ * (m ^ s / s)) := by ring
      _ ≤ (delta⁻¹ * (Real.exp 2)⁻¹ * ((n - 1).factorial : ℝ)⁻¹) *
            (L ^ (-s) * lowerGamma s (eps * L)) := mul_le_mul_of_nonneg_left hcore hCptnn
      _ = ∫ a in Set.Ioo (0:ℝ) eps, (delta⁻¹ * (Real.exp 2)⁻¹ * ((n - 1).factorial : ℝ)⁻¹) *
            (a ^ (s - 1) * Real.exp (-(a * L))) := hval.symm
      _ ≤ ∫ a in Set.Ioo (0:ℝ) eps, a ^ t / risingFac a n * prior a := hmono
  have hfinal : (delta * 2 ^ K * Real.exp 3)⁻¹ * m ^ K / ((n - 1).factorial : ℝ)
      ≤ delta⁻¹ * (Real.exp 3)⁻¹ * ((n - 1).factorial : ℝ)⁻¹ * (m ^ s / s) := by
    have hKpos : (0:ℝ) ≤ K := by rw [hKs]; linarith
    have hlog2a : (1/2 : ℝ) ≤ Real.log 2 := by
      have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1/2 by norm_num)
      rw [Real.log_div one_ne_zero (by norm_num : (2:ℝ) ≠ 0), Real.log_one] at h
      linarith
    have hK_lb : (K - 1) / 2 ≤ 2 ^ K := by
      have h1 : Real.log 2 * K + 1 ≤ (2:ℝ) ^ K := by
        rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2) K]
        exact Real.add_one_le_exp _
      have hmul : (1/2) * K ≤ Real.log 2 * K := mul_le_mul_of_nonneg_right hlog2a hKpos
      linarith
    have hkey2 : s * m ≤ 2 ^ K := by
      have h1 : s * m ≤ s * (1 / 2) := mul_le_mul_of_nonneg_left hm_half (le_of_lt hs0)
      have h2 : s * (1 / 2) = (K - 1) / 2 := by rw [hKs]; ring
      linarith [hK_lb, h2]
    have hmK : m ^ K = m ^ s * m := by
      rw [hKs, show s + 1 = s + ((1:ℕ) : ℝ) by push_cast; ring,
        Real.rpow_add_natCast (ne_of_gt hm0) s 1]
      simp
    have hKM : (0:ℝ) < 2 ^ K := Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) K
    have hMs : (0:ℝ) < m ^ s := Real.rpow_pos_of_pos hm0 s
    have hcore' : m ^ K * s ≤ m ^ s * 2 ^ K := by
      rw [hmK]
      calc m ^ s * m * s = m ^ s * (s * m) := by ring
        _ ≤ m ^ s * 2 ^ K := mul_le_mul_of_nonneg_left hkey2 (le_of_lt hMs)
    have hcore : m ^ K / 2 ^ K ≤ m ^ s / s := by
      have hKM' : (2:ℝ) ^ K ≠ 0 := ne_of_gt hKM
      have hden : (0:ℝ) ≤ 2 ^ K * s := le_of_lt (mul_pos hKM hs0)
      have step1 : m ^ K * s / (2 ^ K * s) ≤ m ^ s * 2 ^ K / (2 ^ K * s) :=
        div_le_div_of_nonneg_right hcore' hden
      have hlhs : m ^ K * s / (2 ^ K * s) = m ^ K / 2 ^ K := by field_simp
      have hrhs : m ^ s * 2 ^ K / (2 ^ K * s) = m ^ s / s := by field_simp
      rw [hlhs, hrhs] at step1
      exact step1
    have hCnn : (0:ℝ) ≤ delta⁻¹ * (Real.exp 3)⁻¹ * ((n - 1).factorial : ℝ)⁻¹ :=
      le_of_lt (mul_pos (mul_pos (inv_pos.mpr h_delta) (inv_pos.mpr (Real.exp_pos 3)))
        (inv_pos.mpr hfac))
    have e1 : (delta * 2 ^ K * Real.exp 3)⁻¹ * m ^ K / ((n - 1).factorial : ℝ)
        = (delta⁻¹ * (Real.exp 3)⁻¹ * ((n - 1).factorial : ℝ)⁻¹) * (m ^ K / 2 ^ K) := by
      field_simp
    have e2 : delta⁻¹ * (Real.exp 3)⁻¹ * ((n - 1).factorial : ℝ)⁻¹ * (m ^ s / s)
        = (delta⁻¹ * (Real.exp 3)⁻¹ * ((n - 1).factorial : ℝ)⁻¹) * (m ^ s / s) := by
      ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left hcore hCnn
  exact hfinal.trans hInt
  /- @proof-region region.target-node.session.40445d2214e58c1a end -/

end Statlib.Imported
end
