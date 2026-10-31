import Statlib.StatFoundation.BasicAnalysis.ENNRealBridge
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.Vocabulary
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.Base
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.ProvedNodes.Node_1445702134_3c8d3810_8f7a15fe
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.ProvedNodes.Node_1492827739_6836739b_286d07d8
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.ProvedNodes.Node_1797268609_53e08000_06dbe633
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.ProvedNodes.Node_243881079_7797ad4a_b3d6966c
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.ProvedNodes.Node_3224678180_5a630a9f_7124eef7
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.ProvedNodes.Node_3781072913_5c5702c4_631a21aa
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.ProvedNodes.Node_3788355289_2a3e6b7e_b3f2870a
open MeasureTheory
open Statlib.Imported

set_option maxHeartbeats 1000000
noncomputable section
open MeasureTheory
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_3249584082_2b6786bc : ∀ (t : ℝ) (ht : 1 ≤ t)
    (π : ℝ → ℝ) (hpi_meas : Measurable π)
    (hpi_nonneg : ∀ α ∈ Set.Ioi (0 : ℝ), 0 ≤ π α)
    (hpi_prob : ∫⁻ α in Set.Ioi (0 : ℝ), ENNReal.ofReal (π α) = 1)
    (delta beta eps0 eps : ℝ) (hdelta : 0 < delta) (hbeta : 0 < beta)
    (heps0 : 0 < eps0) (heps : 0 < eps) (heps_lt : eps < 1 / 2) (heps_le : eps ≤ eps0)
    (hA2 : ∀ α ∈ Set.Ioo (0 : ℝ) eps0, delta⁻¹ * α ^ beta ≤ π α ∧ π α ≤ delta * α ^ beta)
    (hB1 : delta * eps ^ (beta + 1) / (beta + 1) ≤ 1 / 2)
    (n s : ℕ) (hs : 1 ≤ s) (hns : (s : ℝ) + t ≤ (n : ℝ))
    (hfin : priorMoment π (t + (s : ℝ) - 1) ≠ ⊤),
    (∫ α in Set.Ioi eps, α ^ (t + (s : ℝ)) / risingFac α n * π α)
      ≤ Gconst t eps delta beta * (s : ℝ) / eps ^ s *
            (priorMoment π (t + (s : ℝ) - 1)).toReal *
            (lowerGamma (t + (s : ℝ) + beta) (eps * Real.log (n : ℝ)) /
              (Real.log ((n : ℝ) / (1 + eps))) ^ s) *
            (∫ α in Set.Ioi eps, α ^ t / risingFac α n * π α)
        + (3 / 4) * (Gconst t eps delta beta * (s : ℝ) / eps ^ s *
            (priorMoment π (t + (s : ℝ) - 1)).toReal *
            (lowerGamma (t + (s : ℝ) + beta) (eps * Real.log (n : ℝ)) /
              (Real.log ((n : ℝ) / (1 + eps))) ^ s)) *
            (∫ α in Set.Ioo 0 eps, α ^ t / risingFac α n * π α) := by
  /- @proof-region region.target-node.session.f4d5709a50e464da begin -/
  set_option maxHeartbeats 4000000 in
  exact (by
    have reverse_chebyshev_density {X : Type} [MeasurableSpace X]
        (μ : Measure X) (p f q : X → ℝ)
        (hp : Integrable p μ)
        (hf : Integrable (fun x => f x * p x) μ)
        (hq : Integrable (fun x => q x * p x) μ)
        (hfq : Integrable (fun x => f x * q x * p x) μ)
        (hp0 : ∀ᵐ x ∂μ, 0 ≤ p x)
        (hanti : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, (f x - f y) * (q x - q y) ≤ 0) :
        (∫ x, p x ∂μ) * (∫ x, f x * q x * p x ∂μ) ≤
          (∫ x, f x * p x ∂μ) * (∫ x, q x * p x ∂μ) := by
      have hx : ∀ᵐ x ∂μ,
          f x * q x * (∫ y, p y ∂μ) + (∫ y, f y * q y * p y ∂μ) ≤
          f x * (∫ y, q y * p y ∂μ) + q x * (∫ y, f y * p y ∂μ) := by
        filter_upwards [hanti] with x hx
        have hi := integral_mono_ae
          ((hp.const_mul (f x * q x)).add hfq)
          ((hq.const_mul (f x)).add (hf.const_mul (q x))) ?_
        · simpa only [Pi.add_apply, integral_add (hp.const_mul (f x * q x)) hfq,
          integral_add (hq.const_mul (f x)) (hf.const_mul (q x)), integral_const_mul] using hi
        · filter_upwards [hx, hp0] with y hy hpy
          dsimp only [Pi.add_apply]
          nlinarith [mul_nonpos_of_nonpos_of_nonneg hy hpy]
      have hh := integral_mono_ae
        (((hfq.mul_const (∫ y, p y ∂μ))).add
          (hp.const_mul (∫ y, f y * q y * p y ∂μ)))
        (((hf.mul_const (∫ y, q y * p y ∂μ))).add
          ((hq.mul_const (∫ y, f y * p y ∂μ)))) ?_
      · simp only [Pi.add_apply] at hh
        rw [integral_add (hfq.mul_const _) (hp.const_mul _),
          integral_add (hf.mul_const _) (hq.mul_const _)] at hh
        simp only [integral_const_mul, integral_mul_const] at hh
        nlinarith
      · filter_upwards [hx, hp0] with x hx hpx
        dsimp only [Pi.add_apply]
        nlinarith [mul_le_mul_of_nonneg_right hx hpx]
    
    
    have tail_bounds (t ε : ℝ) (s n : ℕ) (π : ℝ → ℝ)
        (ht : 1 ≤ t) (hs : 1 ≤ s) (hn : 1 ≤ n) (hε : 0 < ε)
        (hπmeas : Measurable π)
        (hπnonneg : ∀ a ∈ Set.Ioi (0 : ℝ), 0 ≤ π a)
        (hπint : IntegrableOn π (Set.Ioi (0 : ℝ)))
        (hmass : 1 / 2 ≤ ∫ a in Set.Ioi ε, π a)
        (hEfinite : priorMoment π (t + (s : ℝ) - 1) ≠ ⊤) :
        (∫ a in Set.Ioi ε, a ^ (t + (s : ℝ)) / risingFac a n * π a) ≤
          (priorMoment π (t + (s : ℝ) - 1)).toReal * (ε / risingFac ε n) ∧
        (∫ a in Set.Ioi ε, a ^ (t + (s : ℝ)) / risingFac a n * π a) ≤
          2 * (priorMoment π (t + (s : ℝ) - 1)).toReal * ε ^ (1 - t) *
            (∫ a in Set.Ioi ε, a ^ t / risingFac a n * π a) := by
      let r : ℝ := t + (s : ℝ) - 1
      let q : ℝ → ℝ := fun a => a / risingFac a n
      let f : ℝ → ℝ := fun a => a ^ r
      let μ : Measure ℝ := volume.restrict (Set.Ioi ε)
      have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
      have hr : 0 ≤ r := by dsimp [r]; linarith
      have hs0 : Set.Ioi ε ⊆ Set.Ioi (0 : ℝ) := fun a ha => lt_trans hε ha
      have hp : Integrable π μ := hπint.mono_set hs0
      have hp0 : ∀ᵐ a ∂μ, 0 ≤ π a := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
        exact hπnonneg a (hs0 ha)
      have hpos := statopia_math_node_1445702134_3c8d3810.1
      have hqfacts := statopia_math_node_1445702134_3c8d3810.2.2.2.2.2.2 n hn
      have hqpos : ∀ a ∈ Set.Ioi (0 : ℝ), 0 < q a := hqfacts.1
      have hqanti : AntitoneOn q (Set.Ioi (0 : ℝ)) := hqfacts.2.1
      have hqeps : 0 < q ε := hqpos ε hε
      have hqbound : ∀ a ∈ Set.Ioi ε, q a ≤ q ε :=
        fun a ha => hqanti hε (hs0 ha) ha.le
      have hmmeas : AEStronglyMeasurable (fun a => f a * π a)
          (volume.restrict (Set.Ioi (0 : ℝ))) := by
        exact ((measurable_id.pow_const r).aestronglyMeasurable).mul hπmeas.aestronglyMeasurable
      have hm0 : ∀ᵐ a ∂volume.restrict (Set.Ioi (0 : ℝ)), 0 ≤ f a * π a := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
        exact mul_nonneg (Real.rpow_nonneg ha.le _) (hπnonneg a ha)
      have hEint : IntegrableOn (fun a => f a * π a) (Set.Ioi (0 : ℝ)) := by
        apply (lintegral_ofReal_ne_top_iff_integrable hmmeas hm0).mp
        exact hEfinite
      have hEeq : (∫ a in Set.Ioi (0 : ℝ), f a * π a) =
          (priorMoment π r).toReal := by
        exact (Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.lintegral_toReal_eq_integral_of_nonneg hm0 hEint).symm
      have hf : Integrable (fun a => f a * π a) μ := hEint.mono_set hs0
      have hqmeas : AEStronglyMeasurable (fun a => q a * π a) μ := by
        have hcont : ContinuousOn q (Set.Ioi ε) := by
          apply continuous_id.continuousOn.div
          · exact (show Continuous (fun a : ℝ => risingFac a n) by
              unfold risingFac; fun_prop).continuousOn
          · exact fun a ha => (hpos a n (hs0 ha)).ne'
        exact (hcont.aestronglyMeasurable measurableSet_Ioi).mul hπmeas.aestronglyMeasurable
      have hq : Integrable (fun a => q a * π a) μ := by
        apply (hp.const_mul (q ε)).mono' hqmeas
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hqpos a (hs0 ha)).le (hπnonneg a (hs0 ha)))]
        exact mul_le_mul_of_nonneg_right (hqbound a ha) (hπnonneg a (hs0 ha))
      have hfq : Integrable (fun a => f a * q a * π a) μ := by
        apply (hf.mul_const (q ε)).mono'
          (by simpa only [Pi.mul_apply, mul_assoc] using
            ((measurable_id.pow_const r).aestronglyMeasurable.mul hqmeas))
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
        have hfa : 0 ≤ f a := Real.rpow_nonneg (hs0 ha).le _
        have hpa := hπnonneg a (hs0 ha)
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg hfa (hqpos a (hs0 ha)).le) hpa)]
        nlinarith [mul_le_mul_of_nonneg_left (hqbound a ha) (mul_nonneg hfa hpa)]
      have hAeq : (∫ a in Set.Ioi ε, a ^ (t + (s : ℝ)) / risingFac a n * π a) =
          ∫ a, f a * q a * π a ∂μ := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro a ha
        dsimp [f, q, r]
        rw [show t + (s : ℝ) = (t + (s : ℝ) - 1) + 1 by ring,
          Real.rpow_add (hs0 ha), Real.rpow_one]
        ring
      have hEtail : (∫ a, f a * π a ∂μ) ≤ (priorMoment π r).toReal := by
        rw [← hEeq]
        exact setIntegral_mono_set hEint hm0 (Filter.Eventually.of_forall hs0)
      have hA : (∫ a, f a * q a * π a ∂μ) ≤
          (priorMoment π r).toReal * q ε := by
        calc
          _ ≤ ∫ a, (f a * π a) * q ε ∂μ := integral_mono_ae hfq (hf.mul_const _) (by
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
            have hfa : 0 ≤ f a := Real.rpow_nonneg (hs0 ha).le _
            nlinarith [mul_le_mul_of_nonneg_left (hqbound a ha)
              (mul_nonneg hfa (hπnonneg a (hs0 ha)))])
          _ = (∫ a, f a * π a ∂μ) * q ε := integral_mul_const _ _
          _ ≤ _ := mul_le_mul_of_nonneg_right hEtail hqeps.le
      constructor
      · simpa [hAeq, q, r] using hA
      rw [hAeq]
      have hanti : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, (f x - f y) * (q x - q y) ≤ 0 := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
        by_cases hxy : x ≤ y
        · exact mul_nonpos_of_nonpos_of_nonneg
            (sub_nonpos.mpr (Real.rpow_le_rpow (hs0 hx).le hxy hr))
            (sub_nonneg.mpr (hqanti (hs0 hx) (hs0 hy) hxy))
        · exact mul_nonpos_of_nonneg_of_nonpos
            (sub_nonneg.mpr (Real.rpow_le_rpow (hs0 hy).le (le_of_not_ge hxy) hr))
            (sub_nonpos.mpr (hqanti (hs0 hy) (hs0 hx) (le_of_not_ge hxy)))
      have hcheb := reverse_chebyshev_density μ π f q hp hf hq hfq hp0 hanti
      have hAnon : 0 ≤ ∫ a, f a * q a * π a ∂μ := integral_nonneg_of_ae (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
        exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (hs0 ha).le _) (hqpos a (hs0 ha)).le)
          (hπnonneg a (hs0 ha)))
      have hQnon : 0 ≤ ∫ a, q a * π a ∂μ := integral_nonneg_of_ae (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
        exact mul_nonneg (hqpos a (hs0 ha)).le (hπnonneg a (hs0 ha)))
      have hcheb2 : (∫ a, f a * q a * π a ∂μ) ≤
          2 * (priorMoment π r).toReal * (∫ a, q a * π a ∂μ) := by
        have hh := mul_le_mul_of_nonneg_right hEtail hQnon
        dsimp [μ] at hcheb hAnon ⊢
        nlinarith [mul_le_mul_of_nonneg_right hmass hAnon]
      have hBint : IntegrableOn (fun a => a ^ t / risingFac a n * π a) (Set.Ioi ε) := by
        have hbound : ∀ a ∈ Set.Ioi ε,
            |a ^ t / risingFac a n * π a| ≤
              ε ^ (-(s : ℝ)) * (f a * q a * π a) := by
          intro a ha
          rw [abs_of_nonneg (mul_nonneg (div_nonneg (Real.rpow_nonneg (hs0 ha).le _) (hpos a n (hs0 ha)).le) (hπnonneg a (hs0 ha)))]
          have hnegpow := Real.rpow_le_rpow_of_nonpos hε ha.le (neg_nonpos.mpr (Nat.cast_nonneg s) : -(s : ℝ) ≤ 0)
          have hid : a ^ t / risingFac a n * π a = a ^ (-(s : ℝ)) * (f a * q a * π a) := by
            dsimp [f, q, r]
            calc
              _ = a ^ (t - 1) * a / risingFac a n * π a := by
                rw [Real.rpow_sub (hs0 ha), Real.rpow_one]
                field_simp [ne_of_gt (show 0 < a from hs0 ha)]
              _ = _ := by
                rw [← show -(s : ℝ) + (t + (s : ℝ) - 1) = t - 1 by ring,
                  Real.rpow_add (hs0 ha)]
                ring
          rw [hid]
          exact mul_le_mul_of_nonneg_right hnegpow (mul_nonneg
            (mul_nonneg (Real.rpow_nonneg (hs0 ha).le _) (hqpos a (hs0 ha)).le) (hπnonneg a (hs0 ha)))
        exact (hfq.const_mul _).mono'
          (((measurable_id.pow_const t).div (by unfold risingFac; fun_prop)).aestronglyMeasurable.mul hπmeas.aestronglyMeasurable)
          (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha; exact hbound a ha)
      have hQbound : (∫ a, q a * π a ∂μ) ≤
          ε ^ (1 - t) * (∫ a in Set.Ioi ε, a ^ t / risingFac a n * π a) := by
        calc
          _ ≤ ∫ a in Set.Ioi ε, ε ^ (1 - t) * (a ^ t / risingFac a n * π a) :=
            integral_mono_ae hq (hBint.const_mul _) (by
              filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
              have hpw := Real.rpow_le_rpow_of_nonpos hε ha.le (by linarith : 1 - t ≤ 0)
              have hid : q a * π a = a ^ (1 - t) * (a ^ t / risingFac a n * π a) := by
                dsimp [q]
                rw [← mul_assoc, ← mul_div_assoc, ← Real.rpow_add (hs0 ha),
                  show 1 - t + t = 1 by ring, Real.rpow_one]
              rw [hid]
              exact mul_le_mul_of_nonneg_right hpw (mul_nonneg
                (div_nonneg (Real.rpow_nonneg (hs0 ha).le _) (hpos a n (hs0 ha)).le)
                (hπnonneg a (hs0 ha))))
          _ = _ := integral_const_mul _ _
      exact hcheb2.trans (by
        have h := mul_le_mul_of_nonneg_left hQbound
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
            (show 0 ≤ (priorMoment π r).toReal from ENNReal.toReal_nonneg))
        simpa [r, mul_assoc] using h)
    have harmonic_log_lower (eps : ℝ) (heps : 0 < eps) (m : ℕ) :
        Real.log (((m : ℝ) + 1 + eps) / (1 + eps)) ≤
          ∑ j ∈ Finset.range m, (eps + ((j : ℝ) + 1))⁻¹ := by
      clear reverse_chebyshev_density tail_bounds
      induction m with
      | zero => simp
      | succ m ih =>
        rw [Finset.sum_range_succ]
        have hp : 0 < (m : ℝ) + 1 + eps := by positivity
        have hd : 0 < 1 + eps := by positivity
        have hr : 0 < ((m : ℝ) + 2 + eps) / ((m : ℝ) + 1 + eps) := by positivity
        have h := Real.log_le_sub_one_of_pos hr
        have he : ((m : ℝ) + 2 + eps) / ((m : ℝ) + 1 + eps) - 1 =
            (eps + ((m : ℝ) + 1))⁻¹ := by field_simp; ring
        rw [he] at h
        have hl : Real.log (((m : ℝ) + 1 + eps) / (1 + eps)) =
            Real.log ((m : ℝ) + 1 + eps) - Real.log (1 + eps) :=
          Real.log_div hp.ne' hd.ne'
        have hl' : Real.log (((m : ℝ) + 2 + eps) / ((m : ℝ) + 1 + eps)) =
            Real.log ((m : ℝ) + 2 + eps) - Real.log ((m : ℝ) + 1 + eps) :=
          Real.log_div (by positivity) hp.ne'
        rw [hl] at ih
        rw [hl'] at h
        push_cast
        rw [Real.log_div (by positivity) hd.ne']
        rw [show (m : ℝ) + 1 + 1 + eps = (m : ℝ) + 2 + eps by ring]
        linarith
    have q_exp_lower (n : ℕ) (hn : 1 ≤ n) (eps α : ℝ)
        (heps : 0 < eps) (hα : 0 < α) (hαeps : α ≤ eps) :
        (eps / risingFac eps n) * Real.exp ((eps - α) * Real.log ((n : ℝ) / (1 + eps)))
          ≤ α / risingFac α n := by
      clear reverse_chebyshev_density tail_bounds
      let P := fun z : ℝ => ∏ j ∈ Finset.range (n - 1), (z + ((j : ℝ) + 1))
      have hP : ∀ z, 0 < z → 0 < P z := by
        intro z hz
        exact Finset.prod_pos (fun i _ => by positivity)
      have hlog : Real.log ((n : ℝ) / (1 + eps)) ≤
          ∑ j ∈ Finset.range (n - 1), (eps + ((j : ℝ) + 1))⁻¹ := by
        have h := harmonic_log_lower eps heps (n-1)
        have hncast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by norm_cast; omega
        rw [hncast] at h
        apply le_trans _ h
        apply Real.log_le_log
        · positivity
        · apply div_le_div_of_nonneg_right _ (by positivity)
          linarith
      have hterm : ∀ j ∈ Finset.range (n - 1),
          Real.exp ((eps - α) * (eps + ((j : ℝ) + 1))⁻¹)
            ≤ (eps + ((j : ℝ) + 1)) / (α + ((j : ℝ) + 1)) := by
        intro j hj
        have ha : 0 < α + ((j : ℝ) + 1) := by positivity
        have he : 0 < eps + ((j : ℝ) + 1) := by positivity
        rw [← Real.le_log_iff_exp_le (div_pos he ha)]
        have h := Real.one_sub_inv_le_log_of_pos (div_pos he ha)
        have heq : 1 - ((eps + ((j : ℝ) + 1)) / (α + ((j : ℝ) + 1)))⁻¹ =
            (eps - α) * (eps + ((j : ℝ) + 1))⁻¹ := by field_simp; ring
        rwa [heq] at h
      have hprod : Real.exp ((eps - α) * ∑ j ∈ Finset.range (n - 1),
            (eps + ((j : ℝ) + 1))⁻¹) ≤ P eps / P α := by
        rw [Finset.mul_sum, Real.exp_sum]
        change _ ≤ (∏ j ∈ Finset.range (n - 1), (eps + ((j : ℝ) + 1))) /
          (∏ j ∈ Finset.range (n - 1), (α + ((j : ℝ) + 1)))
        rw [← Finset.prod_div_distrib]
        exact Finset.prod_le_prod (fun j _ => (Real.exp_pos _).le) hterm
      have hExp : Real.exp ((eps - α) * Real.log ((n : ℝ) / (1 + eps))) ≤ P eps / P α :=
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hlog (sub_nonneg.mpr hαeps))).trans hprod
      have heq := (statopia_math_node_1445702134_3c8d3810.2.2.2.2.2.2 n hn).2.2
      rw [heq eps heps, heq α hα]
      change 1 / P eps * Real.exp _ ≤ 1 / P α
      simpa only [one_div] using (inv_mul_le_iff₀ (hP eps heps)).mpr (by simpa [mul_div_assoc] using hExp)
    have exp_rpow_integral (u eps L : ℝ) (hu : 1 < u) (heps : 0 < eps) (hL : 0 < L) :
        (∫ α in Set.Ioo (0:ℝ) eps, α ^ (u - 1) * Real.exp (-L * α)) =
          lowerGamma u (eps * L) / L ^ u := by
      clear reverse_chebyshev_density tail_bounds harmonic_log_lower q_exp_lower
      have hpoint : (∫ α in (0:ℝ)..eps, (L * α) ^ (u - 1) * Real.exp (-(L * α))) =
          L ^ (u - 1) * (∫ α in (0:ℝ)..eps, α ^ (u - 1) * Real.exp (-L * α)) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro α hα
        rw [Set.uIcc_of_le heps.le] at hα
        dsimp only
        rw [Real.mul_rpow hL.le hα.1]
        simp only [neg_mul]
        ring
      have hscale := intervalIntegral.integral_comp_mul_left
          (fun z : ℝ => z ^ (u - 1) * Real.exp (-z))
          (a := 0) (b := eps) hL.ne'
      simp only [mul_zero, smul_eq_mul] at hscale
      rw [hpoint] at hscale
      change _ = L⁻¹ * lowerGamma u (L * eps) at hscale
      have hpow : L ^ (u - 1) = L ^ u / L := Real.rpow_sub_one hL.ne' u
      rw [hpow, mul_comm L eps] at hscale
      rw [intervalIntegral.integral_of_le heps.le, MeasureTheory.integral_Ioc_eq_integral_Ioo] at hscale
      apply (eq_div_iff (Real.rpow_pos_of_pos hL u).ne').mpr
      field_simp at hscale
      rw [mul_comm]
      simpa only [neg_mul, mul_comm L eps] using hscale
    have head_gamma_lower (t eps delta beta : ℝ) (n : ℕ) (π : ℝ → ℝ)
        (ht : 1 ≤ t) (heps : 0 < eps) (hdelta : 0 < delta) (hbeta : 0 < beta)
        (hn : 1 ≤ n) (hL : 0 < Real.log ((n : ℝ) / (1 + eps)))
        (hA2 : ∀ α ∈ Set.Ioo (0:ℝ) eps, delta⁻¹ * α ^ beta ≤ π α)
        (hB_int : IntegrableOn (fun α : ℝ => α ^ t / risingFac α n * π α) (Set.Ioo (0:ℝ) eps)) :
        (eps / risingFac eps n) * (delta⁻¹ * Real.exp (eps * Real.log ((n : ℝ) / (1 + eps))) *
          lowerGamma (t + beta) (eps * Real.log ((n : ℝ) / (1 + eps))) /
            Real.log ((n : ℝ) / (1 + eps)) ^ (t + beta)) ≤
          ∫ α in Set.Ioo (0:ℝ) eps, α ^ t / risingFac α n * π α := by
      clear reverse_chebyshev_density tail_bounds harmonic_log_lower
      let L := Real.log ((n : ℝ) / (1 + eps))
      have hu : 1 < t + beta := by linarith
      have hc : Continuous (fun α : ℝ => α ^ (t + beta - 1) * Real.exp (-L * α)) :=
        (Real.continuous_rpow_const (by linarith)).mul (by fun_prop)
      have hint : IntegrableOn (fun α : ℝ => α ^ (t + beta - 1) * Real.exp (-L * α))
          (Set.Ioo (0:ℝ) eps) := (hc.intervalIntegrable 0 eps).1.mono_set (Set.Ioo_subset_Ioc_self)
      let C := eps / risingFac eps n * (delta⁻¹ * Real.exp (eps * L))
      have hpt : ∀ α ∈ Set.Ioo (0:ℝ) eps,
          C * (α ^ (t + beta - 1) * Real.exp (-L * α)) ≤ α ^ t / risingFac α n * π α := by
        intro α hα
        have hq := q_exp_lower n hn eps α heps hα.1 hα.2.le
        have hfactor : C * (α ^ (t + beta - 1) * Real.exp (-L * α)) =
            (delta⁻¹ * α ^ (t + beta - 1)) *
              ((eps / risingFac eps n) * Real.exp ((eps - α) * L)) := by
          dsimp [C]
          rw [show (eps - α) * L = eps * L + -L * α by ring, Real.exp_add]
          ring
        rw [hfactor]
        have he : (delta⁻¹ * α ^ (t + beta - 1)) * (α / risingFac α n) =
            α ^ t / risingFac α n * (delta⁻¹ * α ^ beta) := by
          rw [Real.rpow_sub_one hα.1.ne', Real.rpow_add hα.1]
          field_simp [hα.1.ne']
        calc (delta⁻¹ * α ^ (t + beta - 1)) *
              ((eps / risingFac eps n) * Real.exp ((eps - α) * L))
            ≤ (delta⁻¹ * α ^ (t + beta - 1)) * (α / risingFac α n) :=
              mul_le_mul_of_nonneg_left hq (mul_nonneg (inv_pos.mpr hdelta).le (Real.rpow_pos_of_pos hα.1 _).le)
          _ = α ^ t / risingFac α n * (delta⁻¹ * α ^ beta) := he
          _ ≤ α ^ t / risingFac α n * π α := mul_le_mul_of_nonneg_left (hA2 α hα)
              (div_nonneg (Real.rpow_pos_of_pos hα.1 t).le
                (statopia_math_node_1445702134_3c8d3810.1 α n hα.1).le)
      have hmono := MeasureTheory.setIntegral_mono_on (hint.const_mul C) hB_int measurableSet_Ioo hpt
      rw [MeasureTheory.integral_const_mul, exp_rpow_integral (t+beta) eps L hu heps hL] at hmono
      simpa only [C, L, mul_div_assoc, mul_assoc] using hmono
    have bernoulli_two (u : ℝ) (hu : 1 ≤ u) : u + 1 ≤ (2 : ℝ) ^ u := by
      clear reverse_chebyshev_density tail_bounds harmonic_log_lower q_exp_lower exp_rpow_integral head_gamma_lower
      simpa only [mul_one, show (1 : ℝ) + 1 = 2 by norm_num, add_comm] using (one_add_mul_self_le_rpow_one_add (s := (1 : ℝ)) (by norm_num) hu)
    have gamma_ratio_ge (u a y : ℝ) (hu : 0 < u) (ha : 0 < a) (hy : 0 < y)
        (hy1 : y ≤ 1) : Real.exp (-1) * (y / a) ^ u ≤ lowerGamma u y / lowerGamma u a := by
      clear reverse_chebyshev_density tail_bounds harmonic_log_lower q_exp_lower exp_rpow_integral head_gamma_lower bernoulli_two
      have hd := statopia_math_node_3224678180_5a630a9f
      have hD := hd.1 u a hu ha
      have hU := hd.2.1 u a hu ha
      have hG := hd.2.2.1 u y hu hy
      have he : Real.exp (-1) ≤ Real.exp (-y) := Real.exp_le_exp.mpr (by linarith)
      have hp : Real.exp (-1) * y ^ u / u ≤ lowerGamma u y := by
        calc _ ≤ Real.exp (-y) * y ^ u / u := by gcongr
             _ ≤ _ := hG
      apply (le_div_iff₀ hD).mpr
      rw [Real.div_rpow hy.le ha.le]
      have hpow := Real.rpow_pos_of_pos ha u
      calc
        Real.exp (-1) * (y ^ u / a ^ u) * lowerGamma u a
          ≤ Real.exp (-1) * (y ^ u / a ^ u) * (a ^ u / u) := by gcongr
        _ = Real.exp (-1) * y ^ u / u := by field_simp [ne_of_gt hpow, ne_of_gt hu] <;> ring
        _ ≤ _ := hp
    have gamma_smallratio_lt_six (u ε δ : ℝ) (s n : ℕ)
        (hu : 1 ≤ u) (he : 0 < ε) (hehalf : ε < 1 / 2)
        (hd : 1 ≤ δ) (hs : 1 ≤ s) (hn : 2 ≤ n)
        (hsmall : lowerGamma u (ε * Real.log ((n : ℝ) / (1 + ε))) /
            lowerGamma u (ε * Real.log 2) < (u + s) / (3 * δ * s)) : n < 6 := by
      clear reverse_chebyshev_density tail_bounds harmonic_log_lower q_exp_lower exp_rpow_integral head_gamma_lower
      let a := ε * Real.log 2
      let y := ε * Real.log ((n : ℝ) / (1 + ε))
      have hu0 : 0 < u := by linarith
      have hδ : 0 < δ := by linarith
      have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
      have hs0 : (0 : ℝ) < s := by linarith
      have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
      have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have ha : 0 < a := mul_pos he hl2
      have hy : 0 < y := by
        apply mul_pos he
        apply Real.log_pos
        exact (one_lt_div (by linarith : 0 < 1 + ε)).mpr (by linarith)
      have hD := statopia_math_node_3224678180_5a630a9f.1 u a hu0 ha
      have hDa := statopia_math_node_3224678180_5a630a9f.2.1 u a hu0 ha
      have hc : (u + (s : ℝ)) / (3 * δ * s) ≤ (u + 1) / 3 := by
        apply (div_le_iff₀ (by positivity : 0 < 3 * δ * (s : ℝ))).mpr
        have hp : 1 ≤ δ * (s : ℝ) := by nlinarith
        nlinarith
      have hsmall' : lowerGamma u y / lowerGamma u a < (u + 1) / 3 := hsmall.trans_le hc
      have haexp : a < Real.exp (-1) := by
        have hee := Real.exp_one_lt_d9
        have hlog := Real.log_two_lt_d9
        have heep := Real.exp_pos (1 : ℝ)
        have hprod : a * Real.exp 1 < 1 := by dsimp [a]; nlinarith
        have hei : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; norm_num
        nlinarith
      have hy1 : y < 1 := by
        by_contra hny
        have hG := statopia_math_node_3224678180_5a630a9f.2.2.2.1 u y hu0 (le_of_not_gt hny)
        have hpow : a ^ u < (Real.exp (-1)) ^ u := Real.rpow_lt_rpow ha.le haexp hu0
        rw [← Real.exp_mul] at hpow
        have huExp : u ≤ Real.exp (u - 1) := by linarith [Real.add_one_le_exp (u - 1)]
        have hm : Real.exp (u - 1) * a ^ u < Real.exp (-1) := by
          calc _ < Real.exp (u - 1) * Real.exp (-1 * u) := mul_lt_mul_of_pos_left hpow (Real.exp_pos _)
               _ = _ := by rw [← Real.exp_add]; congr 1; ring
        have hpowpos : 0 < a ^ u := Real.rpow_pos_of_pos ha u
        have hr : u < lowerGamma u y / lowerGamma u a := by
          apply (lt_div_iff₀ hD).mpr
          have hz : 0 < Real.exp (-1) := Real.exp_pos _
          have hN : u * lowerGamma u a ≤ a ^ u := by nlinarith [(le_div_iff₀ hu0).mp hDa]
          have hG' : Real.exp (-1) ≤ lowerGamma u y * u := (div_le_iff₀ hu0).mp hG
          have : u * a ^ u < Real.exp (-1) := lt_of_le_of_lt (mul_le_mul_of_nonneg_right huExp hpowpos.le) hm
          nlinarith
        linarith
      have hratio := gamma_ratio_ge u a y hu0 ha hy hy1.le
      have hec : (y / a) ^ u < Real.exp 1 * ((u + 1) / 3) := by
        have hei : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; norm_num
        nlinarith [Real.exp_pos (1 : ℝ)]
      have ht : Real.exp 1 * ((u + 1) / 3) < (2 : ℝ) ^ u := by
        have h3 := Real.exp_one_lt_three
        have hber := bernoulli_two u hu
        nlinarith
      have hya : y / a < 2 := by
        by_contra h
        have hmono := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 2) (le_of_not_gt h) hu0.le
        linarith
      have hlog : Real.log ((n : ℝ) / (1 + ε)) < Real.log (4 : ℝ) := by
        have h := (div_lt_iff₀ ha).mp hya
        dsimp [y, a] at h
        have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; norm_num
        rw [h4]
        nlinarith
      have hn6 : (n : ℝ) < 6 := by
        have hdiv : (n : ℝ) / (1 + ε) < 4 := (Real.log_lt_log_iff (by positivity) (by norm_num)).mp hlog
        have h := (div_lt_iff₀ (by linarith : 0 < 1 + ε)).mp hdiv
        linarith
      exact_mod_cast hn6
    have small_n_exp_log (ε : ℝ) (n : ℕ) (he : 0 < ε) (hehalf : ε < 1 / 2)
        (hn : 2 ≤ n) (hn6 : n < 6) :
        (1 / 2 : ℝ) ≤ Real.exp (-(ε * Real.log (n : ℝ))) *
          (Real.log (n : ℝ) / Real.log 2) := by
      clear reverse_chebyshev_density tail_bounds harmonic_log_lower q_exp_lower exp_rpow_integral head_gamma_lower bernoulli_two gamma_ratio_ge gamma_smallratio_lt_six
      have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
      have hn0 : (0 : ℝ) < n := by linarith
      have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hln : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hnR
      have hln0 : 0 < Real.log n := lt_of_lt_of_le hl2 hln
      have hr : (1 : ℝ) ≤ Real.log n / Real.log 2 := (one_le_div hl2).mpr hln
      by_cases h4 : n ≤ 4
      · have h4R : (n : ℝ) ≤ 4 := by exact_mod_cast h4
        have hl4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; norm_num
        have hln4 := Real.log_le_log hn0 h4R
        have hx : ε * Real.log n ≤ Real.log 2 := by nlinarith
        have hxp : (1 / 2 : ℝ) ≤ Real.exp (-(ε * Real.log n)) := by
          have h := Real.exp_le_exp.mpr (show -Real.log 2 ≤ -(ε * Real.log n) by linarith)
          simpa [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)] using h
        nlinarith
      · have hn5 : n = 5 := by omega
        subst n
        have h53 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
        have hl9 : Real.log (9 : ℝ) = 2 * Real.log 3 := by
          rw [show (9 : ℝ) = 3 ^ (2 : ℕ) by norm_num, Real.log_pow]; norm_num
        have hl59 : Real.log (5 : ℝ) ≤ Real.log 9 := Real.log_le_log (by norm_num) (by norm_num)
        have hx : ε * Real.log 5 ≤ Real.log 3 := by norm_num at hln0 ⊢; nlinarith
        have hxp : (1 / 3 : ℝ) ≤ Real.exp (-(ε * Real.log 5)) := by
          have h := Real.exp_le_exp.mpr (show -Real.log 3 ≤ -(ε * Real.log 5) by linarith)
          simpa [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 3)] using h
        have hl4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; norm_num
        have hl45 : Real.log (4 : ℝ) ≤ Real.log 5 := Real.log_le_log (by norm_num) (by norm_num)
        have hr2 : (2 : ℝ) ≤ Real.log 5 / Real.log 2 := (le_div_iff₀ hl2).mpr (by linarith)
        norm_num at *
        nlinarith [Real.exp_pos (-(ε * Real.log 5))]
    have gamma_two_parameter_lower (u a x y : ℝ) (s : ℕ)
        (hu : 0 < u) (ha : 0 < a) (hx : 0 < x) (hy : 0 < y) :
        Real.exp (-x) * (u / (u + s)) * (x / a) ^ u * (x / y) ^ s ≤
          lowerGamma (u + s) x / (lowerGamma u a * y ^ s) := by
      clear reverse_chebyshev_density tail_bounds harmonic_log_lower q_exp_lower exp_rpow_integral head_gamma_lower bernoulli_two gamma_ratio_ge gamma_smallratio_lt_six small_n_exp_log
      have hv : 0 < u + (s : ℝ) := by positivity
      have hD := statopia_math_node_3224678180_5a630a9f.1 u a hu ha
      have hU := statopia_math_node_3224678180_5a630a9f.2.1 u a hu ha
      have hG := statopia_math_node_3224678180_5a630a9f.2.2.1 (u+s) x hv hx
      have haPow := Real.rpow_pos_of_pos ha u
      have hyPow : 0 < y ^ s := pow_pos hy s
      apply (le_div_iff₀ (mul_pos hD hyPow)).mpr
      calc
        Real.exp (-x) * (u / (u + s)) * (x / a) ^ u * (x / y) ^ s *
            (lowerGamma u a * y ^ s)
          ≤ Real.exp (-x) * (u / (u + s)) * (x / a) ^ u * (x / y) ^ s *
            ((a ^ u / u) * y ^ s) := by gcongr
        _ = Real.exp (-x) * x ^ (u + s) / (u + s) := by
          rw [Real.div_rpow hx.le ha.le, div_pow, Real.rpow_add hx, Real.rpow_natCast]
          field_simp [ne_of_gt hu, ne_of_gt hv, ne_of_gt haPow, ne_of_gt hyPow]
        _ ≤ _ := hG
    have small_n_weight_reduced (u ε δ β : ℝ) (s n : ℕ)
        (hu : 1 ≤ u) (he : 0 < ε) (hehalf : ε < 1 / 2)
        (hd : 1 ≤ δ) (hβ : 0 < β) (hs : 1 ≤ s) (hn : 2 ≤ n) (hn6 : n < 6) :
        1 ≤ 2 * δ ^ 2 * (s : ℝ) * ε ^ (-(β + 1)) *
          lowerGamma (u + s) (ε * Real.log n) /
            (lowerGamma u (ε * Real.log 2) * (ε * Real.log ((n : ℝ) / (1 + ε))) ^ s) := by
      clear reverse_chebyshev_density tail_bounds harmonic_log_lower q_exp_lower exp_rpow_integral head_gamma_lower bernoulli_two gamma_ratio_ge gamma_smallratio_lt_six
      let l := Real.log (n : ℝ)
      let L := Real.log ((n : ℝ) / (1 + ε))
      have hu0 : 0 < u := by linarith
      have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
      have hs0 : (0 : ℝ) < s := by linarith
      have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
      have hn0 : (0 : ℝ) < n := by linarith
      have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hl : 0 < l := by dsimp [l]; exact Real.log_pos (by linarith)
      have hL : 0 < L := by
        apply Real.log_pos
        exact (one_lt_div (by linarith : 0 < 1 + ε)).mpr (by linarith)
      have hLl : L ≤ l := by
        apply Real.log_le_log (by positivity)
        exact (div_le_iff₀ (by linarith : 0 < 1 + ε)).mpr (by nlinarith)
      have hl2l : Real.log 2 ≤ l := Real.log_le_log (by norm_num) hnR
      have hf : (1 : ℝ) ≤ l / Real.log 2 := (one_le_div hl2).mpr hl2l
      have hg : (1 : ℝ) ≤ l / L := (one_le_div hL).mpr hLl
      have hfp : l / Real.log 2 ≤ (l / Real.log 2) ^ u := Real.self_le_rpow_of_one_le hf hu
      have hgp : (1 : ℝ) ≤ (l / L) ^ s := one_le_pow₀ hg
      have hv : 0 < u + (s : ℝ) := by positivity
      have hsfrac : (1 / 2 : ℝ) ≤ (s : ℝ) * u / (u + s) := by
        apply (le_div_iff₀ hv).mpr
        have hsu : (s : ℝ) ≤ s * u := by nlinarith
        have hus : u ≤ s * u := by nlinarith
        linarith
      have hpε : (2 : ℝ) ≤ ε ^ (-(β + 1)) := by
        have hmono : ε ^ (-1 : ℝ) ≤ ε ^ (-(β + 1)) :=
          Real.rpow_le_rpow_of_exponent_ge he (by linarith) (by linarith)
        rw [Real.rpow_neg_one] at hmono
        have h2 : (2 : ℝ) ≤ ε⁻¹ := by
          rw [← one_div, le_div_iff₀ he]
          linarith
        exact h2.trans hmono
      have hc : (2 : ℝ) ≤ 2 * δ ^ 2 * ε ^ (-(β + 1)) * ((s : ℝ) * u / (u + s)) := by
        have hd2 : (1 : ℝ) ≤ δ ^ 2 := by nlinarith
        have hpp : 0 ≤ ε ^ (-(β + 1)) := Real.rpow_nonneg he.le _
        have hprod := mul_le_mul hd2 hpε (by norm_num : (0 : ℝ) ≤ 2) (by positivity : 0 ≤ δ ^ 2)
        have hprod2 := mul_le_mul hprod hsfrac (by norm_num : (0 : ℝ) ≤ 1/2)
          (by positivity : 0 ≤ δ ^ 2 * ε ^ (-(β + 1)))
        nlinarith
      have hexp := small_n_exp_log ε n he hehalf hn hn6
      have hefp : (1 / 2 : ℝ) ≤ Real.exp (-(ε * l)) * (l / Real.log 2) ^ u := by
        calc _ ≤ Real.exp (-(ε * l)) * (l / Real.log 2) := hexp
             _ ≤ _ := mul_le_mul_of_nonneg_left hfp (Real.exp_pos _).le
      have hgam := gamma_two_parameter_lower u (ε * Real.log 2) (ε * l) (ε * L) s
        hu0 (mul_pos he hl2) (mul_pos he hl) (mul_pos he hL)
      have hxa : (ε * l) / (ε * Real.log 2) = l / Real.log 2 := by field_simp
      have hxy : (ε * l) / (ε * L) = l / L := by field_simp
      rw [hxa, hxy] at hgam
      have hcpos : 0 ≤ 2 * δ ^ 2 * (s : ℝ) * ε ^ (-(β + 1)) := by positivity
      have hmul := mul_le_mul_of_nonneg_left hgam hcpos
      have hleft : 1 ≤ (2 * δ ^ 2 * (s : ℝ) * ε ^ (-(β + 1))) *
          (Real.exp (-(ε * l)) * (u / (u + s)) * (l / Real.log 2) ^ u * (l / L) ^ s) := by
        have hfpos : 0 ≤ Real.exp (-(ε * l)) * (l / Real.log 2) ^ u := by positivity
        have hcpos2 : 0 ≤ 2 * δ ^ 2 * ε ^ (-(β + 1)) * ((s : ℝ) * u / (u + s)) := by positivity
        have hab : 1 ≤ (2 * δ ^ 2 * ε ^ (-(β + 1)) * ((s : ℝ) * u / (u + s))) *
            (Real.exp (-(ε * l)) * (l / Real.log 2) ^ u) := by nlinarith
        have hmul2 := mul_le_mul_of_nonneg_left hgp (mul_nonneg hcpos2 hfpos)
        simp only [mul_one] at hmul2
        convert hab.trans hmul2 using 1 <;> ring
      convert hleft.trans hmul using 1 <;> dsimp [l, L] <;> ring
    have weight_ratio_identity (t ε δ β : ℝ) (s n : ℕ) (he : 0 < ε)
        (hn : 2 ≤ n) (hehalf : ε < 1 / 2) (hu : 0 < t + β) :
        2 * ε ^ (1 - t) *
          (2 * δ ^ 2 * (s : ℝ) * ε ^ (-(β + 1)) *
            lowerGamma (t + β + s) (ε * Real.log n) /
              (lowerGamma (t + β) (ε * Real.log 2) *
                (ε * Real.log ((n : ℝ) / (1 + ε))) ^ s)) =
          Gconst t ε δ β * (s : ℝ) / ε ^ s *
            (lowerGamma (t + (s : ℝ) + β) (ε * Real.log n) /
              Real.log ((n : ℝ) / (1 + ε)) ^ s) := by
      clear reverse_chebyshev_density tail_bounds harmonic_log_lower q_exp_lower exp_rpow_integral head_gamma_lower bernoulli_two gamma_ratio_ge gamma_smallratio_lt_six small_n_exp_log gamma_two_parameter_lower small_n_weight_reduced
      have hD : 0 < lowerGamma (t + β) (ε * Real.log 2) :=
        statopia_math_node_3224678180_5a630a9f.1 _ _ hu
          (mul_pos he (Real.log_pos (by norm_num)))
      have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
      have hL : 0 < Real.log ((n : ℝ) / (1 + ε)) := by
        apply Real.log_pos
        exact (one_lt_div (by linarith : 0 < 1 + ε)).mpr (by linarith)
      have hsum : ε ^ (1 - t) * ε ^ (t + β) = ε ^ (β + 1) := by
        rw [← Real.rpow_add he]
        congr 1
        ring
      dsimp [Gconst]
      rw [Real.rpow_neg he.le, mul_pow]
      rw [show t + β + (s : ℝ) = t + (s : ℝ) + β by ring]
      have heS := pow_pos he s
      have hLS := pow_pos hL s
      have heU := Real.rpow_pos_of_pos he (t + β)
      have heB := Real.rpow_pos_of_pos he (β + 1)
      field_simp [ne_of_gt heS, ne_of_gt hLS, ne_of_gt heU, ne_of_gt heB, ne_of_gt hD]
      calc
        _ = (ε ^ (1 - t) * ε ^ (t + β)) *
            (4 * δ ^ 2 * (s : ℝ) * lowerGamma (t + (s : ℝ) + β) (ε * Real.log n)) := by ring
        _ = _ := by rw [hsum]; ring
    have small_n_weight (t ε δ β : ℝ) (s n : ℕ)
        (ht : 1 ≤ t) (he : 0 < ε) (hehalf : ε < 1 / 2)
        (hd : 1 ≤ δ) (hβ : 0 < β) (hs : 1 ≤ s) (hn : 2 ≤ n) (hn6 : n < 6) :
        2 * ε ^ (1 - t) ≤
          Gconst t ε δ β * (s : ℝ) / ε ^ s *
            (lowerGamma (t + (s : ℝ) + β) (ε * Real.log n) /
              Real.log ((n : ℝ) / (1 + ε)) ^ s) := by
      clear reverse_chebyshev_density tail_bounds harmonic_log_lower q_exp_lower exp_rpow_integral head_gamma_lower bernoulli_two gamma_ratio_ge gamma_smallratio_lt_six small_n_exp_log gamma_two_parameter_lower
      have h := small_n_weight_reduced (t+β) ε δ β s n (by linarith)
        he hehalf hd hβ hs hn hn6
      have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ 2 * ε ^ (1-t) by positivity)
      simpa only [mul_one, weight_ratio_identity t ε δ β s n he hn hehalf (by linarith)] using hm
    have gamma_weight_dichotomy (t ε δ β : ℝ) (s n : ℕ)
        (ht : 1 ≤ t) (he : 0 < ε) (hehalf : ε < 1 / 2)
        (hd : 1 ≤ δ) (hβ : 0 < β) (hs : 1 ≤ s) (hn : 2 ≤ n) :
        (t + β + s) / (3 * δ * s) ≤
          lowerGamma (t + β) (ε * Real.log ((n : ℝ) / (1 + ε))) /
            lowerGamma (t + β) (ε * Real.log 2) ∨
        2 * ε ^ (1 - t) ≤
          Gconst t ε δ β * (s : ℝ) / ε ^ s *
            (lowerGamma (t + (s : ℝ) + β) (ε * Real.log n) /
              Real.log ((n : ℝ) / (1 + ε)) ^ s) := by
      clear reverse_chebyshev_density tail_bounds harmonic_log_lower q_exp_lower exp_rpow_integral head_gamma_lower bernoulli_two gamma_ratio_ge small_n_exp_log gamma_two_parameter_lower small_n_weight_reduced weight_ratio_identity
      by_cases h : (t + β + s) / (3 * δ * s) ≤
          lowerGamma (t + β) (ε * Real.log ((n : ℝ) / (1 + ε))) /
            lowerGamma (t + β) (ε * Real.log 2)
      · exact Or.inl h
      · exact Or.inr (small_n_weight t ε δ β s n ht he hehalf hd hβ hs hn
          (gamma_smallratio_lt_six (t+β) ε δ s n (by linarith) he hehalf hd hs hn (lt_of_not_ge h)))
    have large_gamma_scalar (δ s v D K H y q B : ℝ)
        (hδ : 0 < δ) (hs : 0 < s) (hv : 0 < v) (hD : 0 < D)
        (hy : 0 < y) (hq : 0 ≤ q)
        (hH : v / (3 * δ * s) ≤ H / D)
        (hK : Real.exp (-y) * y ^ v / v ≤ K)
        (hB : q * (δ⁻¹ * Real.exp y * H / y ^ v) ≤ B) :
        q ≤ (3 / 4 : ℝ) * (4 * δ ^ 2 * s * K / D) * B := by
      clear reverse_chebyshev_density tail_bounds harmonic_log_lower q_exp_lower exp_rpow_integral head_gamma_lower bernoulli_two gamma_ratio_ge gamma_smallratio_lt_six small_n_exp_log gamma_two_parameter_lower small_n_weight_reduced weight_ratio_identity small_n_weight gamma_weight_dichotomy
      have hY : 0 < y ^ v := Real.rpow_pos_of_pos hy _
      have hH0 : 0 < H := by
        have hh : 0 < H / D := lt_of_lt_of_le (by positivity) hH
        exact (div_pos_iff.mp hh).elim (fun h => h.1) (fun h => False.elim ((not_lt_of_ge hD.le) h.2))
      have hK0 : 0 < K := lt_of_lt_of_le (by positivity) hK
      have hH' : v * D ≤ H * (3 * δ * s) := (div_le_div_iff₀ (by positivity) hD).mp hH
      have hK' : Real.exp (-y) * y ^ v ≤ K * v := (div_le_iff₀ hv).mp hK
      have he : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
      have hke : y ^ v ≤ K * v * Real.exp y := by nlinarith [Real.exp_pos y]
      have hcoef : 1 ≤ 3 * δ * s * K * Real.exp y * H / (D * y ^ v) := by
        apply (le_div_iff₀ (mul_pos hD hY)).mpr
        have hh := mul_le_mul_of_nonneg_right hH' hK0.le
        have hh2 := mul_le_mul_of_nonneg_right hh (Real.exp_pos y).le
        have hk := mul_le_mul_of_nonneg_left hke hD.le
        nlinarith
      calc
        q = q * 1 := by ring
        _ ≤ q * (3 * δ * s * K * Real.exp y * H / (D * y ^ v)) :=
          mul_le_mul_of_nonneg_left hcoef hq
        _ = (3 / 4 : ℝ) * (4 * δ ^ 2 * s * K / D) *
            (q * (δ⁻¹ * Real.exp y * H / y ^ v)) := by field_simp <;> ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hB (by positivity)
    have large_gamma_head_bridge (t ε δ β q B : ℝ) (s n : ℕ)
        (ht : 1 ≤ t) (he : 0 < ε) (hehalf : ε < 1 / 2)
        (hd : 0 < δ) (hb : 0 < β) (hs : 1 ≤ s) (hn : 2 ≤ n)
        (hq : 0 ≤ q)
        (hhead : q * (δ⁻¹ * Real.exp (ε * Real.log ((n : ℝ) / (1 + ε))) *
            lowerGamma (t + β) (ε * Real.log ((n : ℝ) / (1 + ε))) /
              Real.log ((n : ℝ) / (1 + ε)) ^ (t + β)) ≤ B)
        (hlarge : (t + β + s) / (3 * δ * s) ≤
          lowerGamma (t + β) (ε * Real.log ((n : ℝ) / (1 + ε))) /
            lowerGamma (t + β) (ε * Real.log 2)) :
        q ≤ (3 / 4 : ℝ) *
          (Gconst t ε δ β * (s : ℝ) / ε ^ s *
            (lowerGamma (t + (s : ℝ) + β) (ε * Real.log n) /
              Real.log ((n : ℝ) / (1 + ε)) ^ s)) * B := by
      clear reverse_chebyshev_density tail_bounds harmonic_log_lower q_exp_lower exp_rpow_integral head_gamma_lower bernoulli_two gamma_ratio_ge gamma_smallratio_lt_six small_n_exp_log gamma_two_parameter_lower small_n_weight_reduced weight_ratio_identity small_n_weight gamma_weight_dichotomy
      let u := t + β
      let v := t + β + (s : ℝ)
      let L := Real.log ((n : ℝ) / (1 + ε))
      let y := ε * L
      let D := lowerGamma u (ε * Real.log 2)
      let K := lowerGamma v (ε * Real.log n)
      let H := lowerGamma u y
      have hu : 0 < u := by dsimp [u]; linarith
      have hv : 0 < v := by dsimp [v]; positivity
      have hL : 0 < L := by
        apply Real.log_pos
        apply (one_lt_div (by positivity : 0 < 1 + ε)).mpr
        have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      have hy : 0 < y := mul_pos he hL
      have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hD : 0 < D := statopia_math_node_3224678180_5a630a9f.1 _ _ hu (mul_pos he hl2)
      have hsR : (0 : ℝ) < s := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hs)
      have hxy : y ≤ ε * Real.log n := by
        apply mul_le_mul_of_nonneg_left _ he.le
        apply Real.log_le_log (by positivity)
        apply (div_le_iff₀ (by positivity : 0 < 1 + ε)).mpr
        have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
        nlinarith
      have hx : 0 < ε * Real.log n := lt_of_lt_of_le hy hxy
      have hK : Real.exp (-y) * y ^ v / v ≤ K := by
        exact (statopia_math_node_3224678180_5a630a9f.2.2.1 v y hv hy).trans
          (statopia_math_node_3224678180_5a630a9f.2.2.2.2.2.1 v hv hy hx hxy)
      let Z := ε ^ v * L ^ s
      have hZ : 0 < Z := mul_pos (Real.rpow_pos_of_pos he v) (pow_pos hL s)
      have hpow : y ^ v = L ^ u * Z := by
        dsimp [y, v, u, Z]
        rw [Real.mul_rpow he.le hL.le, Real.rpow_add hL, Real.rpow_natCast]
        ring
      have hnorm : q * (δ⁻¹ * Real.exp y * H / y ^ v) ≤ B / Z := by
        apply (le_div_iff₀ hZ).mpr
        rw [hpow]
        have heq : q * (δ⁻¹ * Real.exp y * H / (L ^ u * Z)) * Z =
            q * (δ⁻¹ * Real.exp y * H / L ^ u) := by
          field_simp
        rw [heq]
        exact hhead
      have hscl := large_gamma_scalar δ (s:ℝ) v D K H y q (B / Z)
        hd hsR hv hD hy hq hlarge hK hnorm
      convert hscl using 1
      dsimp [Z, v, u, D, K, Gconst, L]
      simp only [Real.rpow_add he, Real.rpow_natCast]
      rw [show t + (s : ℝ) + β = t + β + s by ring]
      field_simp
    clear reverse_chebyshev_density harmonic_log_lower q_exp_lower exp_rpow_integral bernoulli_two gamma_ratio_ge gamma_smallratio_lt_six small_n_exp_log gamma_two_parameter_lower small_n_weight_reduced weight_ratio_identity small_n_weight large_gamma_scalar
    intro t ht pi hpi_meas hpi_nonneg hpi_prob delta beta eps0 eps hdelta hbeta
      heps0 heps heps_lt heps_le hA2 hB1 n s hs hns hfin
    have hA2' : ∀ α ∈ Set.Ioo (0 : ℝ) eps, delta⁻¹ * α ^ beta ≤ pi α ∧ pi α ≤ delta * α ^ beta := by
      intro α hα
      exact hA2 α ⟨hα.1, lt_of_lt_of_le hα.2 heps_le⟩
    have hmass := statopia_math_node_1797268609_53e08000 t ht s hs pi hpi_meas hpi_nonneg hpi_prob
      eps delta beta heps heps_lt hdelta hbeta hA2' hB1
    have hInts := statopia_math_node_3788355289_2a3e6b7e t ht pi hpi_meas hpi_nonneg hpi_prob
      eps delta beta heps hdelta hbeta hA2' n s hs hns
    have hpi_nn : 0 ≤ᶠ[ae (volume.restrict (Set.Ioi (0 : ℝ)))] pi := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
      exact hpi_nonneg α hα
    have hpi_int : IntegrableOn pi (Set.Ioi (0 : ℝ)) := by
      apply (lintegral_ofReal_ne_top_iff_integrable hpi_meas.aestronglyMeasurable hpi_nn).mp
      rw [hpi_prob]; exact ENNReal.one_ne_top
    have hdelta1 : 1 ≤ delta := by
      have hmem : eps / 2 ∈ Set.Ioo (0 : ℝ) eps := ⟨by linarith, by linarith⟩
      have hc : 0 < (eps / 2) ^ beta := Real.rpow_pos_of_pos (by linarith) beta
      have hpair := hA2' _ hmem
      have hle := le_trans hpair.1 hpair.2
      have hinv : delta⁻¹ ≤ delta := le_of_mul_le_mul_right hle hc
      have h3 := mul_le_mul_of_nonneg_left hinv hdelta.le
      rw [mul_inv_cancel₀ hdelta.ne'] at h3
      nlinarith
    have hsR : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
    have hn2 : 2 ≤ n := by exact_mod_cast (show (2 : ℝ) ≤ (n : ℝ) by linarith)
    have hn1 : 1 ≤ n := by omega
    have hL : 0 < Real.log ((n : ℝ) / (1 + eps)) := by
      apply Real.log_pos
      apply (one_lt_div (by positivity)).mpr
      have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
      linarith
    have hTail := tail_bounds t eps s n pi ht hs hn1 heps hpi_meas hpi_nonneg hpi_int
      hmass.2.2.1.2 hfin
    have hBint := hInts.2.2.1
    have hBpos := hInts.2.2.2.1
    have hBtnn := hInts.2.2.2.2.2.2.2.1
    let W := Gconst t eps delta beta * (s : ℝ) / eps ^ s *
      (lowerGamma (t + (s : ℝ) + beta) (eps * Real.log (n : ℝ)) /
        Real.log ((n : ℝ) / (1 + eps)) ^ s)
    have hWpos : 0 < W := statopia_math_node_1492827739_6836739b t eps delta beta n s ht heps heps_lt hdelta hbeta hs hns
    have hEnn : 0 ≤ (priorMoment pi (t + (s : ℝ) - 1)).toReal := ENNReal.toReal_nonneg
    have hHead := head_gamma_lower t eps delta beta n pi ht heps hdelta hbeta hn1 hL
      (fun α hα => (hA2' α hα).1) hBint
    rcases gamma_weight_dichotomy t eps delta beta s n ht heps heps_lt hdelta1 hbeta hs hn2 with hlarge | hsmall
    · have hqnn : 0 ≤ eps / risingFac eps n := div_nonneg heps.le
          (statopia_math_node_1445702134_3c8d3810.1 eps n heps).le
      have hq : eps / risingFac eps n ≤ (3 / 4) * W *
          (∫ α in Set.Ioo 0 eps, α ^ t / risingFac α n * pi α) := by
        exact large_gamma_head_bridge t eps delta beta _ _ s n ht heps heps_lt hdelta hbeta hs hn2 hqnn hHead hlarge
      have htail := hTail.1.trans (mul_le_mul_of_nonneg_left hq hEnn)
      have hExtra := mul_nonneg (mul_nonneg hWpos.le hEnn) hBtnn
      dsimp only [W] at htail hExtra
      nlinarith
    · have hc := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hsmall hEnn) hBtnn
      have htail : (∫ α in Set.Ioi eps, α ^ (t + (s:ℝ)) / risingFac α n * pi α) ≤
          W * (priorMoment pi (t + (s:ℝ) - 1)).toReal *
            (∫ α in Set.Ioi eps, α ^ t / risingFac α n * pi α) := by
        dsimp only [W]
        nlinarith [hTail.2, hc]
      have hExtra := mul_nonneg (mul_nonneg hWpos.le hEnn) hBpos.le
      dsimp only [W] at htail hExtra
      nlinarith
  )
  /- @proof-region region.target-node.session.f4d5709a50e464da end -/

end Statlib.Imported
end
