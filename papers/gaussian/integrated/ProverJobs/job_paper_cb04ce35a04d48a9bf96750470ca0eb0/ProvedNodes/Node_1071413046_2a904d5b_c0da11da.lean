import ProverJobs.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.Vocabulary
import ProverJobs.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.Base

namespace PaperProofTasks.job_paper_cb04ce35a04d48a9bf96750470ca0eb0

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal
open _root_.PaperProofTasks.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.Statlib.Imported

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal
namespace Statlib.Imported
open _root_.Statlib
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_1071413046_2a904d5b : ∀ (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1 / 2)
    (alpha : ℝ) (halpha : 0 < alpha)
    (c_tau : ℝ) (hc_tau : 0 < c_tau)
    (n_tau : ℕ) (hn_tau : 1 ≤ n_tau),
    ∃ n_0 : ℕ, 1 ≤ n_0 ∧
      ∀ (p : ℕ → ℕ) (hp : ∀ n, 1 ≤ p n)
        (L : ℕ → ℕ)
        (hL_def : ∀ n, L n = Nat.ceil (min (max 1 ((Real.log (n : ℝ)) ^ (3 : ℕ))) ((p n : ℝ))))
        (k : ℕ → ℕ)
        (hk_def : ∀ n, k n = Nat.ceil
          (min (max (L n : ℝ) (Real.rpow (n : ℝ) (1 / Real.rpow (Real.log (n : ℝ)) a)))
            ((p n : ℝ))))
        (tau : ℕ → ℝ) (htau0 : ∀ n, 0 ≤ tau n) (htau1 : ∀ n, tau n < 1)
        (beta : ℕ → ℝ) (hbeta_def : ∀ n, beta n = alpha * (1 - tau n))
        (htau_cond : ∀ n, n_tau ≤ n → c_tau ≤ (1 - tau n) * Real.sqrt (Real.log (n : ℝ)))
        (q : ℕ → ℝ) (hq_def : ∀ n, q n = max (2 / beta n) (max (Real.log (n : ℝ)) 3)),
        ∀ n : ℕ, n_0 ≤ n →
          (1 ≤ L n ∧ L n ≤ k n ∧ k n ≤ p n ∧ 0 < beta n ∧ 1 ≤ Real.log (n : ℝ)) ∧
          (3 ≤ q n ∧ Real.log (n : ℝ) ≤ q n ∧ 2 ≤ q n * beta n ∧
            q n ≤ (3 + 2 / (alpha * c_tau)) * Real.log (n : ℝ)) ∧
          (Real.rpow (k n : ℝ) (1 / Real.log (n : ℝ)) ≤ 2 ∧
            Real.rpow (k n : ℝ) (1 / q n) ≤ 2) ∧
          (k n < p n →
            L n = Nat.ceil ((Real.log (n : ℝ)) ^ (3 : ℕ)) ∧ 2 ≤ L n ∧
              Real.log (n : ℝ) ≤ Real.rpow (L n : ℝ) (1 / 3 : ℝ)) := by
  /- @proof-region region.target-node.session.596a15437bd809ff begin -/
  classical
  intro a ha0 ha1 alpha halpha c_tau hc_tau n_tau hn_tau
  have hlog_ge : ∀ V : ℝ, ∃ M : ℕ, ∀ n : ℕ, M ≤ n → V ≤ Real.log (n : ℝ) := by
    intro V
    have h : ∀ᶠ n : ℕ in atTop, V ≤ Real.log (n : ℝ) :=
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop V)
    exact eventually_atTop.mp h
  set U : ℝ := max 10000 (max ((2 / Real.log 2) ^ (1 / a)) (12 ^ (1 / (1 / 2 - a)))) with hU
  obtain ⟨M, hM⟩ := hlog_ge U
  refine ⟨max M n_tau, le_trans hn_tau (le_max_right _ _), ?_⟩
  intro p hp L hL_def k hk_def tau htau0 htau1 beta hbeta_def htau_cond q hq_def n hn
  have hnM : M ≤ n := le_trans (le_max_left _ _) hn
  have hntau : n_tau ≤ n := le_trans (le_max_right _ _) hn
  have hlogU : U ≤ Real.log (n : ℝ) := hM n hnM
  have hU10000 : (10000 : ℝ) ≤ U := by rw [hU]; exact le_max_left _ _
  have hUa : (2 / Real.log 2) ^ (1 / a) ≤ U := by
    rw [hU]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hUb : 12 ^ (1 / (1 / 2 - a)) ≤ U := by
    rw [hU]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hu : (10000 : ℝ) ≤ Real.log (n : ℝ) := le_trans hU10000 hlogU
  have hupos : (0 : ℝ) < Real.log (n : ℝ) := by linarith
  have hu1 : (1 : ℝ) ≤ Real.log (n : ℝ) := by linarith
  have hca : (0 : ℝ) < alpha * c_tau := mul_pos halpha hc_tau
  have hp1 : (1 : ℝ) ≤ (p n : ℝ) := by exact_mod_cast hp n
  have hbeta_pos : 0 < beta n := by
    rw [hbeta_def n]
    have h : 0 < 1 - tau n := by linarith [htau1 n]
    positivity
  have hL1 : 1 ≤ L n := by
    have hz : (1 : ℝ) ≤ min (max (1 : ℝ) ((Real.log (n : ℝ)) ^ (3 : ℕ))) ((p n : ℝ)) :=
      le_min (le_max_left _ _) hp1
    have h2 : (1 : ℝ) ≤
        (Nat.ceil (min (max (1 : ℝ) ((Real.log (n : ℝ)) ^ (3 : ℕ))) ((p n : ℝ))) : ℝ) :=
      le_trans hz (Nat.le_ceil _)
    rw [hL_def n]
    exact_mod_cast h2
  have hLp : L n ≤ p n := by
    rw [hL_def n]
    exact Nat.ceil_le.mpr (min_le_right _ _)
  have hLk : L n ≤ k n := by
    have hz : (L n : ℝ) ≤
        min (max (L n : ℝ) (Real.rpow (n : ℝ) (1 / Real.rpow (Real.log (n : ℝ)) a)))
          ((p n : ℝ)) :=
      le_min (le_max_left _ _) (by exact_mod_cast hLp)
    have h2 : (L n : ℝ) ≤
        (Nat.ceil (min (max (L n : ℝ) (Real.rpow (n : ℝ) (1 / Real.rpow (Real.log (n : ℝ)) a)))
          ((p n : ℝ))) : ℝ) :=
      le_trans hz (Nat.le_ceil _)
    rw [hk_def n]
    exact_mod_cast h2
  have hkp : k n ≤ p n := by
    rw [hk_def n]
    exact Nat.ceil_le.mpr (min_le_right _ _)
  have hq3 : 3 ≤ q n := by
    rw [hq_def n]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hqlog : Real.log (n : ℝ) ≤ q n := by
    rw [hq_def n]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hq2 : 2 ≤ q n * beta n := by
    have h1 : 2 / beta n ≤ q n := by rw [hq_def n]; exact le_max_left _ _
    have h2 := mul_le_mul_of_nonneg_right h1 (le_of_lt hbeta_pos)
    rwa [div_mul_cancel₀ _ (ne_of_gt hbeta_pos)] at h2
  have hqC : q n ≤ (3 + 2 / (alpha * c_tau)) * Real.log (n : ℝ) := by
    have hsq : 0 < Real.sqrt (Real.log (n : ℝ)) := Real.sqrt_pos.mpr hupos
    have hcond := htau_cond n hntau
    have h1 : c_tau / Real.sqrt (Real.log (n : ℝ)) ≤ 1 - tau n := by
      rw [div_le_iff₀ hsq]
      linarith [hcond]
    have hbeta_lb : alpha * (c_tau / Real.sqrt (Real.log (n : ℝ))) ≤ beta n := by
      rw [hbeta_def n]
      exact mul_le_mul_of_nonneg_left h1 halpha.le
    have hmul : alpha * c_tau ≤ beta n * Real.sqrt (Real.log (n : ℝ)) := by
      have h3 := mul_le_mul_of_nonneg_right hbeta_lb hsq.le
      have h4 : alpha * (c_tau / Real.sqrt (Real.log (n : ℝ))) * Real.sqrt (Real.log (n : ℝ))
          = alpha * c_tau := by
        rw [mul_assoc, div_mul_cancel₀ _ (ne_of_gt hsq)]
      rw [h4] at h3
      exact h3
    have h2 : 2 / beta n ≤ 2 * Real.sqrt (Real.log (n : ℝ)) / (alpha * c_tau) := by
      rw [div_le_iff₀ hbeta_pos]
      have heq : 2 * Real.sqrt (Real.log (n : ℝ)) / (alpha * c_tau) * beta n
          = 2 * Real.sqrt (Real.log (n : ℝ)) * beta n / (alpha * c_tau) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]; ring
      rw [heq, le_div_iff₀ hca]
      calc (2 : ℝ) * (alpha * c_tau) ≤ 2 * (beta n * Real.sqrt (Real.log (n : ℝ))) :=
            mul_le_mul_of_nonneg_left hmul (by norm_num)
        _ = 2 * Real.sqrt (Real.log (n : ℝ)) * beta n := by ring
    have hsle : Real.sqrt (Real.log (n : ℝ)) ≤ Real.log (n : ℝ) := by
      have h1' : Real.sqrt (Real.log (n : ℝ)) * 1
          ≤ Real.sqrt (Real.log (n : ℝ)) * Real.sqrt (Real.log (n : ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.one_le_sqrt.mpr hu1) hsq.le
      rw [mul_one] at h1'
      have h2'' : Real.sqrt (Real.log (n : ℝ)) * Real.sqrt (Real.log (n : ℝ))
          = Real.log (n : ℝ) := by
        rw [← pow_two, Real.sq_sqrt hupos.le]
      rwa [h2''] at h1'
    have h3 : 2 * Real.sqrt (Real.log (n : ℝ)) / (alpha * c_tau)
        ≤ 2 * Real.log (n : ℝ) / (alpha * c_tau) := by
      have hA : (0 : ℝ) ≤ 2 / (alpha * c_tau) := by positivity
      calc 2 * Real.sqrt (Real.log (n : ℝ)) / (alpha * c_tau)
          = (2 / (alpha * c_tau)) * Real.sqrt (Real.log (n : ℝ)) := by
            rw [div_eq_mul_inv]; ring
        _ ≤ (2 / (alpha * c_tau)) * Real.log (n : ℝ) := mul_le_mul_of_nonneg_left hsle hA
        _ = 2 * Real.log (n : ℝ) / (alpha * c_tau) := by rw [div_eq_mul_inv]; ring
    have h2' : 2 / beta n ≤ (2 / (alpha * c_tau)) * Real.log (n : ℝ) := by
      calc 2 / beta n ≤ 2 * Real.sqrt (Real.log (n : ℝ)) / (alpha * c_tau) := h2
        _ ≤ 2 * Real.log (n : ℝ) / (alpha * c_tau) := h3
        _ = (2 / (alpha * c_tau)) * Real.log (n : ℝ) := by rw [div_eq_mul_inv]; ring
    rw [hq_def n]
    apply max_le
    · calc 2 / beta n ≤ (2 / (alpha * c_tau)) * Real.log (n : ℝ) := h2'
        _ ≤ (3 + 2 / (alpha * c_tau)) * Real.log (n : ℝ) := by
            apply mul_le_mul_of_nonneg_right (by linarith) hupos.le
    · apply max_le
      · have hC1 : (1 : ℝ) ≤ 3 + 2 / (alpha * c_tau) := by
          have hpos2 : (0 : ℝ) < 2 / (alpha * c_tau) := by positivity
          linarith
        exact le_mul_of_one_le_left hupos.le hC1
      · have hC3 : (3 : ℝ) ≤ 3 + 2 / (alpha * c_tau) := by
          have hpos2 : (0 : ℝ) < 2 / (alpha * c_tau) := by positivity
          linarith
        calc (3 : ℝ) = 3 * 1 := by ring
          _ ≤ 3 * Real.log (n : ℝ) := mul_le_mul_of_nonneg_left hu1 (by norm_num)
          _ ≤ (3 + 2 / (alpha * c_tau)) * Real.log (n : ℝ) :=
              mul_le_mul_of_nonneg_right hC3 hupos.le
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2half : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h1 : Real.log ((2 : ℝ)⁻¹) ≤ (2 : ℝ)⁻¹ - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    have h2 : Real.log ((2 : ℝ)⁻¹) = -Real.log 2 := Real.log_inv 2
    have h3 : ((2 : ℝ)⁻¹) = 1 / 2 := by norm_num
    linarith
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have h : (1 : ℕ) ≤ n := le_trans hn_tau hntau
    have h2 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
    linarith
  have hsqrtpos : 0 < Real.sqrt (Real.log (n : ℝ)) := Real.sqrt_pos.mpr hupos
  have hsqrt24 : (24 : ℝ) ≤ Real.sqrt (Real.log (n : ℝ)) := by
    have h1 : Real.sqrt (576 : ℝ) ≤ Real.sqrt (Real.log (n : ℝ)) :=
      Real.sqrt_le_sqrt (by linarith : (576 : ℝ) ≤ Real.log (n : ℝ))
    have h2 : Real.sqrt (576 : ℝ) = 24 := by
      rw [show (576 : ℝ) = 24 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith
  have hsqr : Real.sqrt (Real.log (n : ℝ)) * Real.sqrt (Real.log (n : ℝ)) = Real.log (n : ℝ) := by
    rw [← pow_two, Real.sq_sqrt hupos.le]
  have hloglog : Real.log (Real.log (n : ℝ)) ≤ 2 * Real.sqrt (Real.log (n : ℝ)) := by
    have h1 : Real.log (Real.sqrt (Real.log (n : ℝ))) = Real.log (Real.log (n : ℝ)) / 2 :=
      Real.log_sqrt hupos.le
    have h2 : Real.log (Real.sqrt (Real.log (n : ℝ))) ≤ Real.sqrt (Real.log (n : ℝ)) - 1 :=
      Real.log_le_sub_one_of_pos hsqrtpos
    linarith
  have hA1 : 3 * Real.log (Real.log (n : ℝ)) ≤ (Real.log 2 / 2) * Real.log (n : ℝ) := by
    have h4 : 6 * Real.sqrt (Real.log (n : ℝ)) ≤ (1 / 4) * Real.log (n : ℝ) := by
      have h := mul_le_mul_of_nonneg_right hsqrt24 hsqrtpos.le
      rw [hsqr] at h
      linarith
    have h5 : (1 / 4 : ℝ) * Real.log (n : ℝ) ≤ (Real.log 2 / 2) * Real.log (n : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) hupos.le
    linarith
  have hpow3 : Real.log ((Real.log (n : ℝ)) ^ (3 : ℕ)) = 3 * Real.log (Real.log (n : ℝ)) := by
    have huu : Real.log (Real.log (n : ℝ) * Real.log (n : ℝ)) = 2 * Real.log (Real.log (n : ℝ)) := by
      rw [Real.log_mul (ne_of_gt hupos) (ne_of_gt hupos)]
      ring
    have hp3 : ((Real.log (n : ℝ)) ^ (3 : ℕ)) = Real.log (n : ℝ) * Real.log (n : ℝ) * Real.log (n : ℝ) := by
      ring
    rw [hp3, Real.log_mul (mul_ne_zero (ne_of_gt hupos) (ne_of_gt hupos)) (ne_of_gt hupos), huu]
    ring
  have hbase : (0 : ℝ) < 2 / Real.log 2 := div_pos (by norm_num) hlog2pos
  have hua : 2 / Real.log 2 ≤ (Real.log (n : ℝ)) ^ a := by
    have h1 : ((2 / Real.log 2) ^ (1 / a)) ^ a = 2 / Real.log 2 := by
      rw [← Real.rpow_mul hbase.le, one_div, inv_mul_cancel₀ (ne_of_gt ha0), Real.rpow_one]
    have h2 : ((2 / Real.log 2) ^ (1 / a)) ^ a ≤ (Real.log (n : ℝ)) ^ a :=
      Real.rpow_le_rpow (Real.rpow_pos_of_pos hbase _).le (le_trans hUa hlogU) ha0.le
    linarith
  have hhalf : 1 / (Real.log (n : ℝ)) ^ a ≤ Real.log 2 / 2 := by
    have hle : 1 ≤ Real.log 2 / 2 * (Real.log (n : ℝ)) ^ a := by
      have h2 : 2 ≤ (Real.log (n : ℝ)) ^ a * Real.log 2 := (div_le_iff₀ hlog2pos).mp hua
      have e : Real.log 2 / 2 * (Real.log (n : ℝ)) ^ a
          = ((Real.log (n : ℝ)) ^ a * Real.log 2) / 2 := by
        rw [div_eq_mul_inv, div_eq_mul_inv]; ring
      rw [e, le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      linarith
    rw [div_le_iff₀ (Real.rpow_pos_of_pos hupos a)]
    linarith
  have hlogx : Real.log ((n : ℝ) ^ (1 / (Real.log (n : ℝ)) ^ a)) = (Real.log (n : ℝ)) ^ (1 - a) := by
    rw [Real.log_rpow hnpos]
    have hsub : (Real.log (n : ℝ)) ^ (1 - a) = Real.log (n : ℝ) / (Real.log (n : ℝ)) ^ a := by
      rw [Real.rpow_sub hupos, Real.rpow_one]
    rw [hsub, div_eq_mul_inv, div_eq_mul_inv]
    ring
  have hexpa : (0 : ℝ) < 1 / 2 - a := by linarith
  have hu3ge2 : (2 : ℝ) ≤ (Real.log (n : ℝ)) ^ (3 : ℕ) := by
    have h2u : (2 : ℝ) ≤ Real.log (n : ℝ) := by linarith
    have h4 : (2 : ℝ) * 2 ≤ Real.log (n : ℝ) * Real.log (n : ℝ) :=
      mul_le_mul h2u h2u (by norm_num) hupos.le
    have h8 : (2 : ℝ) * 2 * 2 ≤ (Real.log (n : ℝ) * Real.log (n : ℝ)) * Real.log (n : ℝ) :=
      mul_le_mul h4 h2u (by norm_num) (mul_nonneg hupos.le hupos.le)
    have hp3' : (Real.log (n : ℝ)) ^ (3 : ℕ)
        = (Real.log (n : ℝ) * Real.log (n : ℝ)) * Real.log (n : ℝ) := by ring
    rw [hp3']
    linarith
  have hident3 : ((Real.log (n : ℝ)) ^ (3 : ℕ)) ^ ((1 : ℝ) / 3) = Real.log (n : ℝ) := by
    have hcube : ((Real.log (n : ℝ)) ^ (3 : ℕ) : ℝ) = (Real.log (n : ℝ)) ^ ((3 : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
    rw [hcube, ← Real.rpow_mul hupos.le]
    have h31 : ((3 : ℕ) : ℝ) * (1 / 3) = 1 := by norm_num
    rw [h31, Real.rpow_one]


  have hlogkTop : Real.log (k n : ℝ) ≤ Real.log 2 * Real.log (n : ℝ) := by
    have hk1 : (1 : ℝ) ≤ (k n : ℝ) := by
      have h : (1 : ℝ) ≤ (L n : ℝ) := by exact_mod_cast hL1
      have h2 : (L n : ℝ) ≤ (k n : ℝ) := by exact_mod_cast hLk
      linarith
    have hkpos : (0 : ℝ) < (k n : ℝ) := by linarith
    have hL1R : (0 : ℝ) ≤ (L n : ℝ) := by
      have h : (1 : ℝ) ≤ (L n : ℝ) := by exact_mod_cast hL1
      linarith
    have hpn0 : (0 : ℝ) ≤ (p n : ℝ) := by linarith
    have hlogk : Real.log (k n : ℝ) ≤ Real.log 2 * Real.log (n : ℝ) := by
      clear hU hU10000 hUa hUb hlogU hM hlog_ge hn hnM hntau hp hp1 hLp hkp hq3 hqlog hq2
        hqC hca hbeta_pos hlog2half hsqrtpos hsqrt24 hsqr hloglog hbase hua hexpa hk1 hL1 hLk
        htau0 htau1 hbeta_def htau_cond hident3

      have hLbound : (L n : ℝ) ≤ (Real.log (n : ℝ)) ^ (3 : ℕ) + 2 := by
        have hc := Nat.ceil_lt_add_one
          (a := min (max (1 : ℝ) ((Real.log (n : ℝ)) ^ (3 : ℕ))) ((p n : ℝ)))
          (le_min (le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left _ _)) hpn0)
        rw [← hL_def n] at hc
        have hA' : max (1 : ℝ) ((Real.log (n : ℝ)) ^ (3 : ℕ)) ≤ (Real.log (n : ℝ)) ^ (3 : ℕ) + 1 := by
          apply max_le
          · have h3 := pow_nonneg hupos.le (3 : ℕ)
            linarith
          · linarith
        have hm : min (max (1 : ℝ) ((Real.log (n : ℝ)) ^ (3 : ℕ))) ((p n : ℝ))
            ≤ (Real.log (n : ℝ)) ^ (3 : ℕ) + 1 :=
          le_trans (min_le_left _ _) hA'
        linarith
      have hkbound : (k n : ℝ) ≤ 2 * max ((Real.log (n : ℝ)) ^ (3 : ℕ) + 2)
          (Real.rpow (n : ℝ) (1 / Real.rpow (Real.log (n : ℝ)) a)) := by
        have hc := Nat.ceil_lt_add_one
          (a := min (max (L n : ℝ) (Real.rpow (n : ℝ) (1 / Real.rpow (Real.log (n : ℝ)) a)))
            ((p n : ℝ)))
          (le_min (le_trans hL1R (le_max_left _ _)) hpn0)
        rw [← hk_def n] at hc
        have h4 : max (L n : ℝ) (Real.rpow (n : ℝ) (1 / Real.rpow (Real.log (n : ℝ)) a))
            ≤ max ((Real.log (n : ℝ)) ^ (3 : ℕ) + 2)
                (Real.rpow (n : ℝ) (1 / Real.rpow (Real.log (n : ℝ)) a)) :=
          max_le_max hLbound le_rfl
        have hm : min (max (L n : ℝ) (Real.rpow (n : ℝ) (1 / Real.rpow (Real.log (n : ℝ)) a)))
            ((p n : ℝ)) ≤ max ((Real.log (n : ℝ)) ^ (3 : ℕ) + 2)
                (Real.rpow (n : ℝ) (1 / Real.rpow (Real.log (n : ℝ)) a)) :=
          le_trans (min_le_left _ _) h4
        have hW1 : (1 : ℝ) ≤ max ((Real.log (n : ℝ)) ^ (3 : ℕ) + 2)
            (Real.rpow (n : ℝ) (1 / Real.rpow (Real.log (n : ℝ)) a)) := by
          have h3 := pow_nonneg hupos.le (3 : ℕ)
          linarith [le_max_left ((Real.log (n : ℝ)) ^ (3 : ℕ) + 2)
            (Real.rpow (n : ℝ) (1 / Real.rpow (Real.log (n : ℝ)) a))]
        linarith
      have hWpos : (0 : ℝ) < max ((Real.log (n : ℝ)) ^ (3 : ℕ) + 2)
          (Real.rpow (n : ℝ) (1 / Real.rpow (Real.log (n : ℝ)) a)) := by
        have h3 := pow_nonneg hupos.le (3 : ℕ)
        linarith [le_max_left ((Real.log (n : ℝ)) ^ (3 : ℕ) + 2)
          (Real.rpow (n : ℝ) (1 / Real.rpow (Real.log (n : ℝ)) a))]
      have hkl : Real.log (k n : ℝ) ≤ Real.log 2 + Real.log (max ((Real.log (n : ℝ)) ^ (3 : ℕ) + 2)
          (Real.rpow (n : ℝ) (1 / Real.rpow (Real.log (n : ℝ)) a))) := by
        have h := Real.log_le_log hkpos hkbound
        rwa [Real.log_mul (by norm_num) (ne_of_gt hWpos)] at h
      have hlogW : Real.log (max ((Real.log (n : ℝ)) ^ (3 : ℕ) + 2)
            (Real.rpow (n : ℝ) (1 / Real.rpow (Real.log (n : ℝ)) a)))
          ≤ max (Real.log ((Real.log (n : ℝ)) ^ (3 : ℕ) + 2))
              (Real.log (Real.rpow (n : ℝ) (1 / Real.rpow (Real.log (n : ℝ)) a))) := by
        rcases le_total ((Real.log (n : ℝ)) ^ (3 : ℕ) + 2)
          (Real.rpow (n : ℝ) (1 / Real.rpow (Real.log (n : ℝ)) a)) with h | h
        · rw [max_eq_right h]; exact le_max_right _ _
        · rw [max_eq_left h]; exact le_max_left _ _
      have hlogA : Real.log ((Real.log (n : ℝ)) ^ (3 : ℕ) + 2)
          ≤ Real.log 2 + (Real.log 2 / 2) * Real.log (n : ℝ) := by
        have hpow2 : (2 : ℝ) ≤ (Real.log (n : ℝ)) ^ (3 : ℕ) := hu3ge2
        have hApos : (0 : ℝ) < (Real.log (n : ℝ)) ^ (3 : ℕ) + 2 := by linarith
        have hle : (Real.log (n : ℝ)) ^ (3 : ℕ) + 2 ≤ 2 * (Real.log (n : ℝ)) ^ (3 : ℕ) := by linarith
        have h1 := Real.log_le_log hApos hle
        have h2 : Real.log (2 * (Real.log (n : ℝ)) ^ (3 : ℕ))
            = Real.log 2 + 3 * Real.log (Real.log (n : ℝ)) := by
          rw [Real.log_mul (by norm_num) (ne_of_gt (pow_pos hupos 3)), hpow3]
        linarith [h1, h2, hA1]
      have hlogX : Real.log (Real.rpow (n : ℝ) (1 / Real.rpow (Real.log (n : ℝ)) a))
          ≤ (Real.log 2 / 2) * Real.log (n : ℝ) := by
        have h1 : Real.log (Real.rpow (n : ℝ) (1 / Real.rpow (Real.log (n : ℝ)) a))
            = (Real.log (n : ℝ)) ^ (1 - a) := hlogx
        have heq2 : (Real.log (n : ℝ)) ^ (1 - a)
            = (1 / (Real.log (n : ℝ)) ^ a) * Real.log (n : ℝ) := by
          rw [Real.rpow_sub hupos, Real.rpow_one, div_eq_mul_inv, div_eq_mul_inv]
          ring
        rw [h1, heq2]
        exact mul_le_mul_of_nonneg_right hhalf hupos.le
      have hmaxle : max (Real.log ((Real.log (n : ℝ)) ^ (3 : ℕ) + 2))
            (Real.log (Real.rpow (n : ℝ) (1 / Real.rpow (Real.log (n : ℝ)) a)))
          ≤ Real.log 2 + (Real.log 2 / 2) * Real.log (n : ℝ) := by
        apply max_le
        · exact hlogA
        · linarith [hlogX]
      have hfin : Real.log (k n : ℝ)
          ≤ Real.log 2 + (Real.log 2 + (Real.log 2 / 2) * Real.log (n : ℝ)) := by
        linarith [hkl, hlogW, hmaxle]
      have hkey : 2 * Real.log 2 ≤ (Real.log 2 / 2) * Real.log (n : ℝ) := by
        have h1 : (4 : ℝ) * Real.log 2 ≤ Real.log (n : ℝ) * Real.log 2 :=
          mul_le_mul_of_nonneg_right (by linarith : (4 : ℝ) ≤ Real.log (n : ℝ)) hlog2pos.le
        have h2 : (Real.log 2 / 2) * Real.log (n : ℝ) = (Real.log (n : ℝ) * Real.log 2) / 2 := by
          rw [div_eq_mul_inv, div_eq_mul_inv]; ring
        linarith [h1, h2]
      linarith [hfin, hkey]
    exact hlogk
  have hexp_gen : ∀ t : ℝ, 0 < t → Real.log (n : ℝ) ≤ t →
      Real.rpow (k n : ℝ) (1 / t) ≤ 2 := by
    intro t htpos htu
    have hk1 : (1 : ℝ) ≤ (k n : ℝ) := by
      have h : (1 : ℝ) ≤ (L n : ℝ) := by exact_mod_cast hL1
      have h2 : (L n : ℝ) ≤ (k n : ℝ) := by exact_mod_cast hLk
      linarith
    have hkpos : (0 : ℝ) < (k n : ℝ) := by linarith
    have hkr : Real.rpow (k n : ℝ) (1 / t) = Real.exp (Real.log (k n : ℝ) * (1 / t)) :=
      Real.rpow_def_of_pos hkpos _
    rw [hkr]
    have harg : Real.log (k n : ℝ) * (1 / t) ≤ Real.log 2 := by
      have h1 : Real.log (k n : ℝ) ≤ Real.log 2 * t := by
        have h2 : Real.log 2 * Real.log (n : ℝ) ≤ Real.log 2 * t :=
          mul_le_mul_of_nonneg_left htu hlog2pos.le
        linarith [hlogkTop, h2]
      have h3 : Real.log (k n : ℝ) * (1 / t) ≤ (Real.log 2 * t) * (1 / t) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      have h4 : (Real.log 2 * t) * (1 / t) = Real.log 2 := by
        rw [one_div, mul_assoc, mul_inv_cancel₀ (ne_of_gt htpos), mul_one]
      linarith [h3, h4]
    calc Real.exp (Real.log (k n : ℝ) * (1 / t)) ≤ Real.exp (Real.log 2) :=
          Real.exp_le_exp.mpr harg
      _ = 2 := Real.exp_log (by norm_num)

  refine ⟨⟨hL1, hLk, hkp, hbeta_pos, hu1⟩, ⟨hq3, hqlog, hq2, hqC⟩, ⟨?_, ?_⟩, ?_⟩
  · exact hexp_gen (Real.log (n : ℝ)) hupos le_rfl
  · exact hexp_gen (q n) (lt_of_lt_of_le hupos hqlog) hqlog
  · intro hk_lt
    have hk_lt_R : (k n : ℝ) < (p n : ℝ) := by exact_mod_cast hk_lt
    have hin : min (max (L n : ℝ) (Real.rpow (n : ℝ) (1 / Real.rpow (Real.log (n : ℝ)) a)))
        ((p n : ℝ)) ≤ (k n : ℝ) := by
      rw [hk_def n]
      exact Nat.le_ceil _
    have hmaxlt : max (L n : ℝ) (Real.rpow (n : ℝ) (1 / Real.rpow (Real.log (n : ℝ)) a))
        < (p n : ℝ) :=
      (min_lt_iff.mp (lt_of_le_of_lt hin hk_lt_R)).resolve_right (lt_irrefl _)
    have hLlt : (L n : ℝ) < (p n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hmaxlt
    have hLle : min (max (1 : ℝ) ((Real.log (n : ℝ)) ^ (3 : ℕ))) ((p n : ℝ)) ≤ (L n : ℝ) := by
      rw [hL_def n]
      exact Nat.le_ceil _
    have hmax1lt : max (1 : ℝ) ((Real.log (n : ℝ)) ^ (3 : ℕ)) < (p n : ℝ) :=
      (min_lt_iff.mp (lt_of_le_of_lt hLle hLlt)).resolve_right (lt_irrefl _)
    have hu3ltp : (Real.log (n : ℝ)) ^ (3 : ℕ) < (p n : ℝ) :=
      lt_of_le_of_lt (le_max_right _ _) hmax1lt
    have h1u3 : (1 : ℝ) ≤ (Real.log (n : ℝ)) ^ (3 : ℕ) :=
      le_trans (by norm_num : (1 : ℝ) ≤ 2) hu3ge2
    have hu3big : (1 : ℝ) < (Real.log (n : ℝ)) ^ (3 : ℕ) :=
      lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hu3ge2
    have hLceil : L n = Nat.ceil ((Real.log (n : ℝ)) ^ (3 : ℕ)) := by
      rw [hL_def n]
      congr 1
      rw [max_eq_right h1u3, min_eq_left (le_of_lt hu3ltp)]
    refine ⟨hLceil, ?_, ?_⟩
    · rw [hLceil]
      have hnotle : ¬ (Nat.ceil ((Real.log (n : ℝ)) ^ (3 : ℕ)) ≤ 1) := by
        intro hc
        have h' : (Real.log (n : ℝ)) ^ (3 : ℕ) ≤ (1 : ℝ) := by
          simpa using (Nat.ceil_le.mp hc)
        exact absurd h' (not_le.mpr hu3big)
      omega
    · have hu3le : (Real.log (n : ℝ)) ^ (3 : ℕ) ≤ (L n : ℝ) := by
        rw [hLceil]
        exact Nat.le_ceil _
      have hcube : ((Real.log (n : ℝ)) ^ (3 : ℕ) : ℝ) = (Real.log (n : ℝ)) ^ ((3 : ℕ) : ℝ) := by
        rw [Real.rpow_natCast]
      have hident : ((Real.log (n : ℝ)) ^ (3 : ℕ)) ^ ((1 : ℝ) / 3) = Real.log (n : ℝ) := by
        rw [hcube, ← Real.rpow_mul hupos.le]
        have h31 : ((3 : ℕ) : ℝ) * (1 / 3) = 1 := by norm_num
        rw [h31, Real.rpow_one]
      calc Real.log (n : ℝ) = ((Real.log (n : ℝ)) ^ (3 : ℕ)) ^ ((1 : ℝ) / 3) := hident.symm
        _ ≤ (L n : ℝ) ^ ((1 : ℝ) / 3) :=
            Real.rpow_le_rpow (pow_nonneg hupos.le 3) hu3le (by norm_num)
  /- @proof-region region.target-node.session.596a15437bd809ff end -/

end

end Statlib.Imported

