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
theorem statopia_math_node_4249859734_bd75d9c7 : ∀ (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1 / 2)
    (alpha : ℝ) (halpha : 0 < alpha)
    (p : ℕ → ℕ) (hp : ∀ n, 1 ≤ p n)
    (L : ℕ → ℕ)
    (hL_def : ∀ n, L n = Nat.ceil (min (max 1 ((Real.log (n : ℝ)) ^ (3 : ℕ))) ((p n : ℝ))))
    (k : ℕ → ℕ)
    (hk_def : ∀ n, k n = Nat.ceil
      (min (max (L n : ℝ) (Real.rpow (n : ℝ) (1 / Real.rpow (Real.log (n : ℝ)) a))) ((p n : ℝ))))
    (tau : ℕ → ℝ) (htau0 : ∀ n, 0 ≤ tau n) (htau1 : ∀ n, tau n < 1)
    (beta : ℕ → ℝ) (hbeta_def : ∀ n, beta n = alpha * (1 - tau n))
    (c : ℝ) (hc : 0 < c) (n₁ : ℕ)
    (hn₁ : ∀ n : ℕ, n₁ ≤ n → (1 : ℝ) ≤ c * ((1 - tau n) * Real.sqrt (Real.log (n : ℝ)))),
    ∀ᶠ n : ℕ in Filter.atTop,
      ((1 : ℝ) ≤ Real.log (n : ℝ)) ∧
      (2 / beta n ≤ (2 * c / alpha) * Real.log (n : ℝ)) ∧
      (Real.log (n : ℝ) + 4 ≤ Real.sqrt (n : ℝ)) ∧
      ((2 * c / alpha) * Real.log (n : ℝ) ≤ Real.sqrt (n : ℝ)) ∧
      ((3 : ℝ) ≤ Real.sqrt (n : ℝ)) ∧
      ((k n : ℝ) ≤ Real.exp 2 * Real.sqrt (n : ℝ)) := by
  /- @proof-region region.target-node.session.c431f441c09a2503 begin -/
  intro a ha0 ha1 alpha halpha p hp L hL_def k hk_def tau htau0 htau1 beta hbeta_def c hc n₁ hn₁
  have h1 : ∀ᶠ n : ℕ in Filter.atTop, (1 : ℝ) ≤ Real.log (n : ℝ) := by
    have hcast : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop
    have h := (Real.tendsto_log_atTop.comp hcast).eventually (eventually_ge_atTop 1)
    simpa using h
  have h5 : ∀ᶠ n : ℕ in Filter.atTop, (3 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    filter_upwards [eventually_ge_atTop 9] with n hn
    have hn' : (9 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h9 : Real.sqrt 9 = (3 : ℝ) := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
      norm_num
    rw [← h9]
    exact Real.sqrt_le_sqrt hn'
  have hrpow_one : ∀ x : ℝ, x ^ (1:ℝ) = x := fun x => by simpa using Real.rpow_natCast x 1
  have h2 : ∀ᶠ n : ℕ in Filter.atTop, 2 / beta n ≤ (2 * c / alpha) * Real.log (n : ℝ) := by
    filter_upwards [h1, eventually_ge_atTop n₁] with n hlog1 hn1
    have hL : (1:ℝ) ≤ Real.log (n:ℝ) := hlog1
    have hdpos : (0:ℝ) < 1 - tau n := by
      have := htau1 n
      linarith
    have hdnn : (0:ℝ) ≤ 1 - tau n := le_of_lt hdpos
    have hsq : Real.sqrt (Real.log (n:ℝ)) ≤ Real.log (n:ℝ) := by
      have h := Real.rpow_le_rpow_of_exponent_le (x := Real.log (n:ℝ)) (y := (1/2:ℝ))
        (z := (1:ℝ)) hL (by norm_num)
      rw [← Real.sqrt_eq_rpow, hrpow_one] at h
      exact h
    have hbase : (1:ℝ) ≤ c * ((1 - tau n) * Real.sqrt (Real.log (n:ℝ))) := hn₁ n hn1
    have hstep1 : (1 - tau n) * Real.sqrt (Real.log (n:ℝ)) ≤ (1 - tau n) * Real.log (n:ℝ) :=
      mul_le_mul_of_nonneg_left hsq hdnn
    have hstep2 : c * ((1 - tau n) * Real.sqrt (Real.log (n:ℝ)))
        ≤ c * ((1 - tau n) * Real.log (n:ℝ)) := mul_le_mul_of_nonneg_left hstep1 (le_of_lt hc)
    have hgoal1 : (1:ℝ) ≤ c * ((1 - tau n) * Real.log (n:ℝ)) := le_trans hbase hstep2
    have hbetapos : (0:ℝ) < beta n := by
      rw [hbeta_def]
      exact mul_pos halpha hdpos
    rw [div_le_iff₀ hbetapos]
    have hA : (2*c/alpha) * Real.log (n:ℝ) * (alpha*(1 - tau n))
        = 2 * (c * ((1 - tau n) * Real.log (n:ℝ))) := by
      have ha_ne : alpha ≠ 0 := ne_of_gt halpha
      field_simp
    rw [hbeta_def, hA]
    linarith
  have h3 : ∀ᶠ n : ℕ in Filter.atTop, Real.log (n : ℝ) + 4 ≤ Real.sqrt (n : ℝ) := by
    filter_upwards [eventually_ge_atTop 4096] with n hn
    have hnR : (0:ℝ) ≤ (n:ℝ) := by positivity
    have h4096 : (4096:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have hmn : (0:ℝ) ≤ (n:ℝ)^(1/4:ℝ) := Real.rpow_nonneg hnR _
    have h64 : Real.sqrt 64 = (8:ℝ) := by
      rw [show (64:ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
      norm_num
    have h4096' : Real.sqrt 4096 = (64:ℝ) := by
      have h := Real.sqrt_mul_self (show (0:ℝ) ≤ 64 by norm_num)
      rw [show (64:ℝ) * 64 = 4096 by norm_num] at h
      exact h
    have hss : Real.sqrt (Real.sqrt (n:ℝ)) = (n:ℝ)^(1/4:ℝ) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hnR (1/2:ℝ) (1/2:ℝ),
        show (1/2:ℝ)*(1/2) = 1/4 by norm_num]
    have hmg : (8:ℝ) ≤ (n:ℝ)^(1/4:ℝ) := by
      rw [← hss, ← h64, Real.sqrt_le_sqrt_iff (Real.sqrt_nonneg (n:ℝ)), ← h4096',
        Real.sqrt_le_sqrt_iff hnR]
      exact h4096
    have hmul : (n:ℝ)^(1/4:ℝ) * (n:ℝ)^(1/4:ℝ) = Real.sqrt (n:ℝ) := by
      rw [← hss]
      exact Real.mul_self_sqrt (Real.sqrt_nonneg (n:ℝ))
    have hlog : Real.log (n:ℝ) ≤ 4 * (n:ℝ)^(1/4:ℝ) := by
      have h := Real.log_le_rpow_div (x := (n:ℝ)) (ε := (1/4:ℝ)) hnR (by norm_num)
      have h' : (n:ℝ)^(1/4:ℝ) / (1/4:ℝ) = 4 * (n:ℝ)^(1/4:ℝ) := by ring
      linarith [h, h']
    have h8m : 8 * (n:ℝ)^(1/4:ℝ) ≤ Real.sqrt (n:ℝ) := by
      rw [← hmul]
      exact mul_le_mul_of_nonneg_right hmg hmn
    have h8 : (8:ℝ) ≤ Real.sqrt (n:ℝ) := by
      rw [← h64]
      exact Real.sqrt_le_sqrt (by linarith : (64:ℝ) ≤ (n:ℝ))
    have hhalf : Real.log (n:ℝ) ≤ Real.sqrt (n:ℝ) / 2 := by linarith [hlog, h8m]
    linarith [hhalf, h8, Real.sqrt_nonneg (n:ℝ)]
  have h4 : ∀ᶠ n : ℕ in Filter.atTop, (2 * c / alpha) * Real.log (n : ℝ) ≤ Real.sqrt (n : ℝ) := by
    have hK : (0:ℝ) < 2 * c / alpha := by positivity
    set C : ℝ := 4 * (2 * c / alpha) with hC
    have hCpos : (0:ℝ) < C := by rw [hC]; positivity
    filter_upwards [eventually_ge_atTop (Nat.ceil (C ^ (4:ℝ)) + 1)] with n hn
    have hnR : (0:ℝ) ≤ (n:ℝ) := by positivity
    have hmn : (0:ℝ) ≤ (n:ℝ)^(1/4:ℝ) := Real.rpow_nonneg hnR _
    have hm4 : ((n:ℝ)^(1/4:ℝ)) ^ (4:ℝ) = (n:ℝ) := by
      rw [← Real.rpow_mul hnR (1/4:ℝ) (4:ℝ), show (1/4:ℝ)*4 = 1 by norm_num]
      exact hrpow_one _
    have hCm : C ≤ (n:ℝ)^(1/4:ℝ) := by
      refine (Real.rpow_le_rpow_iff (le_of_lt hCpos) hmn (by norm_num : (0:ℝ) < 4)).mp ?_
      have hceil : C ^ (4:ℝ) ≤ (n:ℝ) := by
        have h1 : C ^ (4:ℝ) ≤ ((Nat.ceil (C ^ (4:ℝ)) : ℕ) : ℝ) := Nat.le_ceil _
        have h2 : Nat.ceil (C ^ (4:ℝ)) ≤ n := by omega
        have h3 : ((Nat.ceil (C ^ (4:ℝ)) : ℕ) : ℝ) ≤ (n:ℝ) := by exact_mod_cast h2
        linarith [h1, h3]
      rw [hm4]
      exact hceil
    have hss : Real.sqrt (Real.sqrt (n:ℝ)) = (n:ℝ)^(1/4:ℝ) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hnR (1/2:ℝ) (1/2:ℝ),
        show (1/2:ℝ)*(1/2) = 1/4 by norm_num]
    have hmul : (n:ℝ)^(1/4:ℝ) * (n:ℝ)^(1/4:ℝ) = Real.sqrt (n:ℝ) := by
      rw [← hss]
      exact Real.mul_self_sqrt (Real.sqrt_nonneg (n:ℝ))
    have hlog : Real.log (n:ℝ) ≤ 4 * (n:ℝ)^(1/4:ℝ) := by
      have h := Real.log_le_rpow_div (x := (n:ℝ)) (ε := (1/4:ℝ)) hnR (by norm_num)
      have h' : (n:ℝ)^(1/4:ℝ) / (1/4:ℝ) = 4 * (n:ℝ)^(1/4:ℝ) := by ring
      linarith [h, h']
    have hstep : C * (n:ℝ)^(1/4:ℝ) ≤ Real.sqrt (n:ℝ) := by
      rw [← hmul]
      exact mul_le_mul_of_nonneg_right hCm hmn
    have hfac : (2 * c / alpha) * Real.log (n:ℝ) ≤ C * (n:ℝ)^(1/4:ℝ) := by
      have h1 : (0:ℝ) ≤ 2 * c / alpha := le_of_lt hK
      have h2 : (2*c/alpha) * Real.log (n:ℝ) ≤ (2*c/alpha) * (4 * (n:ℝ)^(1/4:ℝ)) :=
        mul_le_mul_of_nonneg_left hlog h1
      have h3 : (2*c/alpha) * (4 * (n:ℝ)^(1/4:ℝ)) = C * (n:ℝ)^(1/4:ℝ) := by
        rw [hC]; ring
      linarith [h2, h3]
    linarith [hfac, hstep]
  have h6 : ∀ᶠ n : ℕ in Filter.atTop, (k n : ℝ) ≤ Real.exp 2 * Real.sqrt (n : ℝ) := by
    have hlogbig : ∀ᶠ n : ℕ in Filter.atTop, Real.rpow 2 (1/a) ≤ Real.log (n : ℝ) := by
      have hcast : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
        tendsto_natCast_atTop_atTop
      exact (Real.tendsto_log_atTop.comp hcast).eventually (eventually_ge_atTop (Real.rpow 2 (1/a)))
    filter_upwards [h1, h5, hlogbig,
      eventually_ge_atTop (max (Nat.ceil (Real.rpow 1728 (4:ℝ)) + 1) 1)] with n hlog1 hsqrt3 hlogbig_n hnN
    have hn1n : 1 ≤ n := le_trans (le_max_right _ _) hnN
    have hB2 : Nat.ceil (Real.rpow 1728 (4:ℝ)) + 1 ≤ n := le_trans (le_max_left _ _) hnN
    have hnR : (0:ℝ) ≤ (n:ℝ) := by positivity
    have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1n
    have hnpos : (0:ℝ) < (n:ℝ) := by linarith
    have hlog0 : (0:ℝ) ≤ Real.log (n:ℝ) := Real.log_natCast_nonneg n
    have hv : (0:ℝ) ≤ (Real.log (n:ℝ))^(3:ℕ) := pow_nonneg hlog0 3
    have hpow2 : (2:ℝ) ≤ Real.rpow (Real.log (n:ℝ)) a := by
      have hbase : ((2:ℝ) ^ (1/a)) ^ a = 2 := by
        rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) (1/a) a,
          show (1/a) * a = 1 by field_simp, hrpow_one]
      have hmono : ((2:ℝ) ^ (1/a)) ^ a ≤ (Real.log (n:ℝ)) ^ a :=
        Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) _) hlogbig_n (le_of_lt ha0)
      exact le_trans hbase.ge hmono
    have hlog12 : Real.log (n:ℝ) ≤ 12 * (n:ℝ)^(1/12:ℝ) := by
      have h := Real.log_le_rpow_div (x := (n:ℝ)) (ε := (1/12:ℝ)) hnR (by norm_num)
      have h' : (n:ℝ)^(1/12:ℝ) / (1/12:ℝ) = 12 * (n:ℝ)^(1/12:ℝ) := by ring
      linarith [h, h']
    have h12nn : (0:ℝ) ≤ 12 * (n:ℝ)^(1/12:ℝ) := by positivity
    have hsquare : (Real.log (n:ℝ))^2 ≤ (12 * (n:ℝ)^(1/12:ℝ))^2 := by
      rw [pow_two, pow_two]
      exact mul_le_mul hlog12 hlog12 hlog0 h12nn
    have hcube : (Real.log (n:ℝ))^3 ≤ 1728 * ((n:ℝ)^(1/12:ℝ))^3 := by
      have h3 : (Real.log (n:ℝ))^2 * Real.log (n:ℝ)
          ≤ (12 * (n:ℝ)^(1/12:ℝ))^2 * (12 * (n:ℝ)^(1/12:ℝ)) :=
        mul_le_mul hsquare hlog12 hlog0 (pow_nonneg h12nn 2)
      have e1 : (Real.log (n:ℝ))^3 = (Real.log (n:ℝ))^2 * Real.log (n:ℝ) := by ring
      have e2 : (12 * (n:ℝ)^(1/12:ℝ))^3
          = (12 * (n:ℝ)^(1/12:ℝ))^2 * (12 * (n:ℝ)^(1/12:ℝ)) := by ring
      have e3 : (12 * (n:ℝ)^(1/12:ℝ))^3 = 1728 * ((n:ℝ)^(1/12:ℝ))^3 := by ring
      linarith [h3, e1, e2, e3]
    have hrpow3 : ((n:ℝ)^(1/12:ℝ))^3 = (n:ℝ)^(1/4:ℝ) := by
      rw [← Real.rpow_natCast ((n:ℝ)^(1/12:ℝ)) 3,
        ← Real.rpow_mul hnR (1/12:ℝ) ((3:ℕ) : ℝ),
        show (1/12:ℝ) * ((3:ℕ) : ℝ) = 1/4 by norm_num]
    have hlog3 : (Real.log (n:ℝ))^3 ≤ 1728 * (n:ℝ)^(1/4:ℝ) := by
      have h := hcube
      rw [hrpow3] at h
      exact h
    have hM4 : ((n:ℝ)^(1/4:ℝ)) ^ (4:ℝ) = (n:ℝ) := by
      rw [← Real.rpow_mul hnR (1/4:ℝ) (4:ℝ), show (1/4:ℝ)*4 = 1 by norm_num]
      exact hrpow_one _
    have hMnn : (0:ℝ) ≤ (n:ℝ)^(1/4:ℝ) := Real.rpow_nonneg hnR _
    have hM1728 : (1728:ℝ) ≤ (n:ℝ)^(1/4:ℝ) := by
      refine (Real.rpow_le_rpow_iff (by norm_num : (0:ℝ) ≤ 1728) hMnn (by norm_num : (0:ℝ) < 4)).mp ?_
      rw [hM4]
      show Real.rpow 1728 (4:ℝ) ≤ (n:ℝ)
      have hce : Real.rpow 1728 (4:ℝ) ≤ ((Nat.ceil (Real.rpow 1728 (4:ℝ)) : ℕ) : ℝ) := Nat.le_ceil _
      have h2 : Nat.ceil (Real.rpow 1728 (4:ℝ)) ≤ n := by omega
      have h3 : ((Nat.ceil (Real.rpow 1728 (4:ℝ)) : ℕ) : ℝ) ≤ (n:ℝ) := by exact_mod_cast h2
      linarith [hce, h3]
    have hMmul : (n:ℝ)^(1/4:ℝ) * (n:ℝ)^(1/4:ℝ) = Real.sqrt (n:ℝ) := by
      rw [← Real.rpow_add hnpos (1/4:ℝ) (1/4:ℝ), show (1/4:ℝ) + 1/4 = 1/2 by norm_num,
        ← Real.sqrt_eq_rpow]
    have hlog3sqrt : (Real.log (n:ℝ))^3 ≤ Real.sqrt (n:ℝ) := by
      have hstep : 1728 * (n:ℝ)^(1/4:ℝ) ≤ (n:ℝ)^(1/4:ℝ) * (n:ℝ)^(1/4:ℝ) :=
        mul_le_mul_of_nonneg_right hM1728 hMnn
      rw [hMmul] at hstep
      linarith [hlog3, hstep]
    have hYnn : (0:ℝ) ≤ Real.rpow (n:ℝ) (1 / Real.rpow (Real.log (n:ℝ)) a) := Real.rpow_nonneg hnR _
    have hexp_le : 1 / Real.rpow (Real.log (n:ℝ)) a ≤ 1/2 :=
      one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 2) hpow2
    have hY : Real.rpow (n:ℝ) (1 / Real.rpow (Real.log (n:ℝ)) a) ≤ Real.sqrt (n:ℝ) := by
      have h := Real.rpow_le_rpow_of_exponent_le (x := (n:ℝ)) hn1
        (y := 1 / Real.rpow (Real.log (n:ℝ)) a) (z := (1/2:ℝ)) hexp_le
      rwa [← Real.sqrt_eq_rpow] at h
    have hBnn : (0:ℝ) ≤ min (max (1:ℝ) ((Real.log (n:ℝ)) ^ (3:ℕ))) ((p n : ℝ)) :=
      le_min (le_trans (by norm_num : (0:ℝ) ≤ 1) (le_max_left _ _)) (by positivity)
    have hL_lt : (L n : ℝ) < (Real.log (n:ℝ))^3 + 2 := by
      have h := Nat.ceil_lt_add_one hBnn
      rw [← hL_def n] at h
      have hle : min (max (1:ℝ) ((Real.log (n:ℝ)) ^ (3:ℕ))) ((p n : ℝ))
          ≤ max (1:ℝ) ((Real.log (n:ℝ)) ^ (3:ℕ)) := min_le_left _ _
      have hmaxle : max (1:ℝ) ((Real.log (n:ℝ)) ^ (3:ℕ)) ≤ (Real.log (n:ℝ))^3 + 1 :=
        max_le (by linarith [hv]) (by linarith)
      linarith [h, hle, hmaxle]
    have hLnn : (0:ℝ) ≤ (L n : ℝ) := by positivity
    have hAnn : (0:ℝ) ≤ min (max (L n : ℝ) (Real.rpow (n:ℝ) (1 / Real.rpow (Real.log (n:ℝ)) a))) ((p n : ℝ)) :=
      le_min (le_trans hLnn (le_max_left _ _)) (by positivity)
    have hk_lt : (k n : ℝ) < max (L n : ℝ) (Real.rpow (n:ℝ) (1 / Real.rpow (Real.log (n:ℝ)) a)) + 1 := by
      have h := Nat.ceil_lt_add_one hAnn
      rw [← hk_def n] at h
      have hle : min (max (L n : ℝ) (Real.rpow (n:ℝ) (1 / Real.rpow (Real.log (n:ℝ)) a))) ((p n : ℝ))
          ≤ max (L n : ℝ) (Real.rpow (n:ℝ) (1 / Real.rpow (Real.log (n:ℝ)) a)) := min_le_left _ _
      linarith [h, hle]
    have hmaxle : max (L n : ℝ) (Real.rpow (n:ℝ) (1 / Real.rpow (Real.log (n:ℝ)) a))
        ≤ (L n : ℝ) + Real.rpow (n:ℝ) (1 / Real.rpow (Real.log (n:ℝ)) a) :=
      max_le (by linarith [hYnn]) (by linarith [hLnn])
    have hk_bound : (k n : ℝ) < (Real.log (n:ℝ))^3 + Real.rpow (n:ℝ) (1 / Real.rpow (Real.log (n:ℝ)) a) + 3 := by
      linarith [hk_lt, hmaxle, hL_lt]
    have hexp3 : (3:ℝ) ≤ Real.exp 2 := by
      have h := Real.add_one_le_exp (2:ℝ)
      linarith
    have hstep1 : (Real.log (n:ℝ))^3 + Real.rpow (n:ℝ) (1 / Real.rpow (Real.log (n:ℝ)) a) + 3 ≤ 3 * Real.sqrt (n:ℝ) := by
      linarith [hlog3sqrt, hY, hsqrt3]
    have hstep2 : 3 * Real.sqrt (n:ℝ) ≤ Real.exp 2 * Real.sqrt (n:ℝ) :=
      mul_le_mul_of_nonneg_right hexp3 (Real.sqrt_nonneg _)
    linarith [hk_bound, hstep1, hstep2]
  filter_upwards [h1, h2, h3, h4, h5, h6] with n h1n h2n h3n h4n h5n h6n
  exact ⟨h1n, h2n, h3n, h4n, h5n, h6n⟩
  /- @proof-region region.target-node.session.c431f441c09a2503 end -/

end

end Statlib.Imported

