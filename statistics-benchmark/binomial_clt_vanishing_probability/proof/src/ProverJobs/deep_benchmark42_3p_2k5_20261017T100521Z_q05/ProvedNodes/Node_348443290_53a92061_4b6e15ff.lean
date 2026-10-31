import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q05.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q05.Base

open MeasureTheory ProbabilityTheory Filter
open Msc62GroundTruth

open MeasureTheory ProbabilityTheory Filter
namespace Msc62GroundTruth

set_option autoImplicit false in
theorem statopia_math_node_348443290_53a92061 : ∀ (t : ℝ),
    Tendsto
      (fun n : ℕ =>
        Complex.exp (Complex.I * ((-(t * (n : ℝ) ^ ((1 : ℝ) / 4)) : ℝ) : ℂ)) *
          (((((1 : ℝ) - 1 / Real.sqrt (n : ℝ)) : ℝ) : ℂ) +
            (((1 / Real.sqrt (n : ℝ) : ℝ) : ℂ) *
              Complex.exp (Complex.I *
                ((t * (n : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)))) ^ n)
      atTop (nhds (Complex.exp ((-(t ^ 2) / 2 : ℝ) : ℂ))) := by
  /- @proof-region region.target-node.session.3fa6593354951bcf begin -/
  intro t
  set A : ℕ → ℂ := fun n =>
    ((((1 / Real.sqrt (n : ℝ) : ℝ)) : ℂ)) *
      (Complex.exp (Complex.I * ((t * (n : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)) - 1) with hA
  have hbase : ∀ n : ℕ,
      ((((1 : ℝ) - 1 / Real.sqrt (n : ℝ) : ℝ)) : ℂ) +
          ((((1 / Real.sqrt (n : ℝ) : ℝ)) : ℂ)) *
            Complex.exp (Complex.I * ((t * (n : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)) = 1 + A n := by
    intro n
    rw [hA]
    push_cast
    ring
  have hbound : ∀ᶠ n : ℕ in atTop, ‖A n‖ ≤ 1 / 2 := by
    filter_upwards [Filter.eventually_ge_atTop 16] with n hn
    have hn16 : (16 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hspos : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
    have hsqr : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (le_of_lt hnpos)
    have h4 : (4 : ℝ) ≤ Real.sqrt (n : ℝ) := by nlinarith
    have hEnorm :
        ‖Complex.exp (Complex.I * ((t * (n : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ))‖ = 1 := by
      rw [mul_comm]
      exact Complex.norm_exp_ofReal_mul_I _
    have hE1 :
        ‖Complex.exp (Complex.I * ((t * (n : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)) - 1‖ ≤ 2 := by
      have h :=
        norm_sub_le (Complex.exp (Complex.I * ((t * (n : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ))) 1
      rw [hEnorm, norm_one] at h
      linarith
    have hle1 : (1 : ℝ) / Real.sqrt (n : ℝ) ≤ 1 / 4 := by
      have hs : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt hspos
      field_simp
      nlinarith
    rw [hA]
    rw [norm_mul]
    have hc : ‖(((1 / Real.sqrt (n : ℝ) : ℝ)) : ℂ)‖ = 1 / Real.sqrt (n : ℝ) := by
      simp
    rw [hc]
    have hprod :
        (1 / Real.sqrt (n : ℝ)) *
            ‖Complex.exp (Complex.I * ((t * (n : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)) - 1‖ ≤
          (1 / 4) * 2 :=
      mul_le_mul hle1 hE1 (norm_nonneg _) (by norm_num)
    linarith
  have hdecay : ∀ c : ℝ, 0 < c → Tendsto (fun n : ℕ => (n : ℝ) ^ (-c)) atTop (nhds 0) := by
    intro c hc
    have hpow_atTop : Tendsto (fun n : ℕ => (n : ℝ) ^ c) atTop atTop := by
      rw [Filter.tendsto_atTop_atTop]
      intro b
      obtain ⟨N, hN⟩ := exists_nat_ge (max b 0 ^ c⁻¹)
      refine ⟨N, fun a ha => ?_⟩
      have hb0 : (0 : ℝ) ≤ max b 0 := le_max_right _ _
      have hNa : max b 0 ^ c⁻¹ ≤ (a : ℝ) := le_trans hN (by exact_mod_cast ha)
      have hb_eq : ((max b 0) ^ c⁻¹) ^ c = max b 0 := Real.rpow_inv_rpow hb0 (ne_of_gt hc)
      calc b ≤ max b 0 := le_max_left _ _
        _ = ((max b 0) ^ c⁻¹) ^ c := hb_eq.symm
        _ ≤ (a : ℝ) ^ c := Real.rpow_le_rpow (by positivity) hNa (le_of_lt hc)
    have hinv : Tendsto (fun n : ℕ => ((n : ℝ) ^ c)⁻¹) atTop (nhds 0) :=
      hpow_atTop.inv_tendsto_atTop
    refine Tendsto.congr' (Eventually.of_forall fun n => ?_) hinv
    exact (Real.rpow_neg (by positivity : (0 : ℝ) ≤ (n : ℝ)) c).symm

  have hsq : Tendsto (fun n : ℕ => (n : ℝ) * ‖A n‖ ^ 2) atTop (nhds 0) := by
    have hdec4 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ) / 4)) atTop (nhds 0) := by
      have h := hdecay ((1 : ℝ) / 4) (by norm_num)
      refine Tendsto.congr' (Eventually.of_forall fun n => ?_) h
      have hb : (-((1 : ℝ) / 4)) = (-(1 : ℝ) / 4) := by norm_num
      rw [hb]
    have hu_tend : Tendsto (fun n : ℕ => t * (n : ℝ) ^ (-(1 : ℝ) / 4)) atTop (nhds 0) := by
      have h := hdec4.const_mul t
      simpa using h
    have hbdry :
        Tendsto (fun n : ℕ => 4 * |t| ^ 2 * (n : ℝ) ^ (-((1 : ℝ) / 2))) atTop (nhds 0) := by
      have h := (hdecay ((1 : ℝ) / 2) (by norm_num)).const_mul (4 * |t| ^ 2)
      simpa using h
    refine squeeze_zero_norm' ?_ hbdry
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hu_tend) 1 (by norm_num)
    filter_upwards [Filter.eventually_ge_atTop (max N 16)] with n hn
    have hNn : N ≤ n := le_trans (le_max_left _ _) hn
    have hn16 : (16 : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_trans (le_max_right _ _) hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hspos : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
    have hsqr : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (le_of_lt hnpos)
    have hu_lt : |t * (n : ℝ) ^ (-(1 : ℝ) / 4)| < 1 := by
      have h := hN n hNn
      rwa [Real.dist_eq, sub_zero] at h
    have hxnorm :
        ‖Complex.I * ((t * (n : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)‖ =
          |t * (n : ℝ) ^ (-(1 : ℝ) / 4)| := by
      rw [norm_mul]
      have hI : ‖Complex.I‖ = 1 := by simp
      rw [hI, one_mul]
      simp
    have hx : ‖Complex.I * ((t * (n : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)‖ ≤ 1 := by
      rw [hxnorm]
      linarith
    have hEb :
        ‖Complex.exp (Complex.I * ((t * (n : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)) - 1‖ ≤
          2 * |t * (n : ℝ) ^ (-(1 : ℝ) / 4)| := by
      have h :=
        Complex.exp_bound (x := Complex.I * ((t * (n : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)) hx
          (n := 1) (by norm_num)
      have h' :
          ‖Complex.exp (Complex.I * ((t * (n : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)) - 1‖ ≤
            ‖Complex.I * ((t * (n : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)‖ * 2 := by
        simpa using h
      rw [hxnorm] at h'
      linarith
    have hAn :
        ‖A n‖ =
          (1 / Real.sqrt (n : ℝ)) *
            ‖Complex.exp (Complex.I * ((t * (n : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)) - 1‖ := by
      rw [hA, norm_mul]
      have hc : ‖(((1 / Real.sqrt (n : ℝ) : ℝ)) : ℂ)‖ = 1 / Real.sqrt (n : ℝ) := by simp
      rw [hc]
    have hsqrt_one : (n : ℝ) * (1 / Real.sqrt (n : ℝ)) ^ 2 = 1 := by
      have hs : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt hspos
      have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
      field_simp
      nlinarith [hsqr]
    have hkey :
        (n : ℝ) * ‖A n‖ ^ 2 =
          ‖Complex.exp (Complex.I * ((t * (n : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)) - 1‖ ^ 2 := by
      rw [hAn, mul_pow, ← mul_assoc, hsqrt_one, one_mul]
    have hpow2 : ((n : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2 = (n : ℝ) ^ (-((1 : ℝ) / 2)) := by
      rw [← Real.rpow_mul_natCast (le_of_lt hnpos)]
      rw [show (-(1 : ℝ) / 4) * ((2 : ℕ) : ℝ) = -((1 : ℝ) / 2) by norm_num]
    have huabs : |t * (n : ℝ) ^ (-(1 : ℝ) / 4)| = |t| * (n : ℝ) ^ (-(1 : ℝ) / 4) := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ (-(1 : ℝ) / 4))]
    have hbnd :
        ‖Complex.exp (Complex.I * ((t * (n : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)) - 1‖ ^ 2 ≤
          4 * |t| ^ 2 * (n : ℝ) ^ (-((1 : ℝ) / 2)) := by
      have hstep :
          ‖Complex.exp (Complex.I * ((t * (n : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)) - 1‖ ^ 2 ≤
            (2 * |t * (n : ℝ) ^ (-(1 : ℝ) / 4)|) ^ 2 := by
        nlinarith [hEb,
          norm_nonneg (Complex.exp (Complex.I * ((t * (n : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)) - 1),
          abs_nonneg (t * (n : ℝ) ^ (-(1 : ℝ) / 4))]
      have heq :
          (2 * |t * (n : ℝ) ^ (-(1 : ℝ) / 4)|) ^ 2 =
            4 * |t| ^ 2 * (n : ℝ) ^ (-((1 : ℝ) / 2)) := by
        rw [huabs, mul_pow, mul_pow, hpow2]
        ring
      rw [heq] at hstep
      exact hstep
    have hnn : (0 : ℝ) ≤ (n : ℝ) * ‖A n‖ ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnn, hkey]
    exact hbnd
  have hratio :
      Tendsto (fun n : ℕ => (1 + A n) ^ n / Complex.exp ((n : ℂ) * A n)) atTop (nhds 1) := by
    have hzero :
        Tendsto (fun n : ℕ => (n : ℂ) * (Complex.log (1 + A n) - A n)) atTop (nhds 0) := by
      have hle : ∀ᶠ n : ℕ in atTop,
          ‖(n : ℂ) * (Complex.log (1 + A n) - A n)‖ ≤ (n : ℝ) * ‖A n‖ ^ 2 := by
        filter_upwards [hbound] with n hn
        have hlt : ‖A n‖ < 1 := by linarith
        have hlog := Complex.norm_log_one_add_sub_self_le (z := A n) hlt
        have hpos : (0 : ℝ) < 1 - ‖A n‖ := by linarith
        have hinv : (1 - ‖A n‖)⁻¹ ≤ 2 := by
          have hmul : (1 - ‖A n‖) * (1 - ‖A n‖)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hpos)
          nlinarith [norm_nonneg (A n)]
        have hden : ‖A n‖ ^ 2 * (1 - ‖A n‖)⁻¹ / 2 ≤ ‖A n‖ ^ 2 := by
          nlinarith [sq_nonneg ‖A n‖, hinv]
        have hcastn : ‖(n : ℂ)‖ = (n : ℝ) := by simp
        calc ‖(n : ℂ) * (Complex.log (1 + A n) - A n)‖
            = ‖(n : ℂ)‖ * ‖Complex.log (1 + A n) - A n‖ := by rw [norm_mul]
          _ ≤ ‖(n : ℂ)‖ * (‖A n‖ ^ 2 * (1 - ‖A n‖)⁻¹ / 2) :=
              mul_le_mul_of_nonneg_left hlog (norm_nonneg _)
          _ ≤ ‖(n : ℂ)‖ * ‖A n‖ ^ 2 := mul_le_mul_of_nonneg_left hden (norm_nonneg _)
          _ = (n : ℝ) * ‖A n‖ ^ 2 := by rw [hcastn]
      exact squeeze_zero_norm' hle hsq
    have heq :
        (fun n : ℕ => (1 + A n) ^ n / Complex.exp ((n : ℂ) * A n))
          =ᶠ[atTop] (fun n : ℕ => Complex.exp ((n : ℂ) * (Complex.log (1 + A n) - A n))) := by
      filter_upwards [hbound] with n hn
      have hne : 1 + A n ≠ 0 := by
        intro h
        have hA1 : A n = -1 := by linear_combination h
        have hnorm : ‖A n‖ = 1 := by rw [hA1, norm_neg, norm_one]
        linarith
      have hne2 : Complex.exp ((n : ℂ) * A n) ≠ 0 := Complex.exp_ne_zero _
      have hpow : (1 + A n) ^ n = Complex.exp ((n : ℂ) * Complex.log (1 + A n)) := by
        rw [Complex.exp_nat_mul, Complex.exp_log hne]
      rw [hpow]
      rw [div_eq_iff hne2]
      rw [← Complex.exp_add]
      congr 1
      ring
    have hlim :
        Tendsto (fun n : ℕ => Complex.exp ((n : ℂ) * (Complex.log (1 + A n) - A n))) atTop
          (nhds 1) := by
      have h := (Complex.continuous_exp.tendsto (0 : ℂ)).comp hzero
      simpa using h
    exact Tendsto.congr' heq.symm hlim
  have hexp : Tendsto
      (fun n : ℕ => Complex.I * ((-(t * (n : ℝ) ^ ((1 : ℝ) / 4)) : ℝ) : ℂ) + (n : ℂ) * A n)
      atTop (nhds (((-(t ^ 2) / 2 : ℝ)) : ℂ)) := by
    have hdec4 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ) / 4)) atTop (nhds 0) := by
      have h := hdecay ((1 : ℝ) / 4) (by norm_num)
      refine Tendsto.congr' (Eventually.of_forall fun n => ?_) h
      have hb : (-((1 : ℝ) / 4)) = (-(1 : ℝ) / 4) := by norm_num
      rw [hb]
    have hu_tend : Tendsto (fun n : ℕ => t * (n : ℝ) ^ (-(1 : ℝ) / 4)) atTop (nhds 0) := by
      have h := hdec4.const_mul t
      simpa using h
    have hT : Tendsto
        (fun n : ℕ => ((Real.sqrt (n : ℝ) : ℝ) : ℂ) *
          (Complex.exp (Complex.I * ((t * (n : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)) - 1
            - Complex.I * ((t * (n : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)
            + ((((t * (n : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2 / 2 : ℝ)) : ℂ)))
        atTop (nhds 0) := by
      have hbdry : Tendsto
          (fun n : ℕ => (2 / 9) * |t| ^ 3 * (n : ℝ) ^ (-((1 : ℝ) / 4))) atTop (nhds 0) := by
        have h := (hdecay ((1 : ℝ) / 4) (by norm_num)).const_mul ((2 / 9) * |t| ^ 3)
        simpa using h
      refine squeeze_zero_norm' ?_ hbdry
      obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hu_tend) 1 (by norm_num)
      filter_upwards [Filter.eventually_ge_atTop (max N 16)] with n hn
      have hNn : N ≤ n := le_trans (le_max_left _ _) hn
      have hn16 : (16 : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_trans (le_max_right _ _) hn
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by linarith
      have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
      have hspos : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
      have hu_lt : |t * (n : ℝ) ^ (-(1 : ℝ) / 4)| < 1 := by
        have h := hN n hNn
        rwa [Real.dist_eq, sub_zero] at h
      have hxnorm :
          ‖Complex.I * ((t * (n : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)‖ =
            |t * (n : ℝ) ^ (-(1 : ℝ) / 4)| := by
        rw [norm_mul, Complex.norm_I, one_mul]
        simp
      have hx : ‖Complex.I * ((t * (n : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)‖ ≤ 1 := by
        rw [hxnorm]
        linarith
      have hxsq :
          (Complex.I * ((t * (n : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)) ^ 2 =
            -(((((t * (n : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2 : ℝ)) : ℂ)) := by
        have hIsq : Complex.I * Complex.I = -1 := by simp
        push_cast
        rw [mul_pow, pow_two (Complex.I), hIsq]
        ring
      have hexpsum :
          (∑ m ∈ Finset.range 3,
              (Complex.I * ((t * (n : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)) ^ m / ↑m.factorial) =
            1 + (Complex.I * ((t * (n : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)) +
              (Complex.I * ((t * (n : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)) ^ 2 / 2 := by
        rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
        norm_num [Nat.factorial]
      have hQb :
          ‖Complex.exp (Complex.I * ((t * (n : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)) - 1
              - Complex.I * ((t * (n : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)
              + ((((t * (n : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2 / 2 : ℝ)) : ℂ)‖ ≤
            (2 / 9) * |t * (n : ℝ) ^ (-(1 : ℝ) / 4)| ^ 3 := by
        have h :=
          Complex.exp_bound (x := Complex.I * ((t * (n : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)) hx
            (n := 3) (by norm_num)
        rw [hexpsum] at h
        have hnum :
            ((↑(Nat.succ 3) : ℝ) * (((↑(Nat.factorial 3) : ℝ) * (↑(3 : ℕ) : ℝ)))⁻¹) = 2 / 9 := by
          norm_num [Nat.factorial]
        rw [hnum] at h
        have harg :
            ‖Complex.I * ((t * (n : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)‖ ^ 3 * (2 / 9) =
              (2 / 9) * ‖Complex.I * ((t * (n : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)‖ ^ 3 := by
          ring
        rw [harg] at h
        have hargeq :
            Complex.exp (Complex.I * ((t * (n : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)) -
                (1 + Complex.I * ((t * (n : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ) +
                  (Complex.I * ((t * (n : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)) ^ 2 / 2) =
              Complex.exp (Complex.I * ((t * (n : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)) - 1
                - Complex.I * ((t * (n : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)
                + ((((t * (n : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2 / 2 : ℝ)) : ℂ) := by
          rw [hxsq]
          push_cast
          ring
        rw [hargeq, hxnorm] at h
        exact h
      have huabs :
          |t * (n : ℝ) ^ (-(1 : ℝ) / 4)| = |t| * (n : ℝ) ^ (-(1 : ℝ) / 4) := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ (-(1 : ℝ) / 4))]
      have hscal :
          Real.sqrt (n : ℝ) * ((n : ℝ) ^ (-(1 : ℝ) / 4)) ^ 3 = (n : ℝ) ^ (-((1 : ℝ) / 4)) := by
        rw [← Real.rpow_mul_natCast (le_of_lt hnpos), Real.sqrt_eq_rpow, ← Real.rpow_add hnpos]
        rw [show ((1 : ℝ) / 2 + (-(1 : ℝ) / 4) * ((3 : ℕ) : ℝ)) = -((1 : ℝ) / 4) by norm_num]
      have hfinal :
          Real.sqrt (n : ℝ) * ((2 / 9) * |t * (n : ℝ) ^ (-(1 : ℝ) / 4)| ^ 3) =
            (2 / 9) * |t| ^ 3 * (n : ℝ) ^ (-((1 : ℝ) / 4)) := by
        rw [huabs, mul_pow]
        linear_combination ((2 / 9) * |t| ^ 3) * hscal
      have hcast : ‖(((Real.sqrt (n : ℝ) : ℝ)) : ℂ)‖ = Real.sqrt (n : ℝ) := by simp
      rw [norm_mul, hcast]
      calc Real.sqrt (n : ℝ) *
            ‖Complex.exp (Complex.I * ((t * (n : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)) - 1
              - Complex.I * ((t * (n : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)
              + ((((t * (n : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2 / 2 : ℝ)) : ℂ)‖
          ≤ Real.sqrt (n : ℝ) * ((2 / 9) * |t * (n : ℝ) ^ (-(1 : ℝ) / 4)| ^ 3) :=
            mul_le_mul_of_nonneg_left hQb (le_of_lt hspos)
        _ = (2 / 9) * |t| ^ 3 * (n : ℝ) ^ (-((1 : ℝ) / 4)) := hfinal
    have hpt :
        (fun n : ℕ =>
            Complex.I * ((-(t * (n : ℝ) ^ ((1 : ℝ) / 4)) : ℝ) : ℂ) + (n : ℂ) * A n) =ᶠ[atTop]
          (fun n : ℕ =>
            ((Real.sqrt (n : ℝ) : ℝ) : ℂ) *
                (Complex.exp (Complex.I * ((t * (n : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)) - 1
                  - Complex.I * ((t * (n : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)
                  + ((((t * (n : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2 / 2 : ℝ)) : ℂ)) -
              (((t ^ 2 / 2 : ℝ)) : ℂ)) := by
      filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
      have hspos : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
      have hsqr : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (le_of_lt hnpos)
      have hcoef :
          (n : ℂ) * (((1 / Real.sqrt (n : ℝ) : ℝ)) : ℂ) = ((Real.sqrt (n : ℝ) : ℝ) : ℂ) := by
        have hreal : (n : ℝ) * (1 / Real.sqrt (n : ℝ)) = Real.sqrt (n : ℝ) := by
          field_simp
          nlinarith [hsqr]
        calc (n : ℂ) * (((1 / Real.sqrt (n : ℝ) : ℝ)) : ℂ) =
              (((n : ℝ) * (1 / Real.sqrt (n : ℝ)) : ℝ) : ℂ) := by
              push_cast
              ring
          _ = ((Real.sqrt (n : ℝ) : ℝ) : ℂ) := by rw [hreal]
      have hAn_eq : (n : ℂ) * A n =
          ((Real.sqrt (n : ℝ) : ℝ) : ℂ) *
            (Complex.exp (Complex.I * ((t * (n : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)) - 1) := by
        rw [hA, ← mul_assoc, hcoef]
      have hp1 : Real.sqrt (n : ℝ) * (n : ℝ) ^ (-(1 : ℝ) / 4) = (n : ℝ) ^ ((1 : ℝ) / 4) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hnpos]
        rw [show ((1 : ℝ) / 2 + (-(1 : ℝ) / 4)) = (1 : ℝ) / 4 by norm_num]
      have hp2 : Real.sqrt (n : ℝ) * ((n : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2 = 1 := by
        rw [show ((n : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2 =
            (n : ℝ) ^ (-(1 : ℝ) / 4) * (n : ℝ) ^ (-(1 : ℝ) / 4) by ring]
        rw [← mul_assoc, hp1, ← Real.rpow_add hnpos]
        rw [show ((1 : ℝ) / 4 + (-(1 : ℝ) / 4)) = 0 by norm_num, Real.rpow_zero]
      have hreal1 :
          Real.sqrt (n : ℝ) * (t * (n : ℝ) ^ (-(1 : ℝ) / 4)) = t * (n : ℝ) ^ ((1 : ℝ) / 4) := by
        calc Real.sqrt (n : ℝ) * (t * (n : ℝ) ^ (-(1 : ℝ) / 4)) =
              t * (Real.sqrt (n : ℝ) * (n : ℝ) ^ (-(1 : ℝ) / 4)) := by ring
          _ = t * (n : ℝ) ^ ((1 : ℝ) / 4) := by rw [hp1]
      have hreal2 :
          Real.sqrt (n : ℝ) * ((t * (n : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2 / 2) = t ^ 2 / 2 := by
        calc Real.sqrt (n : ℝ) * ((t * (n : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2 / 2) =
              (t ^ 2 / 2) * (Real.sqrt (n : ℝ) * ((n : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2) := by ring
          _ = t ^ 2 / 2 := by rw [hp2]; ring
      have hc1 :
          ((Real.sqrt (n : ℝ) : ℝ) : ℂ) *
              (Complex.I * ((t * (n : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)) =
            Complex.I * (((t * (n : ℝ) ^ ((1 : ℝ) / 4)) : ℝ) : ℂ) := by
        rw [← hreal1]
        push_cast
        ring
      have hc2 :
          ((Real.sqrt (n : ℝ) : ℝ) : ℂ) * ((((t * (n : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2 / 2 : ℝ)) : ℂ) =
            (((t ^ 2 / 2 : ℝ)) : ℂ) := by
        rw [← hreal2]
        push_cast
        ring
      have hnegcast :
          Complex.I * ((-(t * (n : ℝ) ^ ((1 : ℝ) / 4)) : ℝ) : ℂ) =
            -(Complex.I * (((t * (n : ℝ) ^ ((1 : ℝ) / 4)) : ℝ) : ℂ)) := by
        push_cast
        ring
      linear_combination hAn_eq + hnegcast + hc1 - hc2
    have hlim :
        Tendsto
          (fun n : ℕ => ((Real.sqrt (n : ℝ) : ℝ) : ℂ) *
              (Complex.exp (Complex.I * ((t * (n : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)) - 1
                - Complex.I * ((t * (n : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)
                + ((((t * (n : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2 / 2 : ℝ)) : ℂ)) -
              (((t ^ 2 / 2 : ℝ)) : ℂ))
          atTop (nhds (0 - (((t ^ 2 / 2 : ℝ)) : ℂ))) :=
      hT.sub tendsto_const_nhds
    have heq : (0 - (((t ^ 2 / 2 : ℝ)) : ℂ)) = (((-(t ^ 2) / 2 : ℝ)) : ℂ) := by
      push_cast
      ring
    rw [heq] at hlim
    exact Tendsto.congr' hpt.symm hlim
  have h1 : Tendsto
      (fun n : ℕ =>
        Complex.exp (Complex.I * ((-(t * (n : ℝ) ^ ((1 : ℝ) / 4)) : ℝ) : ℂ) + (n : ℂ) * A n))
      atTop (nhds (Complex.exp (((-(t ^ 2) / 2 : ℝ)) : ℂ))) :=
    Complex.continuous_exp.tendsto _ |>.comp hexp
  have hprod : Tendsto
      (fun n : ℕ =>
        Complex.exp (Complex.I * ((-(t * (n : ℝ) ^ ((1 : ℝ) / 4)) : ℝ) : ℂ) + (n : ℂ) * A n) *
          ((1 + A n) ^ n / Complex.exp ((n : ℂ) * A n)))
      atTop (nhds (Complex.exp (((-(t ^ 2) / 2 : ℝ)) : ℂ) * 1)) := h1.mul hratio
  have hfun : (fun n : ℕ =>
        Complex.exp (Complex.I * ((-(t * (n : ℝ) ^ ((1 : ℝ) / 4)) : ℝ) : ℂ) + (n : ℂ) * A n) *
          ((1 + A n) ^ n / Complex.exp ((n : ℂ) * A n))) =
      (fun n : ℕ =>
        Complex.exp (Complex.I * ((-(t * (n : ℝ) ^ ((1 : ℝ) / 4)) : ℝ) : ℂ)) * (1 + A n) ^ n) := by
    funext n
    have hne : Complex.exp ((n : ℂ) * A n) ≠ 0 := Complex.exp_ne_zero _
    rw [Complex.exp_add]
    field_simp
  rw [hfun] at hprod
  simpa only [hbase, mul_one] using hprod
  /- @proof-region region.target-node.session.3fa6593354951bcf end -/

end Msc62GroundTruth
