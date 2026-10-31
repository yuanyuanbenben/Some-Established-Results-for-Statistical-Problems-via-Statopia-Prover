import ProverJobs.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Vocabulary
import ProverJobs.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Base

namespace PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators
open _root_.PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Statlib.Imported
open _root_.PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Statlib.Imported.Model

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators
namespace Statlib.Imported

noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_70832348_d8d3cb27 : ∀ {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (a c0 alpha cvar ccirc eps0 Ccor C : ℝ) (M : Model Ω μ a)
    (ha : a ∈ Set.Ioo (0 : ℝ) (1 / 2)) (hc0 : 0 < c0) (halpha : 0 < alpha)
    (hcvar : 0 < cvar) (hccirc : ccirc ∈ Set.Ioo (0 : ℝ) 1)
    (heps0 : eps0 ∈ Set.Ioo (0 : ℝ) 1) (hCcor : 0 < Ccor) (hC : 0 < C)
    (hM : Model.Assumptions M c0 alpha cvar ccirc eps0 Ccor),
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → M.kIdx n < M.p n →
      C * (M.kIdx n : ℝ) ^ (-(alpha * (1 - M.tau n))) * Real.log (n : ℝ)
        ≤ ccirc * (M.ell n : ℝ) ^ (-(alpha * (1 - M.tau n)))
            * Real.sqrt (Real.log (M.ell n : ℝ)) := by
  /- @proof-region region.target-node.session.d09a2daaf7801546 begin -/
  intro Ω _ μ _ a c0 alpha cvar ccirc eps0 Ccor C M ha hc0 halpha hcvar hccirc heps0 hCcor hC hM
  obtain ⟨ct, hct, hτ⟩ := hM.htau_cond
  have key : ∀ᶠ n : ℕ in Filter.atTop, M.kIdx n < M.p n →
      C * (M.kIdx n : ℝ) ^ (-(alpha * (1 - M.tau n))) * Real.log (n : ℝ) ≤
        ccirc * (M.ell n : ℝ) ^ (-(alpha * (1 - M.tau n))) *
          Real.sqrt (Real.log (M.ell n : ℝ)) := by
    have hα : 0 < alpha := halpha
    have hc0' : 0 < ccirc := hccirc.1
    have hs : (0:ℝ) < 1 / 2 - a := by linarith [ha.2]
    have hLbig : ∀ K : ℝ, ∀ᶠ n : ℕ in Filter.atTop, K ≤ Real.log (n:ℝ) := by
      intro K
      refine Filter.eventually_atTop.2 ⟨Nat.ceil (Real.exp K) + 1, fun n hn => ?_⟩
      have h1 : Real.exp K ≤ (Nat.ceil (Real.exp K) : ℝ) := Nat.le_ceil _
      have h2 : (Nat.ceil (Real.exp K) : ℝ) ≤ (n:ℝ) := by
        have h3 : Nat.ceil (Real.exp K) ≤ n := le_trans (Nat.le_succ _) hn
        exact_mod_cast h3
      calc K = Real.log (Real.exp K) := (Real.log_exp K).symm
        _ ≤ Real.log (n:ℝ) := Real.log_le_log (Real.exp_pos K) (le_trans h1 h2)
    have hconv : ∀ (r ε : ℝ), 0 < r → 0 < ε → ∀ᶠ n : ℕ in Filter.atTop,
        Real.log (Real.log (n:ℝ)) ≤ ε * (Real.log (n:ℝ)) ^ r := by
      intro r ε hr hε
      set t : ℝ := r / 2 with ht_def
      set c : ℝ := 2 / (ε * r) with hc_def
      have ht : 0 < t := by rw [ht_def]; linarith
      have hc : 0 < c := by rw [hc_def]; positivity
      filter_upwards [hLbig 1, hLbig (c ^ (2 / r))] with n hL1 hLc
      have hLpos : (0:ℝ) < Real.log (n:ℝ) := by linarith [hL1]
      have hAc : c ≤ (Real.log (n:ℝ)) ^ t := by
        have h1 : (c ^ (2 / r)) ^ t ≤ (Real.log (n:ℝ)) ^ t :=
          Real.rpow_le_rpow (Real.rpow_nonneg (le_of_lt hc) _) hLc (le_of_lt ht)
        have h2 : (c ^ (2 / r)) ^ t = c := by
          have h4 : (2 / r) * t = 1 := by rw [ht_def]; field_simp
          rw [← Real.rpow_mul (le_of_lt hc)]
          rw [h4, Real.rpow_one]
        rwa [h2] at h1
      have hXn : (0:ℝ) ≤ (Real.log (n:ℝ)) ^ t := Real.rpow_nonneg (le_of_lt hLpos) t
      have hB : Real.log (Real.log (n:ℝ)) ≤ (Real.log (n:ℝ)) ^ t / t := by
        have hpos : (0:ℝ) < (Real.log (n:ℝ)) ^ t := Real.rpow_pos_of_pos hLpos t
        have h1 : Real.log ((Real.log (n:ℝ)) ^ t) ≤ (Real.log (n:ℝ)) ^ t - 1 :=
          Real.log_le_sub_one_of_pos hpos
        rw [Real.log_rpow hLpos] at h1
        rw [le_div_iff₀ ht]
        linarith [h1, hpos]
      have hsq : (Real.log (n:ℝ)) ^ t * (Real.log (n:ℝ)) ^ t = (Real.log (n:ℝ)) ^ r := by
        rw [← Real.rpow_add hLpos]
        congr 1
        rw [ht_def]
        ring
      have hcc : ε * c = 2 / r := by rw [hc_def]; field_simp
      have h1t : (1:ℝ) / t = 2 / r := by rw [ht_def]; field_simp
      have hcX : c * (Real.log (n:ℝ)) ^ t ≤ (Real.log (n:ℝ)) ^ t * (Real.log (n:ℝ)) ^ t := by
        nlinarith [hAc, hXn]
      calc Real.log (Real.log (n:ℝ))
          ≤ (Real.log (n:ℝ)) ^ t / t := hB
        _ = (1 / t) * (Real.log (n:ℝ)) ^ t := by ring
        _ = (ε * c) * (Real.log (n:ℝ)) ^ t := by rw [h1t, ← hcc]
        _ = ε * (c * (Real.log (n:ℝ)) ^ t) := by ring
        _ ≤ ε * ((Real.log (n:ℝ)) ^ t * (Real.log (n:ℝ)) ^ t) := by
            linarith [mul_le_mul_of_nonneg_left hcX (le_of_lt hε)]
        _ = ε * (Real.log (n:ℝ)) ^ r := by rw [hsq]
    have hbig : ∀ᶠ n : ℕ in Filter.atTop,
        Real.log 2 + 3 * Real.log (Real.log (n:ℝ)) ≤ (1/2) * (Real.log (n:ℝ)) ^ (1 - a) := by
      filter_upwards [hconv (1 - a) (1/32) (by linarith [ha.2]) (by norm_num), hLbig 2] with n h1 hL2
      have hL2' : (0:ℝ) < Real.log (n:ℝ) := by linarith
      have hlog2 : Real.log 2 ≤ Real.log (Real.log (n:ℝ)) := Real.log_le_log (by norm_num) hL2
      have hLapos : (0:ℝ) ≤ (Real.log (n:ℝ)) ^ (1 - a) := Real.rpow_nonneg (le_of_lt hL2') _
      linarith
    have hlittleS : ∀ᶠ n : ℕ in Filter.atTop,
        Real.log (Real.log (n:ℝ)) ≤ (alpha * ct / 8) * (Real.log (n:ℝ)) ^ (1/2 - a) :=
      hconv (1/2 - a) (alpha * ct / 8) hs (by positivity)
    filter_upwards [hLbig 12, hLbig (Real.exp (1/3)),
      hLbig (Real.exp (Real.log C - Real.log ccirc)), hbig, hlittleS, hτ]
      with n hL12 hL13 hLK hbig' hlit' hτn hk
    have hLpos : (0:ℝ) < Real.log (n:ℝ) := by linarith [hL12]
    have hn0 : (0:ℝ) < (n:ℝ) := by
      rcases Nat.eq_zero_or_pos n with h | h
      · rw [h] at hL12
        simp only [Nat.cast_zero, Real.log_zero] at hL12
        linarith
      · exact_mod_cast h
    have hβpos : (0:ℝ) < alpha * (1 - M.tau n) := by
      have h1 : (0:ℝ) < 1 - M.tau n := by
        have h2 := (hM.htau_mem n).2
        linarith
      exact mul_pos hα h1
    have hβge : alpha * ct ≤ (alpha * (1 - M.tau n)) * Real.sqrt (Real.log (n:ℝ)) := by
      have h := mul_le_mul_of_nonneg_left hτn (le_of_lt hα)
      linarith [h]
    have hminlt : min (max (M.ell n : ℝ) ((n:ℝ) ^ (1 / ((Real.log (n:ℝ)) ^ a)))) (M.p n : ℝ) < (M.p n : ℝ) := by
      by_contra hcon
      have hcon' : (M.p n : ℝ) ≤ min (max (M.ell n : ℝ) ((n:ℝ) ^ (1 / ((Real.log (n:ℝ)) ^ a)))) (M.p n : ℝ) :=
        le_of_not_gt hcon
      have hPleA : (M.p n : ℝ) ≤ max (M.ell n : ℝ) ((n:ℝ) ^ (1 / ((Real.log (n:ℝ)) ^ a))) :=
        le_trans hcon' (min_le_left _ _)
      have hminP : min (max (M.ell n : ℝ) ((n:ℝ) ^ (1 / ((Real.log (n:ℝ)) ^ a)))) (M.p n : ℝ) = (M.p n : ℝ) :=
        min_eq_right hPleA
      have hkp : M.kIdx n = M.p n := by
        show Nat.ceil (min (max (M.ell n : ℝ) ((n:ℝ) ^ (1 / ((Real.log (n:ℝ)) ^ a)))) (M.p n : ℝ)) = M.p n
        rw [hminP, Nat.ceil_natCast]
      omega
    have hAP : max (M.ell n : ℝ) ((n:ℝ) ^ (1 / ((Real.log (n:ℝ)) ^ a))) < (M.p n : ℝ) := by
      by_contra hcon
      have hcon' : (M.p n : ℝ) ≤ max (M.ell n : ℝ) ((n:ℝ) ^ (1 / ((Real.log (n:ℝ)) ^ a))) :=
        le_of_not_gt hcon
      have hminP : min (max (M.ell n : ℝ) ((n:ℝ) ^ (1 / ((Real.log (n:ℝ)) ^ a)))) (M.p n : ℝ) = (M.p n : ℝ) :=
        min_eq_right hcon'
      linarith [hminlt, hminP]

    have hellmin : min (max (1:ℝ) ((Real.log (n:ℝ)) ^ 3)) (M.p n : ℝ) < (M.p n : ℝ) := by
      by_contra hcon
      have hcon' : (M.p n : ℝ) ≤ min (max (1:ℝ) ((Real.log (n:ℝ)) ^ 3)) (M.p n : ℝ) :=
        le_of_not_gt hcon
      have hPleB : (M.p n : ℝ) ≤ max (1:ℝ) ((Real.log (n:ℝ)) ^ 3) :=
        le_trans hcon' (min_le_left _ _)
      have hPell : M.ell n = M.p n := by
        show Nat.ceil (min (max (1:ℝ) ((Real.log (n:ℝ)) ^ 3)) (M.p n : ℝ)) = M.p n
        rw [min_eq_right hPleB, Nat.ceil_natCast]
      have hle : (M.p n : ℝ) ≤ max (M.ell n : ℝ) ((n:ℝ) ^ (1 / ((Real.log (n:ℝ)) ^ a))) := by
        rw [hPell]
        exact le_max_left _ _
      have hkp : M.kIdx n = M.p n := by
        show Nat.ceil (min (max (M.ell n : ℝ) ((n:ℝ) ^ (1 / ((Real.log (n:ℝ)) ^ a)))) (M.p n : ℝ)) = M.p n
        rw [min_eq_right hle, Nat.ceil_natCast]
      omega
    have h1L3 : max (1:ℝ) ((Real.log (n:ℝ)) ^ 3) < (M.p n : ℝ) := by
      by_contra hcon
      have hcon' : (M.p n : ℝ) ≤ max (1:ℝ) ((Real.log (n:ℝ)) ^ 3) := le_of_not_gt hcon
      have hminP : min (max (1:ℝ) ((Real.log (n:ℝ)) ^ 3)) (M.p n : ℝ) = (M.p n : ℝ) := min_eq_right hcon'
      linarith [hellmin, hminP]
    have hL3 : (1:ℝ) ≤ (Real.log (n:ℝ)) ^ 3 := by
      have hLone : (1:ℝ) ≤ Real.log (n:ℝ) := by linarith [hL12]
      have hsq : (1:ℝ) ≤ (Real.log (n:ℝ)) ^ 2 := by
        nlinarith [mul_le_mul hLone hLone (by norm_num : (0:ℝ) ≤ 1) (le_of_lt hLpos)]
      nlinarith [mul_le_mul hLone hsq (by norm_num : (0:ℝ) ≤ 1) (le_of_lt hLpos)]
    have hell3 : M.ell n = Nat.ceil ((Real.log (n:ℝ)) ^ 3) := by
      show Nat.ceil (min (max (1:ℝ) ((Real.log (n:ℝ)) ^ 3)) (M.p n : ℝ)) = Nat.ceil ((Real.log (n:ℝ)) ^ 3)
      rw [min_eq_left (le_of_lt h1L3), max_eq_right hL3]
    have hell_ge : (Real.log (n:ℝ)) ^ 3 ≤ (M.ell n : ℝ) := by
      rw [hell3]
      exact Nat.le_ceil _
    have hell_le : (M.ell n : ℝ) ≤ 2 * (Real.log (n:ℝ)) ^ 3 := by
      rw [hell3]
      have h := Nat.ceil_lt_add_one (show (0:ℝ) ≤ (Real.log (n:ℝ)) ^ 3 by positivity)
      linarith [h, hL3]
    have hpos_ell : (0:ℝ) < (M.ell n : ℝ) := by
      have h2 : (0:ℝ) < (Real.log (n:ℝ)) ^ 3 := by positivity
      linarith [hell_ge]
    have hklower : (n:ℝ) ^ (1 / ((Real.log (n:ℝ)) ^ a)) ≤ (M.kIdx n : ℝ) := by
      have hdef : M.kIdx n = Nat.ceil (min (max (M.ell n : ℝ) ((n:ℝ) ^ (1 / ((Real.log (n:ℝ)) ^ a)))) (M.p n : ℝ)) := rfl
      rw [hdef]
      have h2 : max (M.ell n : ℝ) ((n:ℝ) ^ (1 / ((Real.log (n:ℝ)) ^ a))) ≤
          min (max (M.ell n : ℝ) ((n:ℝ) ^ (1 / ((Real.log (n:ℝ)) ^ a)))) (M.p n : ℝ) :=
        (min_eq_left (le_of_lt hAP)).ge
      exact le_trans (le_trans (le_max_right _ _) h2) (Nat.le_ceil _)
    have hEpos : (0:ℝ) < (n:ℝ) ^ (1 / ((Real.log (n:ℝ)) ^ a)) := Real.rpow_pos_of_pos hn0 _
    have hkpos : (0:ℝ) < (M.kIdx n : ℝ) := lt_of_lt_of_le hEpos hklower
    have hlogk : (Real.log (n:ℝ)) / ((Real.log (n:ℝ)) ^ a) ≤ Real.log (M.kIdx n : ℝ) := by
      have h1 : Real.log ((n:ℝ) ^ (1 / ((Real.log (n:ℝ)) ^ a))) ≤ Real.log (M.kIdx n : ℝ) :=
        Real.log_le_log (Real.rpow_pos_of_pos hn0 _) hklower
      rw [Real.log_rpow hn0] at h1
      have h2 : (1 / ((Real.log (n:ℝ)) ^ a)) * Real.log (n:ℝ) = (Real.log (n:ℝ)) / ((Real.log (n:ℝ)) ^ a) := by ring
      linarith [h1, h2]
    have hell_log : Real.log (M.ell n : ℝ) ≤ Real.log 2 + 3 * Real.log (Real.log (n:ℝ)) := by
      have h1 : Real.log (M.ell n : ℝ) ≤ Real.log (2 * (Real.log (n:ℝ)) ^ 3) :=
        Real.log_le_log hpos_ell hell_le
      have h2 : Real.log (2 * (Real.log (n:ℝ)) ^ 3) = Real.log 2 + 3 * Real.log (Real.log (n:ℝ)) := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
        norm_num
      rwa [h2] at h1
    have hpow : (Real.log (n:ℝ)) ^ (1 - a) = (Real.log (n:ℝ)) / ((Real.log (n:ℝ)) ^ a) := by
      rw [Real.rpow_sub hLpos, Real.rpow_one]
    have h3pow : (Real.log (n:ℝ)) ^ (1 - a) ≤ Real.log (M.kIdx n : ℝ) := by
      rw [hpow]
      exact hlogk
    have hlogineq : Real.log (M.ell n : ℝ) + (1/2) * (Real.log (n:ℝ)) ^ (1 - a) ≤ Real.log (M.kIdx n : ℝ) := by
      linarith [hell_log, hbig', h3pow]
    have hlogell : 3 * Real.log (Real.log (n:ℝ)) ≤ Real.log (M.ell n : ℝ) := by
      have h1 : Real.log ((Real.log (n:ℝ)) ^ 3) ≤ Real.log (M.ell n : ℝ) :=
        Real.log_le_log (by positivity) hell_ge
      rw [Real.log_pow] at h1
      simpa using h1
    have hlogL_third : (1/3:ℝ) ≤ Real.log (Real.log (n:ℝ)) :=
      (Real.le_log_iff_exp_le hLpos).mpr hL13
    have hlogell_one : (1:ℝ) ≤ Real.log (M.ell n : ℝ) := by linarith
    have hsqrt_pow : (Real.log (n:ℝ)) ^ (1 - a) = (Real.log (n:ℝ)) ^ (1/2 - a) * Real.sqrt (Real.log (n:ℝ)) := by
      have h1 : (1/2 - a) + 1/2 = 1 - a := by ring
      rw [← h1, Real.rpow_add hLpos, Real.sqrt_eq_rpow]
    have hLspos : (0:ℝ) ≤ (Real.log (n:ℝ)) ^ (1/2 - a) := Real.rpow_nonneg (le_of_lt hLpos) _
    have hK : Real.log C - Real.log ccirc ≤ Real.log (Real.log (n:ℝ)) :=
      (Real.le_log_iff_exp_le hLpos).mpr hLK
    have hmid : (alpha * ct / 2) * (Real.log (n:ℝ)) ^ (1/2 - a) ≤
        (1/2) * (Real.log (n:ℝ)) ^ (1 - a) * (alpha * (1 - M.tau n)) := by
      have h2 : alpha * ct ≤ Real.sqrt (Real.log (n:ℝ)) * (alpha * (1 - M.tau n)) :=
        hβge.trans_eq (mul_comm _ _)
      have h2' : alpha * ct / 2 ≤ (Real.sqrt (Real.log (n:ℝ)) * (alpha * (1 - M.tau n))) / 2 := by
        linarith
      have h3 : (alpha * ct / 2) * (Real.log (n:ℝ)) ^ (1/2 - a) ≤
          ((Real.sqrt (Real.log (n:ℝ)) * (alpha * (1 - M.tau n))) / 2) * (Real.log (n:ℝ)) ^ (1/2 - a) :=
        mul_le_mul_of_nonneg_right h2' hLspos
      have h4 : ((Real.sqrt (Real.log (n:ℝ)) * (alpha * (1 - M.tau n))) / 2) * (Real.log (n:ℝ)) ^ (1/2 - a) =
          (1/2) * (Real.log (n:ℝ)) ^ (1 - a) * (alpha * (1 - M.tau n)) := by
        rw [hsqrt_pow]
        ring
      linarith [h3, h4]
    have hleft : Real.log C + Real.log (Real.log (n:ℝ)) ≤
        (alpha * ct / 2) * (Real.log (n:ℝ)) ^ (1/2 - a) + Real.log ccirc := by
      have h4 : Real.log (Real.log (n:ℝ)) ≤ (alpha * ct / 8) * (Real.log (n:ℝ)) ^ (1/2 - a) := hlit'
      have h5 : (0:ℝ) ≤ (alpha * ct / 8) * (Real.log (n:ℝ)) ^ (1/2 - a) := by positivity
      linarith [h4, hK, h5, hLspos]
    have hparts : Real.log C + Real.log (Real.log (n:ℝ)) ≤
        (1/2) * (Real.log (n:ℝ)) ^ (1 - a) * (alpha * (1 - M.tau n)) + Real.log ccirc := by
      linarith [hmid, hleft]
    have hexp1 : (M.kIdx n : ℝ) ^ (-(alpha * (1 - M.tau n))) ≤
        (M.ell n : ℝ) ^ (-(alpha * (1 - M.tau n))) *
          Real.exp (-(((1/2) * (Real.log (n:ℝ)) ^ (1 - a)) * (alpha * (1 - M.tau n)))) := by
      rw [Real.rpow_def_of_pos hkpos, Real.rpow_def_of_pos hpos_ell, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h1 : (Real.log (M.ell n : ℝ) + (1/2) * (Real.log (n:ℝ)) ^ (1 - a)) * (alpha * (1 - M.tau n)) ≤
          Real.log (M.kIdx n : ℝ) * (alpha * (1 - M.tau n)) :=
        mul_le_mul_of_nonneg_right hlogineq (le_of_lt hβpos)
      linarith [h1]
    have hscal : C * Real.log (n:ℝ) * Real.exp (-(((1/2) * (Real.log (n:ℝ)) ^ (1 - a)) * (alpha * (1 - M.tau n)))) ≤ ccirc := by
      have hE : Real.exp (Real.log C + Real.log (Real.log (n:ℝ)) - ((1/2) * (Real.log (n:ℝ)) ^ (1 - a)) * (alpha * (1 - M.tau n)))
          = C * Real.log (n:ℝ) * Real.exp (-(((1/2) * (Real.log (n:ℝ)) ^ (1 - a)) * (alpha * (1 - M.tau n)))) := by
        rw [show Real.log C + Real.log (Real.log (n:ℝ)) - ((1/2) * (Real.log (n:ℝ)) ^ (1 - a)) * (alpha * (1 - M.tau n))
            = (Real.log C + Real.log (Real.log (n:ℝ))) + (-(((1/2) * (Real.log (n:ℝ)) ^ (1 - a)) * (alpha * (1 - M.tau n)))) from by ring]
        rw [Real.exp_add, Real.exp_add, Real.exp_log hC, Real.exp_log hLpos]
      rw [← hE, ← Real.exp_log hc0']
      apply Real.exp_le_exp.mpr
      linarith [hparts]
    have hβrpow : (0:ℝ) ≤ (M.ell n : ℝ) ^ (-(alpha * (1 - M.tau n))) :=
      Real.rpow_nonneg (le_of_lt hpos_ell) _
    have hsqrt_one : (1:ℝ) ≤ Real.sqrt (Real.log (M.ell n : ℝ)) := Real.one_le_sqrt.mpr hlogell_one
    calc C * (M.kIdx n : ℝ) ^ (-(alpha * (1 - M.tau n))) * Real.log (n:ℝ)
        ≤ (C * Real.log (n:ℝ) * Real.exp (-(((1/2) * (Real.log (n:ℝ)) ^ (1 - a)) * (alpha * (1 - M.tau n))))) * (M.ell n : ℝ) ^ (-(alpha * (1 - M.tau n))) := by
          have h1 : C * (M.kIdx n : ℝ) ^ (-(alpha * (1 - M.tau n))) ≤
              C * ((M.ell n : ℝ) ^ (-(alpha * (1 - M.tau n))) * Real.exp (-(((1/2) * (Real.log (n:ℝ)) ^ (1 - a)) * (alpha * (1 - M.tau n))))) :=
            mul_le_mul_of_nonneg_left hexp1 (le_of_lt hC)
          have h2 := mul_le_mul_of_nonneg_right h1 (le_of_lt hLpos)
          linarith [h2]
      _ ≤ ccirc * (M.ell n : ℝ) ^ (-(alpha * (1 - M.tau n))) :=
          mul_le_mul_of_nonneg_right hscal hβrpow
      _ ≤ ccirc * (M.ell n : ℝ) ^ (-(alpha * (1 - M.tau n))) * Real.sqrt (Real.log (M.ell n : ℝ)) :=
          le_mul_of_one_le_right (mul_nonneg (le_of_lt hc0') hβrpow) hsqrt_one
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp key
  exact ⟨N, fun n hn hk => hN n hn hk⟩
  /- @proof-region region.target-node.session.d09a2daaf7801546 end -/

end
end Statlib.Imported

