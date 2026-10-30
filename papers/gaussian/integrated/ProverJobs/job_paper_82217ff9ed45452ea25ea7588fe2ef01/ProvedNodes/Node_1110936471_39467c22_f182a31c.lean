import ProverJobs.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Vocabulary
import ProverJobs.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Base
import ProverJobs.job_paper_82217ff9ed45452ea25ea7588fe2ef01.ProvedNodes.Node_1043829637_02d50666_07067a8c

namespace PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators
open _root_.PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Statlib.Imported
open _root_.PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Statlib.Imported.Model

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators
namespace Statlib.Imported
open _root_.Statlib
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_1110936471_39467c22 : ∀ (a c0 alpha cvar ccirc eps0 Ccor : ℝ)
    (ha : a ∈ Set.Ioo (0 : ℝ) (1 / 2)) (halpha : 0 < alpha)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (M : Model Ω μ a) (hM : Model.Assumptions M c0 alpha cvar ccirc eps0 Ccor)
    (C : ℝ) (hC : 0 < C),
    ∃ N_B : ℕ, 1 ≤ N_B ∧ ∀ n : ℕ, N_B ≤ n → M.kIdx n < M.p n →
      (M.tildeLaw n) {w : Fin (M.p n) → ℝ |
        fmax ((Finset.univ : Finset (Fin (M.p n))) \ M.J n (M.kIdx n))
          (fun j => w j / (M.sigma n j) ^ (M.tau n))
        > C * Real.rpow (M.kIdx n : ℝ) (-(alpha * (1 - M.tau n))) * Real.log (n : ℝ)}
      ≤ ENNReal.ofReal ((n : ℝ) ^ (-1 : ℤ)) := by
  /- @proof-region region.target-node.session.91b893579eacbcc3 begin -/
  intro a c0 alpha cvar ccirc eps0 Ccor ha halpha Ω _ μ _ M hM C hC
  have ha0 : 0 < a := ha.1
  have ha1 : a < 1 / 2 := ha.2
  classical
  have hEll : ∀ n : ℕ, M.ell n ≤ M.p n := fun n => Nat.ceil_le.mpr (min_le_right _ _)
  have hk_le : ∀ n : ℕ, M.kIdx n ≤ M.p n := fun n => Nat.ceil_le.mpr (min_le_right _ _)
  have hEll1 : ∀ n : ℕ, 1 ≤ M.ell n := by
    intro m
    have h1 : (1 : ℝ) ≤ min (max (1 : ℝ) ((Real.log (m : ℝ)) ^ 3)) (M.p m : ℝ) :=
      le_min (le_max_left _ _) (by exact_mod_cast M.hp m)
    have h2 : (1 : ℝ) ≤ ((M.ell m : ℕ) : ℝ) := le_trans h1 (Nat.le_ceil _)
    exact_mod_cast h2
  have hk1 : ∀ n : ℕ, 1 ≤ M.kIdx n := by
    intro m
    have h1 : (1 : ℝ) ≤
        min (max (M.ell m : ℝ) ((m : ℝ) ^ (1 / ((Real.log (m : ℝ)) ^ a)))) (M.p m : ℝ) :=
      le_min (le_trans (by exact_mod_cast hEll1 m) (le_max_left _ _))
        (by exact_mod_cast M.hp m)
    have h2 : (1 : ℝ) ≤ ((M.kIdx m : ℕ) : ℝ) := le_trans h1 (Nat.le_ceil _)
    exact_mod_cast h2
  have gauss_tail : ∀ a : ℝ, 0 ≤ a →
      (gaussianReal (0 : ℝ) 1) (Set.Ici a) ≤ ENNReal.ofReal (Real.exp (-(a ^ 2) / 2)) := by
    intro a ha
    rcases eq_or_lt_of_le ha with h0 | hpos
    · subst h0
      have h1 : (gaussianReal (0 : ℝ) 1) (Set.Ici (0 : ℝ)) ≤ 1 := by
        simpa using measure_mono (μ := gaussianReal (0 : ℝ) 1)
          (show Set.Ici (0 : ℝ) ⊆ Set.univ from Set.subset_univ _)
      simpa using h1
    · have hInt : Integrable (fun x : ℝ => Real.exp (a * x)) (gaussianReal (0 : ℝ) 1) :=
        ProbabilityTheory.integrable_exp_mul_gaussianReal a
      have hval : ∫ x, Real.exp (a * x) ∂(gaussianReal (0 : ℝ) 1) = Real.exp (a ^ 2 / 2) := by
        have h := congrFun (ProbabilityTheory.mgf_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : NNReal))) a
        simp only [ProbabilityTheory.mgf] at h
        simpa using h
      have hmarkov := MeasureTheory.mul_meas_ge_le_integral_of_nonneg
        (μ := gaussianReal (0 : ℝ) 1) (f := fun x : ℝ => Real.exp (a * x))
        (Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le)) hInt (Real.exp (a * a))
      rw [hval] at hmarkov
      have hset : {x : ℝ | Real.exp (a * a) ≤ Real.exp (a * x)} = Set.Ici a := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_Ici, Real.exp_le_exp]
        constructor
        · intro h
          by_contra hx
          push_neg at hx
          have hlt : a * x < a * a := mul_lt_mul_of_pos_left hx hpos
          linarith
        · intro h
          exact mul_le_mul_of_nonneg_left h ha
      rw [hset] at hmarkov
      have hstep : (gaussianReal (0 : ℝ) 1).real (Set.Ici a) ≤ Real.exp (-(a ^ 2) / 2) := by
        have h1 : (gaussianReal (0 : ℝ) 1).real (Set.Ici a) ≤
            Real.exp (a ^ 2 / 2) / Real.exp (a * a) := by
          rw [le_div_iff₀ (Real.exp_pos _)]
          calc (gaussianReal (0 : ℝ) 1).real (Set.Ici a) * Real.exp (a * a)
              = Real.exp (a * a) * (gaussianReal (0 : ℝ) 1).real (Set.Ici a) := mul_comm _ _
            _ ≤ Real.exp (a ^ 2 / 2) := hmarkov
        calc (gaussianReal (0 : ℝ) 1).real (Set.Ici a)
            ≤ Real.exp (a ^ 2 / 2) / Real.exp (a * a) := h1
          _ = Real.exp (-(a ^ 2) / 2) := by
              rw [← Real.exp_sub]
              congr 1
              ring
      exact Statlib.StatFoundation.BasicAnalysis.measure_le_ofReal_of_measureReal_le
        (gaussianReal (0 : ℝ) 1) (Set.Ici a) hstep

  suffices h : ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → M.kIdx n < M.p n → (M.tildeLaw n) {w : Fin (M.p n) → ℝ | fmax ((Finset.univ : Finset (Fin (M.p n))) \ M.J n (M.kIdx n)) (fun j => w j / (M.sigma n j) ^ (M.tau n)) > C * Real.rpow (M.kIdx n : ℝ) (-(alpha * (1 - M.tau n))) * Real.log (n : ℝ)} ≤ ENNReal.ofReal ((n : ℝ) ^ (-1 : ℤ)) from by
    obtain ⟨N₀, hN₀⟩ := h
    exact ⟨max N₀ 1, le_max_right _ _, fun n hn hk => hN₀ n (le_trans (le_max_left _ _) hn) hk⟩
  obtain ⟨ct, hctpos, hctev⟩ := hM.htau_cond
  have hev1 : ∀ᶠ n : ℕ in Filter.atTop,
      1 ≤ (C ^ 2 / (2 * (max cvar 1) ^ 2)) * (alpha * (1 - M.tau n))
        * (Real.log (n : ℝ)) ^ 2 := by
    have hApos : (0 : ℝ) < C ^ 2 / (2 * (max cvar 1) ^ 2) := by
      have h1 : (0 : ℝ) < max cvar 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
      positivity
    have hKpos : (0 : ℝ) < (C ^ 2 / (2 * (max cvar 1) ^ 2)) * alpha * ct := by positivity
    have hLtend : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    filter_upwards [hctev, hLtend.eventually (Filter.eventually_ge_atTop (1 : ℝ)),
      hLtend.eventually (Filter.eventually_ge_atTop
        (((C ^ 2 / (2 * (max cvar 1) ^ 2)) * alpha * ct)⁻¹))] with n hnct hL1 hLK
    have hLnn : (0 : ℝ) ≤ Real.log (n : ℝ) := by linarith
    have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (Real.log (n : ℝ)) := Real.one_le_sqrt.mpr hL1
    have h1 : ct * Real.sqrt (Real.log (n : ℝ)) ≤ (1 - M.tau n) * Real.log (n : ℝ) := by
      have h2 := mul_le_mul_of_nonneg_right hnct (Real.sqrt_nonneg (Real.log (n : ℝ)))
      rwa [mul_assoc, Real.mul_self_sqrt hLnn] at h2
    have h2 : ct * Real.sqrt (Real.log (n : ℝ)) * Real.log (n : ℝ)
        ≤ (1 - M.tau n) * Real.log (n : ℝ) * Real.log (n : ℝ) :=
      mul_le_mul_of_nonneg_right h1 hLnn
    have h3 : ct * Real.log (n : ℝ)
        ≤ ct * (Real.sqrt (Real.log (n : ℝ)) * Real.log (n : ℝ)) := by
      have hsq : Real.log (n : ℝ) ≤ Real.sqrt (Real.log (n : ℝ)) * Real.log (n : ℝ) := by
        have h := mul_le_mul_of_nonneg_right hsqrt1 hLnn
        linarith [h]
      exact mul_le_mul_of_nonneg_left hsq (le_of_lt hctpos)
    have h4 : (1 : ℝ) ≤ (C ^ 2 / (2 * (max cvar 1) ^ 2)) * alpha * ct * Real.log (n : ℝ) := by
      have h5 := mul_le_mul_of_nonneg_right hLK (le_of_lt hKpos)
      have h6 : ((C ^ 2 / (2 * (max cvar 1) ^ 2)) * alpha * ct)⁻¹
          * ((C ^ 2 / (2 * (max cvar 1) ^ 2)) * alpha * ct) = 1 :=
        inv_mul_cancel₀ (ne_of_gt hKpos)
      rw [h6] at h5
      linarith [h5]
    have hP : (0 : ℝ) ≤ (C ^ 2 / (2 * (max cvar 1) ^ 2)) * alpha := by positivity
    have hm1 : (C ^ 2 / (2 * (max cvar 1) ^ 2)) * alpha * ct * Real.log (n : ℝ)
        ≤ (C ^ 2 / (2 * (max cvar 1) ^ 2)) * alpha
          * (ct * (Real.sqrt (Real.log (n : ℝ)) * Real.log (n : ℝ))) := by
      have h := mul_le_mul_of_nonneg_left h3 hP
      linarith [h]
    have hm2 : (C ^ 2 / (2 * (max cvar 1) ^ 2)) * alpha
          * (ct * (Real.sqrt (Real.log (n : ℝ)) * Real.log (n : ℝ)))
        ≤ (C ^ 2 / (2 * (max cvar 1) ^ 2)) * (alpha * (1 - M.tau n))
          * (Real.log (n : ℝ)) ^ 2 := by
      have h := mul_le_mul_of_nonneg_left h2 hP
      linarith [h]
    linarith [h4, hm1, hm2]
  have hev2 : ∀ᶠ n : ℕ in Filter.atTop,
      2 * (M.kIdx n : ℝ) ^ 2 * Real.exp (-((C ^ 2 / (2 * (max cvar 1) ^ 2))
        * (Real.log (n : ℝ)) ^ 2)) ≤ Real.exp (-(Real.log (n : ℝ))) := by
    set A : ℝ := C ^ 2 / (2 * (max cvar 1) ^ 2) with hA
    have hApos : 0 < A := by
      rw [hA]
      have h1 : (0 : ℝ) < max cvar 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
      positivity
    have hLtend : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hL3ev : ∀ᶠ n : ℕ in Filter.atTop, (3 : ℝ) ≤ Real.log (n : ℝ) :=
      hLtend.eventually (Filter.eventually_ge_atTop 3)
    have hLA : ∀ᶠ n : ℕ in Filter.atTop, (20 : ℝ) ≤ A * Real.log (n : ℝ) := by
      have h := hLtend.eventually (Filter.eventually_ge_atTop (20 / A))
      filter_upwards [h] with n hn
      have h20 : A * (20 / A) = 20 := by field_simp
      have h2 := mul_le_mul_of_nonneg_left hn (le_of_lt hApos)
      rwa [h20] at h2
    filter_upwards [hL3ev, hLA] with n hL3le hLA20
    have hLpos : (0 : ℝ) < Real.log (n : ℝ) := by linarith
    have hL1 : (1 : ℝ) ≤ Real.log (n : ℝ) := by linarith
    have hn1 : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0
        rw [Nat.cast_zero, Real.log_zero] at hL3le
        norm_num at hL3le
      · exact h0
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hXa : (n : ℝ) ^ (1 / ((Real.log (n : ℝ)) ^ a))
        = Real.exp ((Real.log (n : ℝ)) ^ (1 - a)) := by
      rw [Real.rpow_def_of_pos hnpos]
      congr 1
      rw [Real.rpow_sub hLpos, Real.rpow_one, div_eq_mul_inv, div_eq_mul_inv, one_mul]
    have hloglog : 0 ≤ Real.log (Real.log (n : ℝ)) := Real.log_nonneg hL1
    have h1a1 : 1 - a ≤ 1 := by linarith
    have hLpowle : (Real.log (n : ℝ)) ^ (1 - a) ≤ Real.log (n : ℝ) := by
      calc (Real.log (n : ℝ)) ^ (1 - a)
          = Real.exp (Real.log (Real.log (n : ℝ)) * (1 - a)) := Real.rpow_def_of_pos hLpos _
        _ ≤ Real.exp (Real.log (Real.log (n : ℝ)) * 1) :=
            Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h1a1 hloglog)
        _ = Real.exp (Real.log (Real.log (n : ℝ))) := by rw [mul_one]
        _ = Real.log (n : ℝ) := Real.exp_log hLpos
    have hXle : (n : ℝ) ^ (1 / ((Real.log (n : ℝ)) ^ a)) ≤ (n : ℝ) := by
      have h2 : Real.exp ((Real.log (n : ℝ)) ^ (1 - a)) ≤ Real.exp (Real.log (n : ℝ)) :=
        Real.exp_le_exp.mpr hLpowle
      calc (n : ℝ) ^ (1 / ((Real.log (n : ℝ)) ^ a))
          = Real.exp ((Real.log (n : ℝ)) ^ (1 - a)) := hXa
        _ ≤ Real.exp (Real.log (n : ℝ)) := h2
        _ = (n : ℝ) := Real.exp_log hnpos
    have hkN : (M.kIdx n : ℝ) ≤ (Real.log (n : ℝ)) ^ 3 + 3 + (n : ℝ) := by
      have hceil : (M.kIdx n : ℝ)
          < min (max (M.ell n : ℝ) ((n : ℝ) ^ (1 / ((Real.log (n : ℝ)) ^ a))))
            (M.p n : ℝ) + 1 :=
        Nat.ceil_lt_add_one (le_min (le_trans (Nat.cast_nonneg _) (le_max_left _ _)) (Nat.cast_nonneg _))
      have h2 : min (max (M.ell n : ℝ) ((n : ℝ) ^ (1 / ((Real.log (n : ℝ)) ^ a))))
            (M.p n : ℝ)
          ≤ max (M.ell n : ℝ) ((n : ℝ) ^ (1 / ((Real.log (n : ℝ)) ^ a))) := min_le_left _ _
      have hell : (M.ell n : ℝ) ≤ (Real.log (n : ℝ)) ^ 3 + 2 := by
        have hellc : (M.ell n : ℝ)
            < min (max (1 : ℝ) ((Real.log (n : ℝ)) ^ 3)) (M.p n : ℝ) + 1 :=
          Nat.ceil_lt_add_one (le_min (le_trans zero_le_one (le_max_left _ _)) (Nat.cast_nonneg _))
        have h3 : min (max (1 : ℝ) ((Real.log (n : ℝ)) ^ 3)) (M.p n : ℝ)
            ≤ (Real.log (n : ℝ)) ^ 3 + 1 := by
          have h4 : (1 : ℝ) ≤ (Real.log (n : ℝ)) ^ 3 + 1 := by
            nlinarith [mul_nonneg (sq_nonneg (Real.log (n : ℝ)))
              (by linarith : (0 : ℝ) ≤ Real.log (n : ℝ))]
          have h5 : (Real.log (n : ℝ)) ^ 3 ≤ (Real.log (n : ℝ)) ^ 3 + 1 := by linarith
          exact le_trans (min_le_left _ _) (max_le h4 h5)
        linarith
      have h6 : max (M.ell n : ℝ) ((n : ℝ) ^ (1 / ((Real.log (n : ℝ)) ^ a)))
          ≤ (Real.log (n : ℝ)) ^ 3 + 2 + (n : ℝ) := max_le (by linarith) (by linarith)
      linarith
    have hkpos : (0 : ℝ) < (M.kIdx n : ℝ) := by exact_mod_cast hk1 n
    have hL3pos : (1 : ℝ) ≤ (Real.log (n : ℝ)) ^ 3 + 3 := by
      have h : (0 : ℝ) ≤ (Real.log (n : ℝ)) ^ 3 := by positivity
      linarith
    have hbig : (M.kIdx n : ℝ) ≤ 2 * ((n : ℝ) * ((Real.log (n : ℝ)) ^ 3 + 3)) := by
      have h2 : (n : ℝ) ≤ ((Real.log (n : ℝ)) ^ 3 + 3) * (n : ℝ) := by
        have h := mul_le_mul_of_nonneg_right hL3pos (le_of_lt hnpos)
        simpa using h
      have h3 : ((Real.log (n : ℝ)) ^ 3 + 3) ≤ ((Real.log (n : ℝ)) ^ 3 + 3) * (n : ℝ) := by
        have h := mul_le_mul_of_nonneg_left hn1' (by linarith : (0 : ℝ) ≤ (Real.log (n : ℝ)) ^ 3 + 3)
        simpa using h
      linarith
    have hlog2le : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have hlogk_le : Real.log ((M.kIdx n : ℝ)) ≤ 4 * Real.log (n : ℝ) + 1 := by
      have h1 : Real.log ((M.kIdx n : ℝ))
          ≤ Real.log (2 * ((n : ℝ) * ((Real.log (n : ℝ)) ^ 3 + 3))) :=
        Real.log_le_log hkpos hbig
      have h2 : Real.log (2 * ((n : ℝ) * ((Real.log (n : ℝ)) ^ 3 + 3)))
          = Real.log 2 + (Real.log (n : ℝ) + Real.log ((Real.log (n : ℝ)) ^ 3 + 3)) := by
        rw [Real.log_mul (by norm_num) (by positivity),
          Real.log_mul (ne_of_gt hnpos) (by linarith)]
      have h3 : Real.log ((Real.log (n : ℝ)) ^ 3 + 3) ≤ 3 * Real.log (n : ℝ) := by
        have h4 : Real.log ((Real.log (n : ℝ)) ^ 3 + 3)
            ≤ Real.log (4 * (Real.log (n : ℝ)) ^ 3) := by
          apply Real.log_le_log (by linarith)
          have hLL : (1 : ℝ) ≤ Real.log (n : ℝ) * Real.log (n : ℝ) := by
            have h : (1 : ℝ) * 1 ≤ Real.log (n : ℝ) * Real.log (n : ℝ) :=
              mul_le_mul hL1 hL1 zero_le_one (by linarith)
            simpa using h
          have hLLL : (1 : ℝ) ≤ Real.log (n : ℝ) * Real.log (n : ℝ) * Real.log (n : ℝ) := by
            have h : (1 : ℝ) * 1 ≤ (Real.log (n : ℝ) * Real.log (n : ℝ)) * Real.log (n : ℝ) :=
              mul_le_mul hLL hL1 zero_le_one (by positivity)
            simpa using h
          have hcube : (1 : ℝ) ≤ (Real.log (n : ℝ)) ^ 3 := by
            have h : (Real.log (n : ℝ)) ^ 3
                = Real.log (n : ℝ) * Real.log (n : ℝ) * Real.log (n : ℝ) := by ring
            linarith [hLLL, h]
          linarith
        have h5 : Real.log (4 * (Real.log (n : ℝ)) ^ 3)
            = Real.log 4 + 3 * Real.log (Real.log (n : ℝ)) := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
          push_cast
          ring
        have h6 : Real.log 4 ≤ 3 := by
          have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
          linarith
        have h7 : Real.log (Real.log (n : ℝ)) ≤ Real.log (n : ℝ) - 1 :=
          Real.log_le_sub_one_of_pos hLpos
        linarith
      linarith
    have hlog2k : Real.log (2 * (M.kIdx n : ℝ) ^ 2) ≤ 8 * Real.log (n : ℝ) + 3 := by
      have h1 : Real.log (2 * (M.kIdx n : ℝ) ^ 2)
          = Real.log 2 + 2 * Real.log ((M.kIdx n : ℝ)) := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
        push_cast
        ring
      linarith
    have hfinal : 8 * Real.log (n : ℝ) + 3
        ≤ A * (Real.log (n : ℝ)) ^ 2 - Real.log (n : ℝ) := by
      have h1 : 20 * Real.log (n : ℝ) ≤ A * (Real.log (n : ℝ)) ^ 2 := by
        have h := mul_le_mul_of_nonneg_right hLA20 (le_of_lt hLpos)
        calc 20 * Real.log (n : ℝ) ≤ (A * Real.log (n : ℝ)) * Real.log (n : ℝ) := h
          _ = A * (Real.log (n : ℝ)) ^ 2 := by ring
      linarith
    have hpos2 : (0 : ℝ) < 2 * (M.kIdx n : ℝ) ^ 2 := by positivity
    have hexp : 2 * (M.kIdx n : ℝ) ^ 2
        ≤ Real.exp (A * (Real.log (n : ℝ)) ^ 2 - Real.log (n : ℝ)) := by
      rw [← Real.exp_log hpos2]
      exact Real.exp_le_exp.mpr (le_trans hlog2k hfinal)
    calc 2 * (M.kIdx n : ℝ) ^ 2 * Real.exp (-(A * (Real.log (n : ℝ)) ^ 2))
        ≤ Real.exp (A * (Real.log (n : ℝ)) ^ 2 - Real.log (n : ℝ))
            * Real.exp (-(A * (Real.log (n : ℝ)) ^ 2)) :=
          mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le
      _ = Real.exp (-(Real.log (n : ℝ))) := by
          rw [← Real.exp_add]
          congr 1
          ring

  refine Filter.eventually_atTop.mp ?_
  filter_upwards [Filter.eventually_ge_atTop (a := 3), hctev, hev1, hev2] with n hn3 hnct hthr1 hthr2
  intro hk
  have hn : 0 < n := by omega
  have hsigpos : ∀ j : Fin (M.p n), 0 < M.sigma n j := fun j => hM.hsig_pos n hn j
  have hmarg : ∀ j : Fin (M.p n),
      (M.tildeLaw n).map (fun w => w j / (M.sigma n j) ^ (M.tau n))
        = (gaussianReal (0 : ℝ) 1).map (fun z => (M.sigma n j) ^ (1 - M.tau n) * z) :=
    (statopia_math_node_1043829637_02d50666 a c0 alpha cvar ccirc eps0 Ccor M hM n hn
      (hEll n)).2.2.2.2.2
  have coord_tail : ∀ (j : Fin (M.p n)) (t : ℝ), 0 < t →
      (M.tildeLaw n) {w : Fin (M.p n) → ℝ | w j / (M.sigma n j) ^ (M.tau n) > t}
        ≤ ENNReal.ofReal
            (Real.exp (-((t / (M.sigma n j) ^ (1 - M.tau n)) ^ 2) / 2)) := by
    intro j t ht
    have hc : 0 < (M.sigma n j) ^ (1 - M.tau n) := Real.rpow_pos_of_pos (hsigpos j) _
    have hmeas : Measurable fun w : Fin (M.p n) → ℝ => w j / (M.sigma n j) ^ (M.tau n) :=
      (measurable_pi_apply j).div_const _
    have hstep1 : (M.tildeLaw n) {w : Fin (M.p n) → ℝ | w j / (M.sigma n j) ^ (M.tau n) > t}
        = ((M.tildeLaw n).map
            (fun w : Fin (M.p n) → ℝ => w j / (M.sigma n j) ^ (M.tau n))) (Set.Ioi t) := by
      rw [Measure.map_apply hmeas measurableSet_Ioi]
      rfl
    rw [hstep1, hmarg j]
    have hstep2 : ((gaussianReal (0 : ℝ) 1).map
          (fun z : ℝ => (M.sigma n j) ^ (1 - M.tau n) * z)) (Set.Ioi t)
        = (gaussianReal (0 : ℝ) 1) {z : ℝ | (M.sigma n j) ^ (1 - M.tau n) * z > t} := by
      rw [Measure.map_apply (measurable_const_mul _) measurableSet_Ioi]
      rfl
    rw [hstep2]
    calc (gaussianReal (0 : ℝ) 1) {z : ℝ | (M.sigma n j) ^ (1 - M.tau n) * z > t}
        ≤ (gaussianReal (0 : ℝ) 1) (Set.Ici (t / (M.sigma n j) ^ (1 - M.tau n))) := by
          refine measure_mono ?_
          intro z hz
          simp only [Set.mem_setOf_eq] at hz
          simp only [Set.mem_Ici]
          rw [div_le_iff₀ hc]
          nlinarith [hz]
      _ ≤ ENNReal.ofReal (Real.exp (-((t / (M.sigma n j) ^ (1 - M.tau n)) ^ 2) / 2)) :=
          gauss_tail _ (le_of_lt (div_pos ht hc))
  set s : Finset (Fin (M.p n)) := (Finset.univ : Finset (Fin (M.p n))) \ M.J n (M.kIdx n) with hs
  set T : ℝ := C * ((M.kIdx n : ℝ) ^ (-(alpha * (1 - M.tau n)))) * Real.log (n : ℝ) with hTdef
  have hTnn : 0 ≤ T := by
    rw [hTdef]
    have hlog : 0 ≤ Real.log (n : ℝ) := by
      apply Real.log_nonneg
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
      linarith
    have hrpow : 0 ≤ (M.kIdx n : ℝ) ^ (-(alpha * (1 - M.tau n))) :=
      Real.rpow_nonneg (by positivity) _
    exact mul_nonneg (mul_nonneg hC.le hrpow) hlog
  have hsubset : {w : Fin (M.p n) → ℝ |
      fmax s (fun j => w j / (M.sigma n j) ^ (M.tau n)) > T}
      ⊆ ⋃ j ∈ s, {w : Fin (M.p n) → ℝ | w j / (M.sigma n j) ^ (M.tau n) > T} := by
    intro w hw
    simp only [Set.mem_setOf_eq] at hw
    have hex : ∃ j ∈ s, w j / (M.sigma n j) ^ (M.tau n) > T := by
      by_contra hcon
      push_neg at hcon
      have hle : fmax s (fun j => w j / (M.sigma n j) ^ (M.tau n)) ≤ T := by
        rcases Finset.eq_empty_or_nonempty s with h0 | hne
        · rw [h0]
          have hem : fmax (∅ : Finset (Fin (M.p n)))
              (fun j => w j / (M.sigma n j) ^ (M.tau n)) = 0 := by
            simp only [fmax, Finset.coe_empty, Set.image_empty, Real.sSup_empty]
          rw [hem]
          linarith
        · show sSup ((fun j : Fin (M.p n) => w j / (M.sigma n j) ^ (M.tau n)) ''
            (s : Set (Fin (M.p n)))) ≤ T
          refine csSup_le ?_ ?_
          · obtain ⟨j0, hj0⟩ := hne
            exact ⟨_, j0, by simpa using hj0, rfl⟩
          · rintro b ⟨j, hj, rfl⟩
            exact hcon j (by simpa using hj)
      linarith
    obtain ⟨j, hj, hjt⟩ := hex
    simp only [Set.mem_iUnion, exists_prop]
    exact ⟨j, hj, hjt⟩
  have hmono : (M.tildeLaw n) {w : Fin (M.p n) → ℝ |
      fmax s (fun j => w j / (M.sigma n j) ^ (M.tau n)) > T}
      ≤ ∑ j ∈ s, (M.tildeLaw n)
          {w : Fin (M.p n) → ℝ | w j / (M.sigma n j) ^ (M.tau n) > T} := by
    refine le_trans (measure_mono (μ := M.tildeLaw n) hsubset) ?_
    exact measure_biUnion_finset_le s _
  have hTpos : 0 < T := by
    rw [hTdef]
    have hlog : 0 < Real.log (n : ℝ) := by
      apply Real.log_pos
      have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
      linarith
    have hkpos : (0 : ℝ) < (M.kIdx n : ℝ) := by
      exact_mod_cast (show 0 < M.kIdx n by have := hk1 n; omega)
    have hrpow : 0 < (M.kIdx n : ℝ) ^ (-(alpha * (1 - M.tau n))) :=
      Real.rpow_pos_of_pos hkpos _
    exact mul_pos (mul_pos hC hrpow) hlog
  have htau0 : 0 ≤ M.tau n := (hM.htau_mem n).1
  have htau1 : M.tau n < 1 := (hM.htau_mem n).2
  have hone_sub_pos : (0 : ℝ) < 1 - M.tau n := by linarith
  have hone_sub_le : 1 - M.tau n ≤ 1 := by linarith
  have hbeta_pos : 0 < alpha * (1 - M.tau n) := mul_pos halpha hone_sub_pos
  set cp : ℝ := max cvar 1 with hcp
  have hcp1 : (1 : ℝ) ≤ cp := le_max_right _ _
  have hcppos : (0 : ℝ) < cp := lt_of_lt_of_le one_pos hcp1
  have hcvle : cvar ≤ cp := le_max_left _ _
  set c1 : ℝ := C ^ 2 / (2 * cp ^ 2) with hc1
  have hc1pos : 0 < c1 := by
    rw [hc1]
    positivity

  have hterm : ∀ j ∈ s, (M.tildeLaw n)
      {w : Fin (M.p n) → ℝ | w j / (M.sigma n j) ^ (M.tau n) > T}
      ≤ ENNReal.ofReal (Real.exp (-((T / (M.sigma n j) ^ (1 - M.tau n)) ^ 2) / 2)) :=
    fun j _ => coord_tail j T hTpos
  refine le_trans hmono ?_
  refine le_trans (Finset.sum_le_sum fun j hj => hterm j hj) ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => (Real.exp_pos _).le)]
  apply ENNReal.ofReal_le_ofReal
  have hR : Real.exp (-(Real.log (n : ℝ))) = (n : ℝ) ^ (-1 : ℤ) := by
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [zpow_neg_one, Real.exp_neg, Real.exp_log hnpos]
  rw [← hR]
  have hrank : ∀ j ∈ s, M.kIdx n ≤ ((M.g n).symm j : ℕ) + 1 := by
    intro j hj
    by_contra hlt
    have hlt' : ((M.g n).symm j : ℕ) < M.kIdx n := by omega
    have hJ : j ∈ M.J n (M.kIdx n) := by
      simp only [Model.J, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨(M.g n).symm j, hlt', (M.g n).apply_symm_apply j⟩
    have hnot : j ∉ M.J n (M.kIdx n) := by
      have h2 := hj
      rw [hs] at h2
      exact (Finset.mem_sdiff.mp h2).2
    exact hnot hJ
  have hcp_le : cp ^ (1 - M.tau n) ≤ cp := by
    have hlogcp : 0 ≤ Real.log cp := Real.log_nonneg hcp1
    calc cp ^ (1 - M.tau n) = Real.exp (Real.log cp * (1 - M.tau n)) :=
          Real.rpow_def_of_pos hcppos _
      _ ≤ Real.exp (Real.log cp) := by
          apply Real.exp_le_exp.mpr
          linarith [mul_le_mul_of_nonneg_left hone_sub_le hlogcp]
      _ = cp := Real.exp_log hcppos
  have hsig_bound : ∀ j ∈ s, M.sigma n j ^ (1 - M.tau n)
      ≤ cp * ((((M.g n).symm j : ℕ) + 1 : ℕ) : ℝ) ^ (-(alpha * (1 - M.tau n))) := by
    intro j hj
    have hr : (0 : ℝ) < ((((M.g n).symm j : ℕ) + 1 : ℕ) : ℝ) := by positivity
    have hsu := hM.hsig_upper n hn ((M.g n).symm j) (hrank j hj)
    rw [(M.g n).apply_symm_apply j] at hsu
    have hs' : M.sigma n j ≤ cp * ((((M.g n).symm j : ℕ) + 1 : ℕ) : ℝ) ^ (-alpha) :=
      le_trans hsu (mul_le_mul_of_nonneg_right hcvle (Real.rpow_nonneg (le_of_lt hr) _))
    have h1 : M.sigma n j ^ (1 - M.tau n)
        ≤ (cp * ((((M.g n).symm j : ℕ) + 1 : ℕ) : ℝ) ^ (-alpha)) ^ (1 - M.tau n) :=
      Real.rpow_le_rpow (le_of_lt (hsigpos j)) hs' (le_of_lt hone_sub_pos)
    have h2 : (cp * ((((M.g n).symm j : ℕ) + 1 : ℕ) : ℝ) ^ (-alpha)) ^ (1 - M.tau n)
        = cp ^ (1 - M.tau n)
          * (((((M.g n).symm j : ℕ) + 1 : ℕ) : ℝ) ^ (-alpha)) ^ (1 - M.tau n) :=
      Real.mul_rpow (le_of_lt hcppos) (Real.rpow_nonneg (le_of_lt hr) _)
    have h3 : (((((M.g n).symm j : ℕ) + 1 : ℕ) : ℝ) ^ (-alpha)) ^ (1 - M.tau n)
        = ((((M.g n).symm j : ℕ) + 1 : ℕ) : ℝ) ^ ((-alpha) * (1 - M.tau n)) :=
      (Real.rpow_mul (le_of_lt hr) (-alpha) (1 - M.tau n)).symm
    have h4 : cp ^ (1 - M.tau n)
          * (((((M.g n).symm j : ℕ) + 1 : ℕ) : ℝ) ^ (-alpha)) ^ (1 - M.tau n)
        ≤ cp * ((((M.g n).symm j : ℕ) + 1 : ℕ) : ℝ) ^ (-(alpha * (1 - M.tau n))) := by
      have hb : (0 : ℝ) ≤ ((((M.g n).symm j : ℕ) + 1 : ℕ) : ℝ) ^ ((-alpha) * (1 - M.tau n)) :=
        Real.rpow_nonneg (le_of_lt hr) _
      have he : (-alpha) * (1 - M.tau n) = -(alpha * (1 - M.tau n)) := by ring
      calc cp ^ (1 - M.tau n)
            * (((((M.g n).symm j : ℕ) + 1 : ℕ) : ℝ) ^ (-alpha)) ^ (1 - M.tau n)
          = cp ^ (1 - M.tau n)
            * ((((M.g n).symm j : ℕ) + 1 : ℕ) : ℝ) ^ ((-alpha) * (1 - M.tau n)) := by rw [h3]
        _ ≤ cp * ((((M.g n).symm j : ℕ) + 1 : ℕ) : ℝ) ^ ((-alpha) * (1 - M.tau n)) :=
            mul_le_mul_of_nonneg_right hcp_le hb
        _ = cp * ((((M.g n).symm j : ℕ) + 1 : ℕ) : ℝ) ^ (-(alpha * (1 - M.tau n))) := by
            rw [he]
    exact h1.trans (h2.trans_le h4)
  have hharm : ∀ m : ℕ, ∑ i ∈ Finset.range m, ((((i : ℕ) + 1 : ℕ) : ℝ))⁻¹ ^ 2 ≤ 2 := by
    intro m
    have key : ∀ p : ℕ, 1 ≤ p →
        ∑ i ∈ Finset.range p, ((((i : ℕ) + 1 : ℕ) : ℝ))⁻¹ ^ 2 ≤ 2 - ((p : ℝ))⁻¹ := by
      intro p hp
      induction p with
      | zero => omega
      | succ q ih =>
          rcases Nat.eq_zero_or_pos q with hq | hq
          · subst hq
            norm_num
          · rw [Finset.sum_range_succ]
            have ih' := ih (by omega : 1 ≤ q)
            have hstep : ((((q : ℕ) + 1 : ℕ) : ℝ))⁻¹ ^ 2
                ≤ ((q : ℝ))⁻¹ - (((q : ℕ) + 1 : ℕ) : ℝ)⁻¹ := by
              have hq1 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
              have e : (((q : ℕ) + 1 : ℕ) : ℝ) = ((q : ℝ) + 1) := by push_cast; ring
              rw [e]
              have hq2 : (0 : ℝ) < ((q : ℝ) + 1) := by positivity
              field_simp
              linarith
            linarith
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0
      simp
    · have h1 := key m hpos
      have h2 : (0 : ℝ) ≤ ((m : ℝ))⁻¹ := by positivity
      linarith
  have hsum_rank : ∑ j ∈ s, (((((M.g n).symm j : ℕ) + 1 : ℕ) : ℝ))⁻¹ ^ 2 ≤ 2 := by
    have huniv : ∑ j : Fin (M.p n), (((((M.g n).symm j : ℕ) + 1 : ℕ) : ℝ))⁻¹ ^ 2
        = ∑ i : Fin (M.p n), ((((i : ℕ) + 1 : ℕ) : ℝ))⁻¹ ^ 2 :=
      Equiv.sum_comp (M.g n).symm (fun i : Fin (M.p n) => ((((i : ℕ) + 1 : ℕ) : ℝ))⁻¹ ^ 2)
    have hsub : ∑ j ∈ s, (((((M.g n).symm j : ℕ) + 1 : ℕ) : ℝ))⁻¹ ^ 2
        ≤ ∑ j : Fin (M.p n), (((((M.g n).symm j : ℕ) + 1 : ℕ) : ℝ))⁻¹ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) (fun i _ _ => by positivity)
    have hfin : ∑ i : Fin (M.p n), ((((i : ℕ) + 1 : ℕ) : ℝ))⁻¹ ^ 2 ≤ 2 := by
      rw [show ∑ i : Fin (M.p n), ((((i : ℕ) + 1 : ℕ) : ℝ))⁻¹ ^ 2
          = ∑ i ∈ Finset.range (M.p n), ((((i : ℕ) + 1 : ℕ) : ℝ))⁻¹ ^ 2 from
        Fin.sum_univ_eq_sum_range (fun m : ℕ => ((((m : ℕ) + 1 : ℕ) : ℝ))⁻¹ ^ 2) (M.p n)]
      exact hharm (M.p n)
    linarith
  have hthr1' : 1 ≤ c1 * (alpha * (1 - M.tau n)) * (Real.log (n : ℝ)) ^ 2 := hthr1
  have hthr2' : 2 * (M.kIdx n : ℝ) ^ 2 * Real.exp (-(c1 * (Real.log (n : ℝ)) ^ 2))
      ≤ Real.exp (-(Real.log (n : ℝ))) := hthr2
  have hLpos : (0 : ℝ) < Real.log (n : ℝ) := by
    apply Real.log_pos
    have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    linarith
  have hpoint : ∀ j ∈ s, Real.exp (-((T / (M.sigma n j) ^ (1 - M.tau n)) ^ 2) / 2)
      ≤ Real.exp (-(c1 * (Real.log (n : ℝ)) ^ 2))
        * ((M.kIdx n : ℝ) ^ 2 * (((((M.g n).symm j : ℕ) + 1 : ℕ) : ℝ))⁻¹ ^ 2) := by
    intro j hj
    set rr : ℝ := ((((M.g n).symm j : ℕ) + 1 : ℕ) : ℝ) with hrr
    set kk : ℝ := (M.kIdx n : ℝ) with hkk
    have hr : (0 : ℝ) < rr := by rw [hrr]; positivity
    have hk : (0 : ℝ) < kk := by
      rw [hkk]
      exact_mod_cast (show 0 < M.kIdx n by have := hk1 n; omega)
    have hpos_div : (0 : ℝ) < rr / kk := div_pos hr hk
    have hle := hsig_bound j hj
    rw [← hrr] at hle
    have hapos : (0 : ℝ) < M.sigma n j ^ (1 - M.tau n) := Real.rpow_pos_of_pos (hsigpos j) _
    have hbpos : (0 : ℝ) < cp * rr ^ (-(alpha * (1 - M.tau n))) :=
      mul_pos hcppos (Real.rpow_pos_of_pos hr _)
    have hden : T / (cp * rr ^ (-(alpha * (1 - M.tau n))))
        ≤ T / M.sigma n j ^ (1 - M.tau n) := by
      rw [le_div_iff₀ hapos, div_mul_eq_mul_div, div_le_iff₀ hbpos]
      exact mul_le_mul_of_nonneg_left hle hTpos.le
    have hTb : T / (cp * rr ^ (-(alpha * (1 - M.tau n))))
        = (C / cp) * ((rr / kk) ^ (alpha * (1 - M.tau n))) * Real.log (n : ℝ) := by
      rw [hTdef]
      rw [Real.div_rpow (le_of_lt hr) (le_of_lt hk)]
      have h1 : rr ^ (alpha * (1 - M.tau n)) = (rr ^ (-(alpha * (1 - M.tau n))))⁻¹ := by
        rw [Real.rpow_neg (le_of_lt hr), inv_inv]
      have h2 : kk ^ (alpha * (1 - M.tau n)) = (kk ^ (-(alpha * (1 - M.tau n))))⁻¹ := by
        rw [Real.rpow_neg (le_of_lt hk), inv_inv]
      have hnr : rr ^ (-(alpha * (1 - M.tau n))) ≠ 0 := (Real.rpow_pos_of_pos hr _).ne'
      have hnk : kk ^ (-(alpha * (1 - M.tau n))) ≠ 0 := (Real.rpow_pos_of_pos hk _).ne'
      have hcpn : cp ≠ 0 := hcppos.ne'
      rw [h1, h2]
      field_simp
    have hsq1 : ((T / (cp * rr ^ (-(alpha * (1 - M.tau n))))) ^ 2) / 2
        = c1 * ((rr / kk) ^ (2 * (alpha * (1 - M.tau n)))) * (Real.log (n : ℝ)) ^ 2 := by
      rw [hTb, hc1]
      have hpw : ((rr / kk) ^ (alpha * (1 - M.tau n))) ^ 2
          = (rr / kk) ^ (2 * (alpha * (1 - M.tau n))) := by
        rw [← Real.rpow_mul_natCast (le_of_lt hpos_div) (alpha * (1 - M.tau n)) 2]
        rw [show (alpha * (1 - M.tau n)) * ((2 : ℕ) : ℝ) = 2 * (alpha * (1 - M.tau n)) by
          push_cast
          ring]
      have hcpn : cp ≠ 0 := hcppos.ne'
      rw [mul_pow, mul_pow, hpw]
      field_simp
    have hsqmono : (T / (cp * rr ^ (-(alpha * (1 - M.tau n))))) ^ 2
        ≤ (T / M.sigma n j ^ (1 - M.tau n)) ^ 2 := by
      have h1 : (0 : ℝ) ≤ T / (cp * rr ^ (-(alpha * (1 - M.tau n)))) :=
        le_of_lt (div_pos hTpos hbpos)
      have h2 := mul_self_le_mul_self h1 hden
      calc (T / (cp * rr ^ (-(alpha * (1 - M.tau n))))) ^ 2
          = (T / (cp * rr ^ (-(alpha * (1 - M.tau n)))))
              * (T / (cp * rr ^ (-(alpha * (1 - M.tau n))))) := by ring
        _ ≤ (T / M.sigma n j ^ (1 - M.tau n)) * (T / M.sigma n j ^ (1 - M.tau n)) := h2
        _ = (T / M.sigma n j ^ (1 - M.tau n)) ^ 2 := by ring
    have hu1 : 1 ≤ rr / kk := by
      rw [le_div_iff₀ hk, hkk, hrr]
      have h' : ((M.kIdx n : ℕ) : ℝ) ≤ ((((M.g n).symm j : ℕ) + 1 : ℕ) : ℝ) := by
        exact_mod_cast hrank j hj
      linarith
    have hulog : 0 ≤ Real.log (rr / kk) := Real.log_nonneg hu1
    have hgrowth : 1 + Real.log (rr / kk) * (2 * (alpha * (1 - M.tau n)))
        ≤ (rr / kk) ^ (2 * (alpha * (1 - M.tau n))) := by
      have h2 : (rr / kk) ^ (2 * (alpha * (1 - M.tau n)))
          = Real.exp (Real.log (rr / kk) * (2 * (alpha * (1 - M.tau n)))) :=
        Real.rpow_def_of_pos hpos_div _
      rw [h2]
      linarith [Real.add_one_le_exp (Real.log (rr / kk) * (2 * (alpha * (1 - M.tau n))))]
    have hbe1 : 1 ≤ c1 * (Real.log (n : ℝ)) ^ 2 * (alpha * (1 - M.tau n)) := by
      calc (1 : ℝ) ≤ c1 * (alpha * (1 - M.tau n)) * (Real.log (n : ℝ)) ^ 2 := hthr1'
        _ = c1 * (Real.log (n : ℝ)) ^ 2 * (alpha * (1 - M.tau n)) := by ring
    have hexp2 : 2 * Real.log (rr / kk)
        ≤ c1 * (Real.log (n : ℝ)) ^ 2 * ((rr / kk) ^ (2 * (alpha * (1 - M.tau n))) - 1) := by
      have hc1L : 0 ≤ c1 * (Real.log (n : ℝ)) ^ 2 := mul_nonneg hc1pos.le (sq_nonneg _)
      have hgr : 2 * (alpha * (1 - M.tau n)) * Real.log (rr / kk)
          ≤ (rr / kk) ^ (2 * (alpha * (1 - M.tau n))) - 1 := by linarith [hgrowth]
      have sA : 2 * Real.log (rr / kk)
          ≤ (c1 * (Real.log (n : ℝ)) ^ 2 * (alpha * (1 - M.tau n))) * (2 * Real.log (rr / kk)) := by
        calc 2 * Real.log (rr / kk) = 1 * (2 * Real.log (rr / kk)) := by ring
          _ ≤ (c1 * (Real.log (n : ℝ)) ^ 2 * (alpha * (1 - M.tau n)))
                * (2 * Real.log (rr / kk)) := mul_le_mul_of_nonneg_right hbe1 (by linarith)
      have sB : (c1 * (Real.log (n : ℝ)) ^ 2 * (alpha * (1 - M.tau n)))
            * (2 * Real.log (rr / kk))
          ≤ c1 * (Real.log (n : ℝ)) ^ 2 * ((rr / kk) ^ (2 * (alpha * (1 - M.tau n))) - 1) := by
        calc (c1 * (Real.log (n : ℝ)) ^ 2 * (alpha * (1 - M.tau n))) * (2 * Real.log (rr / kk))
            = c1 * (Real.log (n : ℝ)) ^ 2
              * (2 * (alpha * (1 - M.tau n)) * Real.log (rr / kk)) := by ring
          _ ≤ c1 * (Real.log (n : ℝ)) ^ 2 * ((rr / kk) ^ (2 * (alpha * (1 - M.tau n))) - 1) :=
              mul_le_mul_of_nonneg_left hgr hc1L
      linarith [sA, sB]
    have hu2 : Real.exp (2 * Real.log (rr / kk)) = (rr / kk) ^ 2 := by
      have h2 : (2 : ℝ) * Real.log (rr / kk)
          = Real.log (rr / kk) + Real.log (rr / kk) := by ring
      rw [h2, Real.exp_add, Real.exp_log hpos_div]
      ring
    have hkey : Real.exp (-(c1 * ((rr / kk) ^ (2 * (alpha * (1 - M.tau n))))
            * (Real.log (n : ℝ)) ^ 2)) * ((rr / kk) ^ 2)
        ≤ Real.exp (-(c1 * (Real.log (n : ℝ)) ^ 2)) := by
      rw [← hu2, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h9 := hexp2
      have h10 : c1 * (Real.log (n : ℝ)) ^ 2 * ((rr / kk) ^ (2 * (alpha * (1 - M.tau n))) - 1)
          = c1 * (Real.log (n : ℝ)) ^ 2 * (rr / kk) ^ (2 * (alpha * (1 - M.tau n)))
            - c1 * (Real.log (n : ℝ)) ^ 2 := by ring
      linarith [h9, h10]
    have hu2pos : (0 : ℝ) < (rr / kk) ^ 2 := pow_pos hpos_div 2
    have hexp_le : Real.exp (-(c1 * ((rr / kk) ^ (2 * (alpha * (1 - M.tau n))))
            * (Real.log (n : ℝ)) ^ 2))
        ≤ Real.exp (-(c1 * (Real.log (n : ℝ)) ^ 2)) * ((rr / kk) ^ 2)⁻¹ := by
      have h2 : Real.exp (-(c1 * ((rr / kk) ^ (2 * (alpha * (1 - M.tau n))))
              * (Real.log (n : ℝ)) ^ 2))
          ≤ Real.exp (-(c1 * (Real.log (n : ℝ)) ^ 2)) / ((rr / kk) ^ 2) := by
        rw [le_div_iff₀ hu2pos]
        simpa [mul_assoc] using hkey
      simpa [div_eq_mul_inv] using h2
    have hconv : ((rr / kk) ^ 2)⁻¹ = kk ^ 2 * (rr⁻¹) ^ 2 := by
      have hkn : kk ≠ 0 := hk.ne'
      have hrn : rr ≠ 0 := hr.ne'
      field_simp
    calc Real.exp (-((T / (M.sigma n j) ^ (1 - M.tau n)) ^ 2) / 2)
        ≤ Real.exp (-(c1 * ((rr / kk) ^ (2 * (alpha * (1 - M.tau n))))
            * (Real.log (n : ℝ)) ^ 2)) := by
          apply Real.exp_le_exp.mpr
          linarith [hsq1, hsqmono]
      _ ≤ Real.exp (-(c1 * (Real.log (n : ℝ)) ^ 2)) * ((rr / kk) ^ 2)⁻¹ := hexp_le
      _ = Real.exp (-(c1 * (Real.log (n : ℝ)) ^ 2)) * (kk ^ 2 * (rr⁻¹) ^ 2) := by rw [hconv]
      _ = Real.exp (-(c1 * (Real.log (n : ℝ)) ^ 2))
            * ((M.kIdx n : ℝ) ^ 2 * (((((M.g n).symm j : ℕ) + 1 : ℕ) : ℝ))⁻¹ ^ 2) := by
          rw [hkk, hrr]
  have hsum_le : ∑ j ∈ s, Real.exp (-((T / M.sigma n j ^ (1 - M.tau n)) ^ 2) / 2)
      ≤ Real.exp (-(c1 * (Real.log (n : ℝ)) ^ 2))
        * ((M.kIdx n : ℝ) ^ 2 * ∑ j ∈ s, (((((M.g n).symm j : ℕ) + 1 : ℕ) : ℝ))⁻¹ ^ 2) := by
    refine le_trans (Finset.sum_le_sum fun j hj => hpoint j hj) (le_of_eq ?_)
    rw [Finset.mul_sum, Finset.mul_sum]
  calc ∑ j ∈ s, Real.exp (-((T / M.sigma n j ^ (1 - M.tau n)) ^ 2) / 2)
      ≤ Real.exp (-(c1 * (Real.log (n : ℝ)) ^ 2))
        * ((M.kIdx n : ℝ) ^ 2 * ∑ j ∈ s, (((((M.g n).symm j : ℕ) + 1 : ℕ) : ℝ))⁻¹ ^ 2) := hsum_le
    _ ≤ Real.exp (-(c1 * (Real.log (n : ℝ)) ^ 2)) * ((M.kIdx n : ℝ) ^ 2 * 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum_rank (sq_nonneg _))
          (Real.exp_pos _).le
    _ = 2 * (M.kIdx n : ℝ) ^ 2 * Real.exp (-(c1 * (Real.log (n : ℝ)) ^ 2)) := by ring
    _ ≤ Real.exp (-(Real.log (n : ℝ))) := hthr2'
  /- @proof-region region.target-node.session.91b893579eacbcc3 end -/

end
end Statlib.Imported

