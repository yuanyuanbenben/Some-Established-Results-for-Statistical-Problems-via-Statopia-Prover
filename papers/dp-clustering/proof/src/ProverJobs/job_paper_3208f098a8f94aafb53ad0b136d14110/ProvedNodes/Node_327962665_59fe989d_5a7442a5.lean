import Statlib.StatFoundation.BasicAnalysis.ENNRealBridge
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.Vocabulary
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.Base
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.ProvedNodes.Node_1445702134_3c8d3810_8f7a15fe
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.ProvedNodes.Node_3224678180_5a630a9f_7124eef7
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.ProvedNodes.Node_3788355289_2a3e6b7e_b3f2870a
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.ProvedNodes.Node_4213379669_bb9a52d2_f7733836



open MeasureTheory
open Statlib.Imported

noncomputable section
open MeasureTheory
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_327962665_59fe989d : ∀ (t : ℝ) (ht : 1 ≤ t)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1 / 2)
    (δ β : ℝ) (hδ : 0 < δ) (hβ : 0 < β)
    (π : ℝ → ℝ) (hπ_meas : Measurable π)
    (hπ_nonneg : ∀ α ∈ Set.Ioi (0 : ℝ), 0 ≤ π α)
    (hπ_prob : ∫⁻ α in Set.Ioi (0 : ℝ), ENNReal.ofReal (π α) = 1)
    (hA2 : ∀ α ∈ Set.Ioo (0 : ℝ) ε, δ⁻¹ * α ^ β ≤ π α ∧ π α ≤ δ * α ^ β),
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ n : ℕ, t + 1 ≤ (n : ℝ) →
        IntegrableOn (fun α : ℝ => α ^ t / risingFac α n * π α) (Set.Ioo (0 : ℝ) ε) ∧
          0 < ∫ α in Set.Ioo (0 : ℝ) ε, α ^ t / risingFac α n * π α ∧
            IntegrableOn (fun α : ℝ => α ^ t / risingFac α n * π α) (Set.Ioi ε) ∧
              (∫ α in Set.Ioi ε, α ^ t / risingFac α n * π α) ≤
                C * (n : ℝ) ^ (-ε) * (1 + Real.log (n : ℝ)) ^ K *
                  (∫ α in Set.Ioo (0 : ℝ) ε, α ^ t / risingFac α n * π α) := by
  /- @proof-region region.target-node.session.16f84b4399f51e47 begin -/
  intro t ht eps h_eps h_eps_lt delta beta h_delta h_beta pi hpi_meas hpi_nonneg hpi_prob hA2
  have hIoi0 : MeasurableSet (Set.Ioi (0 : ℝ)) := measurableSet_Ioi
  have hpi_ae : 0 ≤ᶠ[ae (volume.restrict (Set.Ioi (0 : ℝ)))] pi := by
    filter_upwards [MeasureTheory.ae_restrict_mem hIoi0] with a ha
    exact hpi_nonneg a ha
  have hpi_intble : Integrable pi (volume.restrict (Set.Ioi (0 : ℝ))) := by
    rw [← MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hpi_meas.aestronglyMeasurable hpi_ae]
    rw [hpi_prob]
    exact ENNReal.one_ne_top
  have hpi_prob_real : ∫ a in Set.Ioi (0 : ℝ), pi a = 1 := by
    rw [Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.integral_eq_lintegral_toReal_of_nonneg hpi_ae hpi_intble, hpi_prob]
    simp
  have hdep := statopia_math_node_3788355289_2a3e6b7e t ht pi hpi_meas hpi_nonneg hpi_prob eps delta beta h_eps h_delta h_beta hA2
  obtain ⟨m, htm, hmn⟩ :
      ∃ m : ℕ, t ≤ (m : ℝ) ∧ ∀ n : ℕ, (n : ℝ) ≥ t + 1 → (m : ℝ) ≤ (n : ℝ) - 1 := by
    refine ⟨⌈t⌉₊, Nat.le_ceil t, ?_⟩
    intro n hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by linarith
    have hn1' : 1 ≤ n := by exact_mod_cast hn1
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub hn1']
      norm_num
    have hle : ⌈t⌉₊ ≤ n - 1 := by
      rw [Nat.ceil_le]
      rw [hcast]
      linarith
    calc (⌈t⌉₊ : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hle
      _ = (n : ℝ) - 1 := hcast
  set K : ℝ := t + beta + 1 with hK
  have hK0 : 0 ≤ K := by positivity
  obtain ⟨hrf_pos, hrf_pow, hrf_fact, hrf_monoOn, hrf_mono, hrf_posε, hrf_anti⟩ :=
    statopia_math_node_1445702134_3c8d3810
  have hlog_lower : ∀ u : ℝ, 0 ≤ u → u / (1 + u) ≤ Real.log (1 + u) := by
    intro u hu
    have h1 : (0 : ℝ) < 1 + u := by linarith
    have h2 : Real.log ((1 + u)⁻¹) ≤ (1 + u)⁻¹ - 1 := Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_inv] at h2
    have h3 : (1 + u)⁻¹ - 1 = -(u / (1 + u)) := by
      field_simp
      ring
    rw [h3] at h2
    linarith
  have hlog_upper : ∀ u : ℝ, 0 ≤ u → Real.log (1 + u) ≤ u := by
    intro u hu
    have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + u by linarith)
    linarith
  have htel : ∀ m : ℕ,
      ∑ j ∈ Finset.range m, (Real.log ((j:ℝ)+2) - Real.log ((j:ℝ)+1)) =
        Real.log ((m:ℝ)+1) := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      rw [show (k:ℝ) + 1 + 1 = (k:ℝ) + 2 by ring]
      ring
  have hHarm : ∀ m : ℕ, Real.log ((m:ℝ)+1) ≤ ∑ k ∈ Finset.range m, (1/((k:ℝ)+1)) := by
    intro m
    rw [← htel m]
    apply Finset.sum_le_sum
    intro k hk
    have hsplit : Real.log ((k:ℝ)+2) - Real.log ((k:ℝ)+1)
        = Real.log (((k:ℝ)+2)/((k:ℝ)+1)) :=
      (Real.log_div (by positivity) (by positivity)).symm
    rw [hsplit]
    have h2 : ((k:ℝ)+2)/((k:ℝ)+1) = 1 + 1/((k:ℝ)+1) := by
      field_simp
      ring
    rw [h2]
    exact hlog_upper _ (by positivity)
  have hShiftUpper : ∀ m : ℕ, (∑ k ∈ Finset.range m, (1/((k:ℝ)+2))) ≤ Real.log ((m:ℝ)+1) := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ]
      have hstep : 1/((k:ℝ)+2) ≤ Real.log ((k:ℝ)+2) - Real.log ((k:ℝ)+1) := by
        rw [← Real.log_div (by positivity) (by positivity)]
        have hsp : ((k:ℝ)+2)/((k:ℝ)+1) = 1 + 1/((k:ℝ)+1) := by
          field_simp
          ring
        rw [hsp]
        have h := hlog_lower (1/((k:ℝ)+1)) (by positivity)
        have he : (1/((k:ℝ)+1))/(1 + 1/((k:ℝ)+1)) = 1/((k:ℝ)+2) := by
          field_simp
          ring
        rw [he] at h
        exact h
      have hc : ((k+1:ℕ):ℝ) + 1 = (k:ℝ) + 2 := by
        push_cast
        ring
      rw [hc]
      linarith [ih, hstep]
  have hP1 : ∀ (n : ℕ) (a : ℝ), 1 ≤ n → 0 < a → a ≤ 1 →
      risingFac a n ≤ Real.exp 1 * (n : ℝ) ^ a * ((n - 1).factorial : ℝ) := by
    intro n a hn hapos ha1
    rcases eq_or_lt_of_le hn with hn1 | hn2
    · have hn1' : n = 1 := hn1.symm
      subst hn1'
      have hrf1 : risingFac a 1 = a := by
        unfold risingFac
        simp
      rw [hrf1]
      have h2 : a ≤ Real.exp 1 := by
        have h3 := Real.add_one_le_exp 1
        linarith
      simpa using h2
    · have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
      have hrf : risingFac a n = a * ∏ k ∈ Finset.range (n - 1), (a + ((k:ℝ)+1)) := by
        unfold risingFac
        conv_lhs => rw [show n = (n - 1) + 1 by omega]
        rw [Finset.prod_range_succ']
        simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero]
        ring
      have hfac : (∏ k ∈ Finset.range (n-1), ((k:ℝ)+1)) = ((n-1).factorial : ℝ) := by
        have hgen : ∀ m : ℕ, (∏ k ∈ Finset.range m, ((k:ℝ)+1)) = ((m).factorial : ℝ) := by
          intro m
          induction m with
          | zero => simp
          | succ k ih =>
            rw [Finset.prod_range_succ, ih, Nat.factorial_succ]
            push_cast
            ring
        exact hgen (n-1)
      have hsplit : (∏ k ∈ Finset.range (n - 1), (a + ((k:ℝ)+1)))
          = ((n-1).factorial : ℝ) * ∏ k ∈ Finset.range (n-1), (1 + a/((k:ℝ)+1)) := by
        rw [← hfac, ← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro k hk
        have hk1 : (0:ℝ) < (k:ℝ)+1 := by positivity
        field_simp
        ring
      have hpeel : (∏ k ∈ Finset.range (n-1), (1 + a/((k:ℝ)+1)))
          = (∏ k ∈ Finset.range (n-2), (1 + a/((k:ℝ)+2))) * (1 + a) := by
        conv_lhs => rw [show n - 1 = (n - 2) + 1 by omega]
        rw [Finset.prod_range_succ']
        have hbody : ∀ k ∈ Finset.range (n-2), (1 + a/(((k+1:ℕ):ℝ) + 1)) = (1 + a/((k:ℝ)+2)) := by
          intro k hk
          have hc : (((k+1:ℕ)):ℝ) + 1 = (k:ℝ) + 2 := by
            push_cast
            ring
          rw [hc]
        rw [Finset.prod_congr rfl hbody]
        simp
      have hlogterm : ∀ k ∈ Finset.range (n-2), Real.log (1 + a/((k:ℝ)+2)) ≤ a/((k:ℝ)+2) := by
        intro k hk
        exact hlog_upper _ (by positivity)
      have hsum_bound : (∑ k ∈ Finset.range (n-2), Real.log (1 + a/((k:ℝ)+2))) ≤
          a * Real.log (n:ℝ) := by
        have hs1 : (∑ k ∈ Finset.range (n-2), Real.log (1 + a/((k:ℝ)+2)))
            ≤ ∑ k ∈ Finset.range (n-2), a/((k:ℝ)+2) := Finset.sum_le_sum hlogterm
        have hs2 : (∑ k ∈ Finset.range (n-2), a/((k:ℝ)+2))
            = a * ∑ k ∈ Finset.range (n-2), (1/((k:ℝ)+2)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          ring
        have hs3 : (∑ k ∈ Finset.range (n-2), (1/((k:ℝ)+2))) ≤ Real.log (((n-2:ℕ):ℝ) + 1) :=
          hShiftUpper (n-2)
        have hs4 : ((n - 2 : ℕ) : ℝ) + 1 ≤ (n:ℝ) := by
          have h5 : n - 2 + 1 ≤ n := by omega
          exact_mod_cast h5
        have hs5 : Real.log (((n-2:ℕ):ℝ) + 1) ≤ Real.log (n:ℝ) :=
          Real.log_le_log (by positivity) hs4
        have hs6 : a * (∑ k ∈ Finset.range (n-2), (1/((k:ℝ)+2))) ≤ a * Real.log (n:ℝ) :=
          mul_le_mul_of_nonneg_left (le_trans hs3 hs5) hapos.le
        linarith [hs1, hs2, hs6]
      have hexp_prod : (∏ k ∈ Finset.range (n-2), (1 + a/((k:ℝ)+2)))
          = Real.exp (∑ k ∈ Finset.range (n-2), Real.log (1 + a/((k:ℝ)+2))) := by
        rw [Real.exp_sum]
        apply Finset.prod_congr rfl
        intro k hk
        exact (Real.exp_log (show (0:ℝ) < 1 + a/((k:ℝ)+2) by positivity)).symm
      have hmain : (∏ k ∈ Finset.range (n-2), (1 + a/((k:ℝ)+2))) * (1 + a) ≤
          Real.exp 1 * (n:ℝ)^a := by
        rw [hexp_prod]
        have hexp_le : Real.exp (∑ k ∈ Finset.range (n-2), Real.log (1 + a/((k:ℝ)+2))) ≤
            (n:ℝ)^a := by
          rw [Real.rpow_def_of_pos hnpos]
          exact Real.exp_le_exp.mpr (by simpa [mul_comm] using hsum_bound)
        have h2 : (1 + a) ≤ Real.exp 1 := by
          have h3 := Real.add_one_le_exp 1
          linarith
        have hm : Real.exp (∑ k ∈ Finset.range (n-2), Real.log (1 + a/((k:ℝ)+2))) * (1 + a) ≤
            (n:ℝ)^a * Real.exp 1 :=
          mul_le_mul hexp_le h2 (by positivity) (Real.rpow_nonneg hnpos.le a)
        simpa [mul_comm] using hm
      rw [hrf, hsplit, hpeel]
      have hmul := mul_le_mul_of_nonneg_left hmain (by positivity : (0:ℝ) ≤ a * ((n - 1).factorial : ℝ))
      have hstep2 : a * (((n-1).factorial : ℝ) * (Real.exp 1 * (n:ℝ)^a)) ≤
          ((n-1).factorial : ℝ) * (Real.exp 1 * (n:ℝ)^a) := by
        have hX : (0:ℝ) ≤ ((n-1).factorial : ℝ) * (Real.exp 1 * (n:ℝ)^a) := by positivity
        have h := mul_le_mul_of_nonneg_right ha1 hX
        simpa using h
      linarith [hmul, hstep2]
  have hP2 : ∀ n : ℕ, 1 ≤ n →
      eps * (n : ℝ) ^ eps * ((n - 1).factorial : ℝ) ≤ Real.exp 1 * risingFac eps n := by
    intro n hn
    have hrf : risingFac eps n = eps * ∏ k ∈ Finset.range (n - 1), (eps + ((k:ℝ)+1)) := by
      unfold risingFac
      conv_lhs => rw [show n = (n - 1) + 1 by omega]
      rw [Finset.prod_range_succ']
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero]
      ring
    have hfac : (∏ k ∈ Finset.range (n-1), ((k:ℝ)+1)) = ((n-1).factorial : ℝ) := by
      have hgen : ∀ m : ℕ, (∏ k ∈ Finset.range m, ((k:ℝ)+1)) = ((m).factorial : ℝ) := by
        intro m
        induction m with
        | zero => simp
        | succ k ih =>
          rw [Finset.prod_range_succ, ih, Nat.factorial_succ]
          push_cast
          ring
      exact hgen (n-1)
    have hsplit : (∏ k ∈ Finset.range (n - 1), (eps + ((k:ℝ)+1)))
        = ((n-1).factorial : ℝ) * ∏ k ∈ Finset.range (n-1), (1 + eps/((k:ℝ)+1)) := by
      rw [← hfac, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro k hk
      have hk1 : (0:ℝ) < (k:ℝ)+1 := by positivity
      field_simp
      ring
    have hlogterm : ∀ k ∈ Finset.range (n-1),
        eps/((k:ℝ)+2) ≤ Real.log (1 + eps/((k:ℝ)+1)) := by
      intro k hk
      have hA : (0:ℝ) < (k:ℝ)+2 := by positivity
      have hB : (0:ℝ) < (k:ℝ)+1+eps := by linarith
      have h1 : eps/((k:ℝ)+1) / (1 + eps/((k:ℝ)+1)) ≤ Real.log (1 + eps/((k:ℝ)+1)) :=
        hlog_lower _ (by positivity)
      have he : eps/((k:ℝ)+1) / (1 + eps/((k:ℝ)+1)) = eps/((k:ℝ)+1+eps) := by
        field_simp
      rw [he] at h1
      have h2 : eps/((k:ℝ)+2) ≤ eps/((k:ℝ)+1+eps) := by
        have hrw : eps/((k:ℝ)+1+eps) * ((k:ℝ)+2) = eps * ((k:ℝ)+2)/((k:ℝ)+1+eps) := by
          field_simp
        rw [div_le_iff₀ hA, hrw, le_div_iff₀ hB]
        apply mul_le_mul_of_nonneg_left _ h_eps.le
        linarith
      linarith
    have htel3 : ∀ m : ℕ,
        ∑ k ∈ Finset.range m, (Real.log ((k:ℝ)+3) - Real.log ((k:ℝ)+2)) =
          Real.log ((m:ℝ)+2) - Real.log 2 := by
      intro m
      induction m with
      | zero => simp
      | succ k ih =>
        rw [Finset.sum_range_succ, ih]
        push_cast
        rw [show (k:ℝ) + 1 + 2 = (k:ℝ) + 3 by ring]
        ring
    have hlogn' : Real.log (n:ℝ) - 1 ≤ ∑ k ∈ Finset.range (n-1), (1/((k:ℝ)+2)) := by
      have hterm : ∑ k ∈ Finset.range (n-1), (Real.log ((k:ℝ)+3) - Real.log ((k:ℝ)+2)) ≤
          ∑ k ∈ Finset.range (n-1), (1/((k:ℝ)+2)) := by
        apply Finset.sum_le_sum
        intro k hk
        rw [← Real.log_div (by positivity) (by positivity)]
        have hsp : ((k:ℝ)+3)/((k:ℝ)+2) = 1 + 1/((k:ℝ)+2) := by
          field_simp
          ring
        rw [hsp]
        exact hlog_upper _ (by positivity)
      have hcast2 : ((n - 1 : ℕ) : ℝ) + 2 = (n:ℝ) + 1 := by
        rw [Nat.cast_sub hn]
        ring
      rw [htel3 (n-1), hcast2] at hterm
      have h2 : Real.log 2 ≤ 1 := by
        have h3 := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
        linarith
      have h4 : Real.log (n:ℝ) ≤ Real.log ((n:ℝ)+1) :=
        Real.log_le_log (by positivity) (by linarith)
      linarith
    have hsum_lb : eps * (Real.log (n:ℝ) - 1) ≤
        ∑ k ∈ Finset.range (n-1), Real.log (1 + eps/((k:ℝ)+1)) := by
      have hs1 : ∑ k ∈ Finset.range (n-1), eps/((k:ℝ)+2) ≤
          ∑ k ∈ Finset.range (n-1), Real.log (1 + eps/((k:ℝ)+1)) :=
        Finset.sum_le_sum hlogterm
      have hs2 : eps * (Real.log (n:ℝ) - 1) ≤ ∑ k ∈ Finset.range (n-1), eps/((k:ℝ)+2) := by
        calc eps * (Real.log (n:ℝ) - 1) ≤ eps * ∑ k ∈ Finset.range (n-1), (1/((k:ℝ)+2)) :=
              mul_le_mul_of_nonneg_left hlogn' h_eps.le
          _ = ∑ k ∈ Finset.range (n-1), eps * (1/((k:ℝ)+2)) := by rw [Finset.mul_sum]
          _ = ∑ k ∈ Finset.range (n-1), eps/((k:ℝ)+2) := by
              apply Finset.sum_congr rfl
              intro k hk
              ring
      linarith [hs1, hs2]
    have hhexp : ∏ k ∈ Finset.range (n-1), (1 + eps/((k:ℝ)+1))
        = Real.exp (∑ k ∈ Finset.range (n-1), Real.log (1 + eps/((k:ℝ)+1))) := by
      rw [Real.exp_sum]
      apply Finset.prod_congr rfl
      intro k hk
      exact (Real.exp_log (show (0:ℝ) < 1 + eps/((k:ℝ)+1) by positivity)).symm
    have hmain : (n:ℝ)^eps ≤
        Real.exp 1 * ∏ k ∈ Finset.range (n-1), (1 + eps/((k:ℝ)+1)) := by
      rw [Real.rpow_def_of_pos (by positivity : (0:ℝ) < (n:ℝ))]
      have hle : Real.log (n:ℝ) * eps ≤
          1 + ∑ k ∈ Finset.range (n-1), Real.log (1 + eps/((k:ℝ)+1)) := by
        have h1 := hsum_lb
        have h2 : eps ≤ 1 := by linarith
        nlinarith [h1, h2]
      calc Real.exp (Real.log (n:ℝ) * eps)
          ≤ Real.exp (1 + ∑ k ∈ Finset.range (n-1), Real.log (1 + eps/((k:ℝ)+1))) :=
            Real.exp_le_exp.mpr hle
        _ = Real.exp 1 * Real.exp (∑ k ∈ Finset.range (n-1), Real.log (1 + eps/((k:ℝ)+1))) :=
            Real.exp_add 1 _
        _ = Real.exp 1 * ∏ k ∈ Finset.range (n-1), (1 + eps/((k:ℝ)+1)) := by
            rw [← hhexp]
    rw [hrf, hsplit]
    have h1 : ((n-1).factorial : ℝ) * eps * (n:ℝ)^eps ≤
        ((n-1).factorial : ℝ) * eps *
          (Real.exp 1 * ∏ k ∈ Finset.range (n-1), (1 + eps/((k:ℝ)+1))) :=
      mul_le_mul_of_nonneg_left hmain (by positivity)
    nlinarith [h1]
  have hprod_nonneg : ∀ (N : ℕ) (f : ℕ → ℝ), (∀ j, 0 ≤ f j) →
      (0:ℝ) ≤ ∏ j ∈ Finset.range N, f j := by
    intro N f hf
    induction N with
    | zero => simp
    | succ k ih =>
      rw [Finset.prod_range_succ]
      exact mul_nonneg ih (hf k)
  have hprod_le : ∀ (N : ℕ) (f g : ℕ → ℝ), (∀ j, 0 ≤ f j) → (∀ j, 0 ≤ g j) →
      (∀ j ∈ Finset.range N, f j ≤ g j) →
      ∏ j ∈ Finset.range N, f j ≤ ∏ j ∈ Finset.range N, g j := by
    intro N
    induction N with
    | zero => intro f g _ _ _; simp
    | succ k ih =>
      intro f g hf0 hg0 hfg
      rw [Finset.prod_range_succ, Finset.prod_range_succ]
      exact mul_le_mul
        (ih f g hf0 hg0 (fun j hj => hfg j (Finset.mem_range.mpr (lt_trans (Finset.mem_range.mp hj) (Nat.lt_succ_self k)))))
        (hfg k (Finset.mem_range.mpr (Nat.lt_succ_self k)))
        (hf0 k) (hprod_nonneg k g hg0)
  have hfac2 : ∀ mm : ℕ, (∏ j ∈ Finset.range mm, ((j:ℝ)+2)) = ((mm+1).factorial : ℝ) := by
    intro mm
    induction mm with
    | zero => norm_num
    | succ k ih =>
      rw [Finset.prod_range_succ, ih]
      have h1 : ((k+1+1).factorial : ℝ) = ((k+1+1 : ℕ) : ℝ) * ((k+1).factorial : ℝ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      have hfac : ((k+1+1).factorial : ℝ) = ((k:ℝ)+2) * ((k+1).factorial : ℝ) := by
        rw [h1]
        push_cast
        ring
      rw [hfac]
      ring

  have htail : ∀ n : ℕ, (n : ℝ) ≥ t + 1 →
      (∫ a in Set.Ioi eps, a ^ t / risingFac a n * pi a) ≤
        Real.exp 1 * ((m + 1).factorial : ℝ) /
          (eps * (n : ℝ) ^ eps * ((n - 1).factorial : ℝ)) := by
    intro n hn
    exact (statopia_math_node_4213379669_bb9a52d2 t ht eps h_eps h_eps_lt delta beta h_delta
      h_beta pi hpi_meas hpi_nonneg hpi_prob hA2 m htm hmn K hK n hn).1
  have hsmall : ∀ n : ℕ, (n : ℝ) ≥ t + 1 →
      (delta * 2 ^ K * Real.exp 3)⁻¹ * (min eps (1 / Real.log (n : ℝ))) ^ K /
          ((n - 1).factorial : ℝ) ≤
        (∫ a in Set.Ioo (0 : ℝ) eps, a ^ t / risingFac a n * pi a) := by
    intro n hn
    exact (statopia_math_node_4213379669_bb9a52d2 t ht eps h_eps h_eps_lt delta beta h_delta
      h_beta pi hpi_meas hpi_nonneg hpi_prob hA2 m htm hmn K hK n hn).2
  have hstep : ∀ n : ℕ, (n : ℝ) ≥ t + 1 →
      Real.exp 1 * ((m + 1).factorial : ℝ) / (eps * (n : ℝ) ^ eps * ((n - 1).factorial : ℝ)) ≤
        ((m + 1).factorial : ℝ) * Real.exp 4 * 2 ^ K * delta / eps ^ (K + 1) *
          (n : ℝ) ^ (-eps) * (1 + Real.log (n : ℝ)) ^ K *
          ((delta * 2 ^ K * Real.exp 3)⁻¹ * (min eps (1 / Real.log (n : ℝ))) ^ K /
            ((n - 1).factorial : ℝ)) := by
    intro n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hLpos : (0 : ℝ) < Real.log (n : ℝ) := Real.log_pos (by linarith)
    have h1L : (0 : ℝ) < 1 + Real.log (n : ℝ) := by linarith
    have hvpos : (0 : ℝ) < min eps (1 / Real.log (n : ℝ)) := lt_min h_eps (by positivity)
    have hDpos : (0 : ℝ) < ((m + 1).factorial : ℝ) := by positivity
    have hEpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    have hvK : eps ^ K ≤ (1 + Real.log (n : ℝ)) ^ K * (min eps (1 / Real.log (n : ℝ))) ^ K := by
      have hAB : eps ^ K ≤
          (min eps (1 / Real.log (n : ℝ))) ^ K * (1 + Real.log (n : ℝ)) ^ K := by
        have hle : eps ≤ min eps (1 / Real.log (n : ℝ)) * (1 + Real.log (n : ℝ)) := by
          have hmin : eps / (1 + Real.log (n : ℝ)) ≤ min eps (1 / Real.log (n : ℝ)) := by
            refine le_min ?_ ?_
            · rw [div_le_iff₀ h1L]
              nlinarith [mul_nonneg h_eps.le hLpos.le]
            · rw [div_le_iff₀ h1L]
              have hrew : 1 / Real.log (n : ℝ) * (1 + Real.log (n : ℝ)) =
                  (1 + Real.log (n : ℝ)) / Real.log (n : ℝ) := by
                field_simp
              rw [hrew, le_div_iff₀ hLpos]
              have hEL : eps * Real.log (n : ℝ) ≤ Real.log (n : ℝ) := by
                have hle1 : eps ≤ 1 := by linarith
                calc eps * Real.log (n : ℝ) ≤ 1 * Real.log (n : ℝ) :=
                      mul_le_mul_of_nonneg_right hle1 hLpos.le
                  _ = Real.log (n : ℝ) := one_mul _
              linarith [hEL]
          calc eps = eps / (1 + Real.log (n : ℝ)) * (1 + Real.log (n : ℝ)) := by
                field_simp
            _ ≤ min eps (1 / Real.log (n : ℝ)) * (1 + Real.log (n : ℝ)) :=
                mul_le_mul_of_nonneg_right hmin h1L.le
        calc eps ^ K ≤ (min eps (1 / Real.log (n : ℝ)) * (1 + Real.log (n : ℝ))) ^ K :=
              Real.rpow_le_rpow h_eps.le hle hK0
          _ = (min eps (1 / Real.log (n : ℝ))) ^ K * (1 + Real.log (n : ℝ)) ^ K :=
              Real.mul_rpow hvpos.le h1L.le
      rw [mul_comm ((min eps (1 / Real.log (n : ℝ))) ^ K)] at hAB
      exact hAB
    have hcore : Real.exp 1 * ((m + 1).factorial : ℝ) / eps ≤
        (Real.exp 1 * ((m + 1).factorial : ℝ) / eps ^ (K + 1)) *
          ((1 + Real.log (n : ℝ)) ^ K * (min eps (1 / Real.log (n : ℝ))) ^ K) := by
      rw [Real.rpow_add_one h_eps.ne']
      have hAB : eps ^ K * eps ≤
          ((1 + Real.log (n : ℝ)) ^ K * (min eps (1 / Real.log (n : ℝ))) ^ K) * eps :=
        mul_le_mul_of_nonneg_right hvK h_eps.le
      have h2 := mul_le_mul_of_nonneg_left hAB (by positivity : (0 : ℝ) ≤ Real.exp 1 * ((m + 1).factorial : ℝ))
      field_simp
      nlinarith [h2]
    have hLHS : Real.exp 1 * ((m + 1).factorial : ℝ) /
          (eps * (n : ℝ) ^ eps * ((n - 1).factorial : ℝ))
        = (Real.exp 1 * ((m + 1).factorial : ℝ) / eps) * ((n : ℝ) ^ (-eps)) /
            ((n - 1).factorial : ℝ) := by
      rw [Real.rpow_neg (le_of_lt hnpos)]
      field_simp
    rw [hLHS, mul_div_assoc]
    have hfac : (0 : ℝ) ≤ (n : ℝ) ^ (-eps) / ((n - 1).factorial : ℝ) := by positivity
    calc (Real.exp 1 * ((m + 1).factorial : ℝ) / eps) *
          ((n : ℝ) ^ (-eps) / ((n - 1).factorial : ℝ))
        ≤ ((Real.exp 1 * ((m + 1).factorial : ℝ) / eps ^ (K + 1)) *
            ((1 + Real.log (n : ℝ)) ^ K * (min eps (1 / Real.log (n : ℝ))) ^ K)) *
            ((n : ℝ) ^ (-eps) / ((n - 1).factorial : ℝ)) :=
          mul_le_mul_of_nonneg_right hcore hfac
      _ = ((m + 1).factorial : ℝ) * Real.exp 4 * 2 ^ K * delta / eps ^ (K + 1) *
            (n : ℝ) ^ (-eps) * (1 + Real.log (n : ℝ)) ^ K *
            ((delta * 2 ^ K * Real.exp 3)⁻¹ * (min eps (1 / Real.log (n : ℝ))) ^ K /
              ((n - 1).factorial : ℝ)) := by
          field_simp
          rw [← Real.exp_add]
          norm_num
  refine ⟨((m + 1).factorial : ℝ) * Real.exp 4 * 2 ^ K * delta / eps ^ (K + 1), ?_, K, hK0, ?_⟩
  · have h1 : (0 : ℝ) < ((m + 1).factorial : ℝ) := by positivity
    have h4 : (0 : ℝ) < eps ^ (K + 1) := Real.rpow_pos_of_pos h_eps (K + 1)
    have h5 : (0 : ℝ) < (2 : ℝ) ^ K := Real.rpow_pos_of_pos (by norm_num) K
    have h6 : (0 : ℝ) < Real.exp 4 := Real.exp_pos 4
    positivity
  · intro n hn
    obtain ⟨-, -, hBint, hBpos, -, -, hTint, hTnonneg, -⟩ :=
      hdep n 1 le_rfl (by push_cast; linarith)
    refine ⟨hBint, hBpos, hTint, ?_⟩
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hCf : (0 : ℝ) ≤ ((m + 1).factorial : ℝ) * Real.exp 4 * 2 ^ K * delta / eps ^ (K + 1) *
        (n : ℝ) ^ (-eps) * (1 + Real.log (n : ℝ)) ^ K := by
      have h1 : (0 : ℝ) < ((m + 1).factorial : ℝ) := by positivity
      have h2 : (0 : ℝ) < Real.exp 4 := Real.exp_pos 4
      have h3 : (0 : ℝ) < (2 : ℝ) ^ K := Real.rpow_pos_of_pos (by norm_num) K
      have h4 : (0 : ℝ) < eps ^ (K + 1) := Real.rpow_pos_of_pos h_eps (K + 1)
      have h5 : (0 : ℝ) < (n : ℝ) ^ (-eps) := Real.rpow_pos_of_pos hnpos (-eps)
      have h6 : (0 : ℝ) < (1 + Real.log (n : ℝ)) ^ K := Real.rpow_pos_of_pos (by positivity) K
      positivity
    have hmul := mul_le_mul_of_nonneg_left (hsmall n hn) hCf
    linarith [htail n hn, hstep n hn]
  /- @proof-region region.target-node.session.16f84b4399f51e47 end -/

end Statlib.Imported
end
