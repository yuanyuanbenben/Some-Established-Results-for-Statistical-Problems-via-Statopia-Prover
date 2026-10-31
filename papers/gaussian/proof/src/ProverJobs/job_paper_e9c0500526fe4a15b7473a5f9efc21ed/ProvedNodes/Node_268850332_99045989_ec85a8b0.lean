import ProverJobs.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Vocabulary
import ProverJobs.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Base

namespace PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed

open _root_.PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
universe u₀ u₁

set_option autoImplicit false in
theorem statopia_math_node_268850332_99045989 : ∀ (a : ℝ) (ha_pos : 0 < a) (ha_lt : a < 1 / 2)
    (p : ℕ → ℕ) (hp : ∀ n : ℕ, 1 ≤ p n),
    (∀ eta : ℝ, 0 < eta → ∃ n1 : ℕ, 1 ≤ n1 ∧
      ∀ n : ℕ, n1 ≤ n → (kIdx p a n : ℝ) ≤ (n : ℝ) ^ eta) ∧
    (∀ delta : ℝ, 0 < delta → ∃ n1 : ℕ, 1 ≤ n1 ∧
      ∀ n : ℕ, n1 ≤ n → (kIdx p a n : ℝ) ^ (7 / 4 : ℝ) ≤ (n : ℝ) ^ delta) := by
  /- @proof-region region.target-node.session.cbd61bc8c361f8f4 begin -/
  intro a ha_pos ha_lt p hp
  have key : ∀ η : ℝ, 0 < η → ∃ n1 : ℕ, 1 ≤ n1 ∧ ∀ n : ℕ, n1 ≤ n → (kIdx p a n : ℝ) ≤ (n : ℝ) ^ η := by
    intro η hη
    have hlog_large : ∀ K : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → K ≤ Real.log (n : ℝ) := by
      intro K
      by_cases hK : K ≤ 0
      · refine ⟨1, fun n hn => le_trans hK ?_⟩
        exact Real.log_nonneg (by exact_mod_cast hn)
      · push_neg at hK
        refine ⟨Nat.ceil (Real.exp K) + 1, fun n hn => ?_⟩
        have h3 : Nat.ceil (Real.exp K) ≤ n := le_trans (Nat.le_succ _) hn
        have h4 : Real.exp K ≤ (Nat.ceil (Real.exp K) : ℝ) := Nat.le_ceil _
        have h5 : (Nat.ceil (Real.exp K) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h3
        have h6 : Real.exp K ≤ (n : ℝ) := le_trans h4 h5
        calc K = Real.log (Real.exp K) := (Real.log_exp K).symm
          _ ≤ Real.log (n : ℝ) := Real.log_le_log (Real.exp_pos K) h6
    set c : ℝ := (η / 6) ^ 6 with hc_def
    have hcpos : 0 < c := by
      rw [hc_def]
      have h6 : (0 : ℝ) < η / 6 := by linarith
      positivity
    obtain ⟨N1, hN1⟩ := hlog_large 1
    obtain ⟨N2, hN2⟩ := hlog_large (12 / c)
    obtain ⟨N3, hN3⟩ := hlog_large ((2 / η) ^ (1 / a) + 1)
    obtain ⟨N4, hN4⟩ := hlog_large (2 * Real.log 2 / η)
    refine ⟨N1 + N2 + N3 + N4 + 2, by omega, ?_⟩
    intro n hn
    have hN1' : N1 ≤ n := by omega
    have hN2' : N2 ≤ n := by omega
    have hN3' : N3 ≤ n := by omega
    have hN4' : N4 ≤ n := by omega
    have hn2 : 2 ≤ n := by omega
    have hL1 : (1 : ℝ) ≤ Real.log (n : ℝ) := hN1 n hN1'
    have hLc : 12 / c ≤ Real.log (n : ℝ) := hN2 n hN2'
    have hLe : (2 / η) ^ (1 / a) + 1 ≤ Real.log (n : ℝ) := hN3 n hN3'
    have hLlog : 2 * Real.log 2 / η ≤ Real.log (n : ℝ) := hN4 n hN4'
    have ceil_bound : (kIdx p a n : ℝ) ≤
        (Real.log (n : ℝ)) ^ 3 + (n : ℝ) ^ (1 / (Real.log (n : ℝ)) ^ a) + 3 := by
      have hnpos : (0 : ℝ) < (n : ℝ) := by
        have h1n : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_trans (by norm_num) hn2)
        linarith
      have hX0 : (0 : ℝ) ≤ (n : ℝ) ^ (1 / (Real.log (n : ℝ)) ^ a) :=
        Real.rpow_nonneg (le_of_lt hnpos) _
      have step1 : (kIdx p a n : ℝ) ≤
          (Nat.ceil (max (ellIdx p n : ℝ) ((n : ℝ) ^ (1 / (Real.log (n : ℝ)) ^ a))) : ℝ) := by
        have h : kIdx p a n ≤
            Nat.ceil (max (ellIdx p n : ℝ) ((n : ℝ) ^ (1 / (Real.log (n : ℝ)) ^ a))) :=
          Nat.ceil_le_ceil (min_le_left _ _)
        exact_mod_cast h
      have hmax0 : (0 : ℝ) ≤ max (ellIdx p n : ℝ) ((n : ℝ) ^ (1 / (Real.log (n : ℝ)) ^ a)) :=
        le_trans (Nat.cast_nonneg _) (le_max_left _ _)
      have step2 : (Nat.ceil (max (ellIdx p n : ℝ) ((n : ℝ) ^ (1 / (Real.log (n : ℝ)) ^ a))) : ℝ) ≤
          max (ellIdx p n : ℝ) ((n : ℝ) ^ (1 / (Real.log (n : ℝ)) ^ a)) + 1 :=
        le_of_lt (Nat.ceil_lt_add_one hmax0)
      have hell : (ellIdx p n : ℝ) ≤ (Real.log (n : ℝ)) ^ 3 + 2 := by
        have hmin : min (max 1 ((Real.log (n : ℝ)) ^ 3)) ((p n : ℝ)) ≤
            max 1 ((Real.log (n : ℝ)) ^ 3) := min_le_left _ _
        have hc : (ellIdx p n : ℝ) ≤ (Nat.ceil (max 1 ((Real.log (n : ℝ)) ^ 3)) : ℝ) := by
          have h2 : ellIdx p n ≤ Nat.ceil (max 1 ((Real.log (n : ℝ)) ^ 3)) := Nat.ceil_le_ceil hmin
          exact_mod_cast h2
        have hpos : (0 : ℝ) ≤ max 1 ((Real.log (n : ℝ)) ^ 3) :=
          le_trans zero_le_one (le_max_left _ _)
        have hlt : (Nat.ceil (max 1 ((Real.log (n : ℝ)) ^ 3)) : ℝ) ≤
            max 1 ((Real.log (n : ℝ)) ^ 3) + 1 := le_of_lt (Nat.ceil_lt_add_one hpos)
        have hmax2 : max 1 ((Real.log (n : ℝ)) ^ 3) ≤ (Real.log (n : ℝ)) ^ 3 + 1 := by
          have h0 : (0 : ℝ) ≤ (Real.log (n : ℝ)) ^ 3 := pow_nonneg (by linarith) 3
          exact max_le (by linarith) (by linarith)
        linarith
      have hmaxle : max (ellIdx p n : ℝ) ((n : ℝ) ^ (1 / (Real.log (n : ℝ)) ^ a)) ≤
          (ellIdx p n : ℝ) + (n : ℝ) ^ (1 / (Real.log (n : ℝ)) ^ a) :=
        max_le (le_add_of_nonneg_right hX0) (le_add_of_nonneg_left (Nat.cast_nonneg _))
      linarith
    have hA : (Real.log (n : ℝ)) ^ 3 + 3 ≤ (n : ℝ) ^ η / 2 := by
      set L := Real.log (n : ℝ) with hLdef
      have hnpos : (0 : ℝ) < (n : ℝ) := by
        have h1n : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_trans (by norm_num) hn2)
        linarith
      have hL0 : (0 : ℝ) ≤ L := by linarith
      have hL3geL : L ≤ L ^ 3 := by
        have h2 : (1 : ℝ) ≤ L ^ 2 := by nlinarith [hL1]
        calc L = L * 1 := (mul_one L).symm
          _ ≤ L * L ^ 2 := mul_le_mul_of_nonneg_left h2 hL0
          _ = L ^ 3 := by ring
      have hL6geL : L ≤ L ^ 6 := by
        have h2 : (1 : ℝ) ≤ L ^ 3 := le_trans hL1 hL3geL
        have hL3le6 : L ^ 3 ≤ L ^ 6 := by
          calc L ^ 3 = L ^ 3 * 1 := (mul_one _).symm
            _ ≤ L ^ 3 * L ^ 3 := mul_le_mul_of_nonneg_left h2 (pow_nonneg hL0 3)
            _ = L ^ 6 := by ring
        linarith
      have hc4nn : (0 : ℝ) ≤ c / 4 := by linarith
      have hc4 : (3 : ℝ) ≤ (c / 4) * L := by
        have hcross : (c / 4) * (12 / c) = 3 := by field_simp; ring
        calc (3 : ℝ) = (c / 4) * (12 / c) := hcross.symm
          _ ≤ (c / 4) * L := mul_le_mul_of_nonneg_left hLc hc4nn
      have h1 : (1 : ℝ) ≤ (c / 4) * L ^ 3 :=
        le_trans (by norm_num) (le_trans hc4 (mul_le_mul_of_nonneg_left hL3geL hc4nn))
      have h2 : (3 : ℝ) ≤ (c / 4) * L ^ 6 :=
        le_trans hc4 (mul_le_mul_of_nonneg_left hL6geL hc4nn)
      have hstep : L ^ 3 ≤ (c / 4) * L ^ 6 := by
        have hm := mul_le_mul_of_nonneg_right h1 (pow_nonneg hL0 3)
        calc L ^ 3 = 1 * L ^ 3 := (one_mul _).symm
          _ ≤ ((c / 4) * L ^ 3) * L ^ 3 := hm
          _ = (c / 4) * L ^ 6 := by ring
      have hfinal : 2 * L ^ 3 + 6 ≤ c * L ^ 6 := by
        have hD : c * L ^ 6 = 4 * ((c / 4) * L ^ 6) := by ring
        rw [hD]
        linarith
      have hrpow : (n : ℝ) ^ (η / 6) = Real.exp ((η / 6) * L) := by
        rw [Real.rpow_def_of_pos hnpos, ← hLdef]
        congr 1
        ring
      have hexp : (η / 6) * L + 1 ≤ (n : ℝ) ^ (η / 6) := by
        rw [hrpow]
        exact Real.add_one_le_exp ((η / 6) * L)
      have hbase0 : (0 : ℝ) ≤ (η / 6) * L := by
        have hη6 : (0 : ℝ) < η / 6 := by linarith
        nlinarith
      have hle : (η / 6) * L ≤ (n : ℝ) ^ (η / 6) := by linarith
      have h6 : ((η / 6) * L) ^ 6 ≤ ((n : ℝ) ^ (η / 6)) ^ 6 := by
        gcongr
      have hcL : ((η / 6) * L) ^ 6 = c * L ^ 6 := by
        rw [hc_def]; ring
      have hfin : c * L ^ 6 ≤ ((n : ℝ) ^ (η / 6)) ^ 6 := by
        rw [← hcL]
        exact h6
      have hpow : (n : ℝ) ^ η = ((n : ℝ) ^ (η / 6)) ^ 6 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hnpos)]
        congr 1
        ring
      rw [hpow]
      linarith
    have hB : (n : ℝ) ^ (1 / (Real.log (n : ℝ)) ^ a) ≤ (n : ℝ) ^ η / 2 := by
      set L := Real.log (n : ℝ) with hLdef
      have hnpos : (0 : ℝ) < (n : ℝ) := by
        have h1n : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_trans (by norm_num) hn2)
        linarith
      have hLpos : 0 < L := by linarith
      have hLapos : (0 : ℝ) < L ^ a := Real.rpow_pos_of_pos hLpos a
      have hLa : 2 / η ≤ L ^ a := by
        have h1 : (2 / η) ^ (1 / a) ≤ L := by linarith
        have h2 : ((2 / η) ^ (1 / a)) ^ a ≤ L ^ a :=
          Real.rpow_le_rpow (by positivity) h1 (le_of_lt ha_pos)
        have h3 : ((2 / η) ^ (1 / a)) ^ a = 2 / η := by
          rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 2 / η)]
          rw [show (1 / a) * a = 1 by field_simp]
          simp
        linarith
      have hinv : 1 / L ^ a ≤ η / 2 := by
        rw [div_le_iff₀ hLapos]
        have h2le : (2 : ℝ) ≤ η * L ^ a := by
          have hm := mul_le_mul_of_nonneg_left hLa (le_of_lt hη)
          have hsimp : η * (2 / η) = 2 := by field_simp
          linarith
        nlinarith [h2le]
      have hlog2 : Real.log 2 ≤ (η / 2) * L := by
        have hm := mul_le_mul_of_nonneg_left hLlog (by linarith : (0 : ℝ) ≤ η / 2)
        have hsimp : (η / 2) * (2 * Real.log 2 / η) = Real.log 2 := by field_simp
        linarith
      have hexp_le : (1 / L ^ a) * L ≤ η * L - Real.log 2 := by
        have h1 : (1 / L ^ a) * L ≤ (η / 2) * L :=
          mul_le_mul_of_nonneg_right hinv (le_of_lt hLpos)
        linarith
      have hXdef : (n : ℝ) ^ (1 / L ^ a) = Real.exp ((1 / L ^ a) * L) := by
        rw [Real.rpow_def_of_pos hnpos, ← hLdef]
        congr 1
        ring
      have e2 : (n : ℝ) ^ η = Real.exp (η * L) := by
        rw [Real.rpow_def_of_pos hnpos, ← hLdef]
        congr 1
        ring
      rw [hXdef]
      refine le_trans (Real.exp_le_exp.mpr hexp_le) ?_
      rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2), ← e2]
    linarith
  constructor
  · exact key
  · intro δ hδ
    have hη : (0 : ℝ) < 4 * δ / 7 := by linarith
    obtain ⟨n1, hn1, hbound⟩ := key (4 * δ / 7) hη
    refine ⟨n1, hn1, fun n hn => ?_⟩
    have hbase := hbound n hn
    have hk0 : (0 : ℝ) ≤ (kIdx p a n : ℝ) := Nat.cast_nonneg _
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    have h1 : (kIdx p a n : ℝ) ^ (7 / 4 : ℝ) ≤ ((n : ℝ) ^ (4 * δ / 7)) ^ (7 / 4 : ℝ) :=
      Real.rpow_le_rpow hk0 hbase (by norm_num)
    have h2 : ((n : ℝ) ^ (4 * δ / 7)) ^ (7 / 4 : ℝ) = (n : ℝ) ^ δ := by
      rw [← Real.rpow_mul hn0]
      congr 1
      ring
    rwa [h2] at h1
  /- @proof-region region.target-node.session.cbd61bc8c361f8f4 end -/

end
end Statlib.Imported

