import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.Vocabulary
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.Base
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.ProvedNodes.Node_1445702134_3c8d3810_8f7a15fe

open MeasureTheory
open Statlib.Imported

noncomputable section
open MeasureTheory
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_3226374292_602af891 : ∀ (t : ℝ) (ht : 1 ≤ t)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1 / 2)
    (π : ℝ → ℝ) (hπ_meas : Measurable π)
    (hπ_nonneg : ∀ α ∈ Set.Ioi (0 : ℝ), 0 ≤ π α)
    (hπ_prob : ∫⁻ α in Set.Ioi (0 : ℝ), ENNReal.ofReal (π α) = 1)
    (m : ℕ) (htm : t ≤ (m : ℝ))
    (n : ℕ) (hn : t + 1 ≤ (n : ℝ)),
    (∫ a in Set.Ioi ε, a ^ t / risingFac a n * π a)
      ≤ Real.exp 1 * ((m + 1).factorial : ℝ) /
          (ε * (n : ℝ) ^ ε * ((n - 1).factorial : ℝ)) := by
  /- @proof-region region.target-node.session.4d996c229eba543a begin -/
  intro t ht ε hε_pos hε_lt π hπ_meas hπ_nonneg hπ_prob m htm n hn
  have h2n : (2 : ℝ) ≤ (n : ℝ) := by linarith
  have hn2 : 2 ≤ n := by exact_mod_cast h2n
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hε1 : ε ≤ 1 := by linarith
  have hε0 : (0 : ℝ) < ε := hε_pos
  have hnsub : 1 ≤ n - 1 := by omega
  set K : ℝ := Real.exp 1 * ((m + 1).factorial : ℝ) /
      (ε * (n : ℝ) ^ ε * ((n - 1).factorial : ℝ)) with hK
  have hKpos : 0 < K := by
    have h1 : (0 : ℝ) < ((m + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (m + 1)
    have h2 : (0 : ℝ) < (n : ℝ) ^ ε := Real.rpow_pos_of_pos hnpos ε
    have h3 : (0 : ℝ) < ((n - 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (n - 1)
    have h4 : (0 : ℝ) < ε * (n : ℝ) ^ ε * ((n - 1).factorial : ℝ) := by positivity
    rw [hK]
    exact div_pos (mul_pos (Real.exp_pos 1) h1) h4
  have hfac := statopia_math_node_1445702134_3c8d3810
  have amgm : ∀ (u : ℝ), 0 ≤ u → ∀ r : ℝ, 0 ≤ r → r ≤ 1 → u ^ r ≤ r * u + (1 - r) := by
    intro u hu r hr0 hr1
    rcases eq_or_lt_of_le hu with hu0 | hu_pos
    · rw [← hu0]
      rcases eq_or_lt_of_le hr0 with hr00 | hrpos
      · rw [← hr00, Real.rpow_zero]; norm_num
      · rw [Real.zero_rpow hrpos.ne']; nlinarith
    · set A : ℝ := r * u + (1 - r) with hA
      have hApos : 0 < A := by
        rw [hA]
        by_cases h : (1 : ℝ) ≤ u
        · have hh : 0 ≤ r * (u - 1) := mul_nonneg hr0 (by linarith)
          nlinarith
        · have hh : r * (1 - u) ≤ 1 * (1 - u) :=
            mul_le_mul_of_nonneg_right hr1 (by linarith)
          nlinarith
      have hAne : A ≠ 0 := hApos.ne'
      have hune : u ≠ 0 := hu_pos.ne'
      have hlog : r * Real.log u ≤ Real.log A := by
        have h1 : Real.log (u / A) ≤ u / A - 1 :=
          Real.log_le_sub_one_of_pos (div_pos hu_pos hApos)
        have h2 : Real.log (1 / A) ≤ 1 / A - 1 :=
          Real.log_le_sub_one_of_pos (div_pos one_pos hApos)
        have hm1 : r * Real.log (u / A) ≤ r * (u / A - 1) := mul_le_mul_of_nonneg_left h1 hr0
        have hm2 : (1 - r) * Real.log (1 / A) ≤ (1 - r) * (1 / A - 1) :=
          mul_le_mul_of_nonneg_left h2 (by linarith)
        have hsum : r * (u / A - 1) + (1 - r) * (1 / A - 1) = 0 := by
          have hrw : r * (u / A - 1) + (1 - r) * (1 / A - 1) = (r * u + (1 - r)) / A - 1 := by
            ring
          rw [hrw, ← hA, div_self hAne]
          ring
        have hkey : r * Real.log (u / A) + (1 - r) * Real.log (1 / A) = r * Real.log u - Real.log A := by
          rw [Real.log_div hune hAne, Real.log_div one_ne_zero hAne, Real.log_one]; ring
        linarith [hm1, hm2, hsum, hkey]
      calc u ^ r = Real.exp (Real.log u * r) := Real.rpow_def_of_pos hu_pos r
        _ ≤ Real.exp (Real.log A) := Real.exp_le_exp.mpr (by linarith)
        _ = A := Real.exp_log hApos
        _ = r * u + (1 - r) := hA
  have key : ∀ a ∈ Set.Ioi ε, a ^ t / risingFac a n * π a ≤ K * π a := by
    intro a ha
    have ha0 : 0 < a := lt_trans hε_pos ha
    have haε : ε ≤ a := le_of_lt ha
    obtain ⟨k, hk⟩ : ∃ k : ℕ, k = ⌈t⌉₊ := ⟨⌈t⌉₊, rfl⟩
    have hk1 : 1 ≤ k := by
      have h : (1 : ℝ) ≤ (k : ℝ) := by
        rw [hk]
        exact le_trans ht (Nat.le_ceil t)
      exact_mod_cast h
    have hk_ge : t ≤ (k : ℝ) := by
      rw [hk]
      exact Nat.le_ceil t
    have hk_lt : (k : ℝ) < t + 1 := by
      rw [hk]
      exact Nat.ceil_lt_add_one (le_trans zero_le_one ht)
    have hk_n : k ≤ n := by
      have h : (k : ℝ) < (n : ℝ) := by linarith
      have h2 : k < n := by exact_mod_cast h
      omega
    have hk_m : k ≤ m + 1 := by
      have h : (k : ℝ) < ((m + 1 : ℕ) : ℝ) := by
        push_cast
        linarith
      have h2 : k < m + 1 := by exact_mod_cast h
      omega
    have hkpos : (0 : ℝ) < (k : ℝ) := by
      have h : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
      linarith
    have hmain : a ^ t / risingFac a n ≤ K := by
      have hkn : k + (n - k) = n := Nat.add_sub_of_le hk_n
      have hsplit : risingFac a n
          = (∏ j ∈ Finset.range k, (a + (j:ℝ))) *
            (∏ j ∈ Finset.range (n - k), (a + ((k + j : ℕ) : ℝ))) := by
        unfold risingFac
        conv_lhs => rw [← hkn]
        rw [Finset.prod_range_add]
      set F : ℝ := ∏ j ∈ Finset.range (n - k), ((k:ℝ) + (j:ℝ)) with hFdef
      set Q : ℝ := ((n:ℝ)) ^ ε / ((k:ℝ)) ^ ε with hQdef
      have hF : 0 < F := by
        rw [hFdef]
        exact Finset.prod_pos (fun j hj => by
          have h2 : (0:ℝ) ≤ (j:ℝ) := by positivity
          linarith)
      have hQ : 0 < Q := by
        rw [hQdef]
        exact div_pos (Real.rpow_pos_of_pos hnpos ε) (Real.rpow_pos_of_pos hkpos ε)
      have hfirst : a ^ k ≤ ∏ j ∈ Finset.range k, (a + (j:ℝ)) := by
        have h1 : (∏ j ∈ Finset.range k, a) = a ^ k := by simp
        rw [← h1]
        exact Finset.prod_le_prod (fun j hj => ha0.le)
          (fun j hj => le_add_of_nonneg_right (by positivity))
      have hP : ∀ m : ℕ, (((k:ℝ) + (m:ℝ)) / (k:ℝ)) ^ ε
          ≤ ∏ j ∈ Finset.range m, (1 + a / ((k:ℝ) + (j:ℝ))) := by
        intro m
        induction m with
        | zero =>
            have hkne : ((k:ℝ)) ≠ 0 := hkpos.ne'
            have h1 : ((k:ℝ) + ((0:ℕ):ℝ)) / (k:ℝ) = 1 := by
              rw [Nat.cast_zero, add_zero, div_self hkne]
            rw [h1]
            have h2 : (1:ℝ) ^ ε ≤ 1 := by
              have h := amgm 1 zero_le_one ε hε_pos.le hε1
              linarith
            simpa using h2
        | succ m ih =>
            have hcast : ((k:ℝ) + ((Nat.succ m : ℕ) : ℝ)) = (k:ℝ) + ((m:ℝ) + 1) := by
              push_cast
              ring
            rw [hcast, Finset.prod_range_succ]
            have hD : (0:ℝ) < (k:ℝ) + (m:ℝ) := by
              have h2 : (0:ℝ) ≤ (m:ℝ) := by positivity
              linarith
            have hstep : (1 + 1 / ((k:ℝ) + (m:ℝ))) ^ ε ≤ 1 + a / ((k:ℝ) + (m:ℝ)) := by
              have hle : ε / ((k:ℝ) + (m:ℝ)) ≤ a / ((k:ℝ) + (m:ℝ)) :=
                div_le_div_of_nonneg_right haε hD.le
              have h2 := amgm (1 + 1 / ((k:ℝ) + (m:ℝ))) (by positivity) ε hε_pos.le hε1
              have h3 : ε * (1 + 1 / ((k:ℝ) + (m:ℝ))) + (1 - ε) = 1 + ε / ((k:ℝ) + (m:ℝ)) := by
                field_simp
                ring
              linarith
            calc (((k:ℝ) + ((m:ℝ) + 1)) / (k:ℝ)) ^ ε
                = ((((k:ℝ) + (m:ℝ)) / (k:ℝ)) * (1 + 1 / ((k:ℝ) + (m:ℝ)))) ^ ε := by
                  congr 1
                  field_simp
                  ring
              _ = (((k:ℝ) + (m:ℝ)) / (k:ℝ)) ^ ε * (1 + 1 / ((k:ℝ) + (m:ℝ))) ^ ε := by
                  rw [Real.mul_rpow (by positivity) (by positivity)]
              _ ≤ (∏ j ∈ Finset.range m, (1 + a / ((k:ℝ) + (j:ℝ)))) *
                    (1 + a / ((k:ℝ) + (m:ℝ))) := by
                  apply mul_le_mul ih hstep
                  · exact (Real.rpow_pos_of_pos (by positivity) ε).le
                  · exact (Finset.prod_pos (fun j hj => by positivity)).le
      have hQle : Q ≤ ∏ j ∈ Finset.range (n - k), (1 + a / ((k:ℝ) + (j:ℝ))) := by
        have hPn := hP (n - k)
        have hq : (k:ℝ) + ((n - k : ℕ) : ℝ) = (n:ℝ) := by
          rw [← Nat.cast_add, hkn]
        rw [hq, Real.div_rpow hnpos.le hkpos.le, ← hQdef] at hPn
        exact hPn
      have hpt : ∀ j ∈ Finset.range (n - k),
          (a + ((k + j : ℕ) : ℝ)) = ((k:ℝ) + (j:ℝ)) * (1 + a / ((k:ℝ) + (j:ℝ))) := by
        intro j hj
        have hpos : (0:ℝ) < (k:ℝ) + (j:ℝ) := by
          have h2 : (0:ℝ) ≤ (j:ℝ) := by positivity
          linarith
        field_simp
        push_cast
        ring
      have htail : F * Q ≤ ∏ j ∈ Finset.range (n - k), (a + ((k + j : ℕ) : ℝ)) := by
        rw [hFdef]
        have hPpos : (0:ℝ) ≤ ∏ j ∈ Finset.range (n - k), ((k:ℝ) + (j:ℝ)) :=
          (Finset.prod_pos (fun j hj => by
            have h2 : (0:ℝ) ≤ (j:ℝ) := by positivity
            linarith)).le
        calc (∏ j ∈ Finset.range (n - k), ((k:ℝ) + (j:ℝ))) * Q
            ≤ (∏ j ∈ Finset.range (n - k), ((k:ℝ) + (j:ℝ))) *
                ∏ j ∈ Finset.range (n - k), (1 + a / ((k:ℝ) + (j:ℝ))) :=
              mul_le_mul_of_nonneg_left hQle hPpos
          _ = ∏ j ∈ Finset.range (n - k),
                (((k:ℝ) + (j:ℝ)) * (1 + a / ((k:ℝ) + (j:ℝ)))) := by
              rw [Finset.prod_mul_distrib]
          _ = ∏ j ∈ Finset.range (n - k), (a + ((k + j : ℕ) : ℝ)) := by
              exact Finset.prod_congr rfl (fun j hj => (hpt j hj).symm)
      have hrise : a ^ k * (F * Q) ≤ risingFac a n := by
        rw [hsplit]
        exact mul_le_mul hfirst htail (mul_nonneg hF.le hQ.le)
          (Finset.prod_pos (fun j hj => by positivity)).le
      have hratio : a ^ t / a ^ k ≤ 1 / ε := by
        have hsub : a ^ t / a ^ k = a ^ (t - (k:ℝ)) := (Real.rpow_sub_natCast ha0.ne' t k).symm
        rw [hsub]
        have hs : t - (k:ℝ) ≤ 0 := by linarith
        have hxa : (0:ℝ) < ε / a := div_pos hε_pos ha0
        have hxa1 : ε / a ≤ 1 := by
          have h2 : ε / a ≤ a / a := div_le_div_of_nonneg_right haε ha0.le
          rwa [div_self ha0.ne'] at h2
        have h := Real.rpow_le_rpow_of_exponent_ge hxa hxa1 hs
        rw [Real.rpow_zero, Real.div_rpow hε_pos.le ha0.le] at h
        have hp : (0:ℝ) < a ^ (t - (k:ℝ)) := Real.rpow_pos_of_pos ha0 _
        have hm := mul_le_mul_of_nonneg_right h hp.le
        have heq : (ε ^ (t - (k:ℝ)) / a ^ (t - (k:ℝ))) * a ^ (t - (k:ℝ)) = ε ^ (t - (k:ℝ)) := by
          field_simp
        have hneg : ε ^ (-1:ℝ) = 1 / ε := by
          have h2 := Real.rpow_sub_natCast hε_pos.ne' (0:ℝ) 1
          have h0 : (0:ℝ) - ((1:ℕ):ℝ) = (-1:ℝ) := by norm_num
          rw [h0] at h2
          rw [h2]
          simp
        rw [one_mul, heq] at hm
        have h2 : ε ^ (t - (k:ℝ)) ≤ ε ^ (-1:ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hε_pos hε1 (by linarith)
        rw [hneg] at h2
        exact le_trans hm h2
      have hnat2 : k.factorial = k * (k - 1).factorial := by
        rw [Nat.factorial_eq_prod_range_add_one, Nat.factorial_eq_prod_range_add_one]
        have h1 : k - 1 + 1 = k := Nat.sub_add_cancel hk1
        conv_lhs => rw [← h1]
        rw [Finset.prod_range_succ, h1, Nat.mul_comm]
      have hkfac : ((k.factorial : ℕ) : ℝ) = (k:ℝ) * ((k-1).factorial : ℝ) := by
        rw [hnat2]
        push_cast
        ring
      have hkε : (k:ℝ) ^ ε ≤ (k:ℝ) := by
        have h := amgm (k:ℝ) (le_of_lt hkpos) ε hε_pos.le hε1
        have h3 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk1
        nlinarith
      have hnat1 : (n - 1).factorial
          = (k - 1).factorial * (∏ j ∈ Finset.range (n - k), (k + j)) := by
        rw [Nat.factorial_eq_prod_range_add_one, Nat.factorial_eq_prod_range_add_one]
        have h1 : k - 1 + (n - k) = n - 1 := by omega
        conv_lhs => rw [← h1]
        rw [Finset.prod_range_add]
        congr 1
        exact Finset.prod_congr rfl (fun j hj => by omega)
      have hfactR : ((n - 1).factorial : ℝ) = ((k - 1).factorial : ℝ) * F := by
        rw [hFdef, hnat1, Nat.cast_mul, Nat.cast_prod]
        push_cast
        rfl
      have hmain3 : (k:ℝ)^ε * ((n-1).factorial : ℝ)
          ≤ Real.exp 1 * ((m+1).factorial : ℝ) * F := by
        have h1 : (k:ℝ)^ε * ((k-1).factorial : ℝ) ≤ ((m+1).factorial : ℝ) := by
          have hnn : (0:ℝ) ≤ ((k-1).factorial : ℝ) := by positivity
          have h4 : (k:ℝ)^ε * ((k-1).factorial : ℝ) ≤ (k:ℝ) * ((k-1).factorial : ℝ) :=
            mul_le_mul_of_nonneg_right hkε hnn
          rw [← hkfac] at h4
          have h5 : ((k.factorial : ℕ) : ℝ) ≤ ((m + 1).factorial : ℝ) := by
            have h6 := Nat.factorial_le hk_m
            exact_mod_cast h6
          linarith
        have hexp1 : (1:ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
        calc (k:ℝ)^ε * ((n-1).factorial : ℝ)
            = ((k:ℝ)^ε * ((k-1).factorial : ℝ)) * F := by
              rw [hfactR]; ring
          _ ≤ ((m+1).factorial : ℝ) * F := mul_le_mul_of_nonneg_right h1 hF.le
          _ ≤ Real.exp 1 * ((m+1).factorial : ℝ) * F := by
              have hfm : (0:ℝ) ≤ ((m+1).factorial : ℝ) := by positivity
              have hle2 := mul_le_mul_of_nonneg_right hexp1 hfm
              rw [one_mul] at hle2
              exact mul_le_mul_of_nonneg_right hle2 hF.le
      have hAk : (0:ℝ) < a ^ k := pow_pos ha0 k
      have hεne : ε ≠ 0 := hε_pos.ne'
      have hnne : ((n:ℝ)^ε) ≠ 0 := (Real.rpow_pos_of_pos hnpos ε).ne'
      have hkεne : ((k:ℝ)^ε) ≠ 0 := (Real.rpow_pos_of_pos hkpos ε).ne'
      have hfne : ((n-1).factorial : ℝ) ≠ 0 :=
        (by positivity : (0:ℝ) < ((n-1).factorial : ℝ)).ne'
      have hKQ : K * Q = Real.exp 1 * ((m+1).factorial : ℝ) /
          (ε * ((k:ℝ)^ε) * ((n-1).factorial : ℝ)) := by
        rw [hK, hQdef]
        field_simp
      have hkey : 1 / ε ≤ K * (F * Q) := by
        have hD3 : (0:ℝ) < ε * (((k:ℝ)^ε) * ((n-1).factorial : ℝ)) := by positivity
        refine le_of_mul_le_mul_right ?_ hD3
        have hL : (1 / ε) * (ε * (((k:ℝ)^ε) * ((n-1).factorial : ℝ)))
            = (k:ℝ)^ε * ((n-1).factorial : ℝ) := by
          field_simp
        have hR : (K * (F * Q)) * (ε * (((k:ℝ)^ε) * ((n-1).factorial : ℝ)))
            = Real.exp 1 * ((m+1).factorial : ℝ) * F := by
          have hre : K * (F * Q) = (K * Q) * F := by ring
          rw [hre, hKQ]
          field_simp
        rw [hL, hR]
        exact hmain3
      have hAkne : a ^ k ≠ 0 := hAk.ne'
      have hs2 : a ^ t = a ^ k * (a ^ t / a ^ k) := by
        field_simp
      have hle1 : a ^ t / a ^ k ≤ K * (F * Q) := by linarith
      have h1 : a ^ k * (a ^ t / a ^ k) ≤ a ^ k * (K * (F * Q)) :=
        mul_le_mul_of_nonneg_left hle1 hAk.le
      have h2 : a ^ k * (K * (F * Q)) = (a ^ k * (F * Q)) * K := by ring
      have h3 : (a ^ k * (F * Q)) * K ≤ risingFac a n * K :=
        mul_le_mul_of_nonneg_right hrise hKpos.le
      have hmul : a ^ t ≤ risingFac a n * K := by
        linarith [hs2, h1, h2, h3]
      have h4 := div_le_div_of_nonneg_right hmul (hfac.1 a n ha0).le
      have h5 : risingFac a n * K / risingFac a n = K := by
        have hRne : risingFac a n ≠ 0 := (hfac.1 a n ha0).ne'
        field_simp
      rwa [h5] at h4
    have hπa : 0 ≤ π a := hπ_nonneg a (Set.mem_Ioi.mpr ha0)
    exact mul_le_mul_of_nonneg_right hmain hπa
  have hfnn : ∀ a ∈ Set.Ioi ε, 0 ≤ a ^ t / risingFac a n * π a := by
    intro a ha
    have ha0 : 0 < a := lt_trans hε_pos ha
    have h1 : 0 < risingFac a n := hfac.1 a n ha0
    have h2 : 0 ≤ a ^ t := (Real.rpow_pos_of_pos ha0 t).le
    have h3 : 0 ≤ π a := hπ_nonneg a (Set.mem_Ioi.mpr ha0)
    exact mul_nonneg (div_nonneg h2 h1.le) h3
  have hmeas : AEStronglyMeasurable (fun a : ℝ => a ^ t / risingFac a n * π a)
      (volume.restrict (Set.Ioi ε)) := by
    have h1 : Measurable (fun a : ℝ => a ^ t) :=
      (Continuous.rpow_const continuous_id (fun x => Or.inr (le_trans zero_le_one ht))).measurable
    have h2 : Measurable (fun a : ℝ => risingFac a n) := by
      unfold risingFac
      exact Finset.measurable_prod _ (fun j _ => measurable_id.add measurable_const)
    exact ((h1.div h2).mul hπ_meas).aestronglyMeasurable
  have hnn_ae : 0 ≤ᵐ[volume.restrict (Set.Ioi ε)] (fun a : ℝ => a ^ t / risingFac a n * π a) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with a ha
    exact hfnn a ha
  have hlin : (∫⁻ a in Set.Ioi ε, ENNReal.ofReal (a ^ t / risingFac a n * π a)) ≤ ENNReal.ofReal K := by
    have step1 : (∫⁻ a in Set.Ioi ε, ENNReal.ofReal (a ^ t / risingFac a n * π a))
        ≤ ∫⁻ a in Set.Ioi ε, ENNReal.ofReal (K * π a) := by
      apply MeasureTheory.lintegral_mono_ae
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with a ha
      exact ENNReal.ofReal_le_ofReal (key a ha)
    have step3 : (∫⁻ a in Set.Ioi ε, ENNReal.ofReal (π a)) ≤ 1 := by
      calc (∫⁻ a in Set.Ioi ε, ENNReal.ofReal (π a))
          ≤ ∫⁻ a in Set.Ioi (0 : ℝ), ENNReal.ofReal (π a) :=
            MeasureTheory.lintegral_mono_set (Set.Ioi_subset_Ioi hε_pos.le)
        _ = 1 := hπ_prob
    calc (∫⁻ a in Set.Ioi ε, ENNReal.ofReal (a ^ t / risingFac a n * π a))
        ≤ ∫⁻ a in Set.Ioi ε, ENNReal.ofReal (K * π a) := step1
      _ = ENNReal.ofReal K * (∫⁻ a in Set.Ioi ε, ENNReal.ofReal (π a)) := by
          simp only [ENNReal.ofReal_mul hKpos.le]
          rw [MeasureTheory.lintegral_const_mul]
          exact ENNReal.measurable_ofReal.comp hπ_meas
      _ ≤ ENNReal.ofReal K * 1 := mul_le_mul_left' step3 _
      _ = ENNReal.ofReal K := mul_one _
  have hbridge : (∫ a in Set.Ioi ε, a ^ t / risingFac a n * π a)
      = (∫⁻ a in Set.Ioi ε, ENNReal.ofReal (a ^ t / risingFac a n * π a)).toReal :=
    MeasureTheory.integral_eq_lintegral_of_nonneg_ae hnn_ae hmeas
  rw [hbridge]
  exact ENNReal.toReal_le_of_le_ofReal hKpos.le hlin
  /- @proof-region region.target-node.session.4d996c229eba543a end -/

end Statlib.Imported
end
