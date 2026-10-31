import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q25.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q25.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q25.ProvedNodes.Node_1239051236_4b1511cf_0d4a601d
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q25.ProvedNodes.Node_2372557247_ba69a24e_468f5f42
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q25.ProvedNodes.Node_3138288691_f6d99626_7613c66a



open MeasureTheory ProbabilityTheory
open scoped BigOperators

open MeasureTheory ProbabilityTheory
open scoped BigOperators

set_option autoImplicit false in
theorem statopia_math_node_493757669_8e9c5e2f : ∀ (n : ℕ) (hn : 1 ≤ n) (a : ℝ)
    (ha_nonneg : 0 ≤ a) (ha_le : a ≤ (n : ℝ)),
    Real.exp (-a) - (1 - a / (n : ℝ)) ^ n ≤ 1 / (n : ℝ) := by
  /- @proof-region region.target-node.session.3682ac47781fdb43 begin -/
  intro n hn a ha_nonneg ha_le
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  set z : ℝ := a / (n : ℝ) with hz
  have hz_nonneg : 0 ≤ z := by
    rw [hz]
    exact div_nonneg ha_nonneg (le_of_lt hnpos)
  have hz_le_one : z ≤ 1 := by
    rw [hz, div_le_one hnpos]
    exact ha_le
  have hzn : z * (n : ℝ) = a := by
    rw [hz]
    field_simp
  have hB_nonneg : (0 : ℝ) ≤ 1 - z := by linarith
  have hBE : 1 - z ≤ Real.exp (-z) := by
    have h := statopia_math_node_3138288691_f6d99626 1 le_rfl z hz_nonneg hz_le_one
    simpa using h
  have hpd := statopia_math_node_2372557247_ba69a24e n hn (1 - z) (Real.exp (-z)) hB_nonneg hBE
  have hgap : Real.exp (-z) - (1 - z) ≤ z ^ 2 / 2 := by
    have h := statopia_math_node_1239051236_4b1511cf z hz_nonneg
    linarith
  have hstep1 : Real.exp (-z) ^ n - (1 - z) ^ n ≤
      (n : ℝ) * Real.exp (-z) ^ (n - 1) * (z ^ 2 / 2) := by
    have hmono : (n : ℝ) * Real.exp (-z) ^ (n - 1) * (Real.exp (-z) - (1 - z)) ≤
        (n : ℝ) * Real.exp (-z) ^ (n - 1) * (z ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left hgap (by positivity)
    linarith [hpd.1]
  have harg : (n : ℝ) * (-z) = -a := by
    have h2 : (n : ℝ) * (-z) = -(z * (n : ℝ)) := by ring
    linarith
  have hexp_a : Real.exp (-a) = Real.exp (-z) ^ n := by
    rw [← harg]
    exact Real.exp_nat_mul (-z) n
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn]
    simp
  have harg2 : ((n - 1 : ℕ) : ℝ) * (-z) = -a + z := by
    rw [hcast]
    have h3 : ((n : ℝ) - 1) * (-z) = -(z * (n : ℝ)) + z := by ring
    linarith
  have hexp_pow : Real.exp (-z) ^ (n - 1) = Real.exp (-a + z) := by
    rw [← Real.exp_nat_mul (-z) (n - 1), harg2]
  have hstep2 : Real.exp (-a) - (1 - z) ^ n ≤ (n : ℝ) * Real.exp (-a + z) * (z ^ 2 / 2) := by
    rw [hexp_a, ← hexp_pow]
    exact hstep1
  have hkey : a ^ 2 * Real.exp (-a + z) ≤ 2 := by
    by_cases h1 : a ≤ 1
    · have hz_le_a : z ≤ a := by
        rw [← hzn]
        have hprod : (0 : ℝ) ≤ z * ((n : ℝ) - 1) := mul_nonneg hz_nonneg (by linarith)
        nlinarith
      have hexp1 : Real.exp (-a + z) ≤ 1 := by
        have hle : -a + z ≤ 0 := by linarith
        calc Real.exp (-a + z) ≤ Real.exp 0 := Real.exp_le_exp.mpr hle
          _ = 1 := Real.exp_zero
      have ha2 : a ^ 2 ≤ 1 := by nlinarith
      have hmul : a ^ 2 * Real.exp (-a + z) ≤ 1 * 1 :=
        mul_le_mul ha2 hexp1 (le_of_lt (Real.exp_pos _)) (by norm_num)
      linarith
    · push_neg at h1
      have hexp_le : Real.exp (-a + z) ≤ Real.exp (1 - a) := by
        apply Real.exp_le_exp.mpr
        linarith
      have ht : (0 : ℝ) ≤ a - 1 := by linarith
      have hsum := Real.sum_le_exp_of_nonneg ht 3
      have heval : (∑ i ∈ Finset.range 3, (a - 1) ^ i / (Nat.factorial i : ℝ)) =
          1 + (a - 1) + (a - 1) ^ 2 / 2 := by
        simp [Finset.sum_range_succ, Nat.factorial]
      rw [heval] at hsum
      have htail : a ^ 2 / 2 ≤ Real.exp (a - 1) := by nlinarith
      have hmul : Real.exp (a - 1) * Real.exp (1 - a) = 1 := by
        rw [← Real.exp_add, show (a - 1) + (1 - a) = 0 by ring, Real.exp_zero]
      have htmp : a ^ 2 / 2 * Real.exp (1 - a) ≤ Real.exp (a - 1) * Real.exp (1 - a) :=
        mul_le_mul_of_nonneg_right htail (le_of_lt (Real.exp_pos (1 - a)))
      have hcase2 : a ^ 2 * Real.exp (1 - a) ≤ 2 := by nlinarith [htmp, hmul]
      have hstep3 : a ^ 2 * Real.exp (-a + z) ≤ a ^ 2 * Real.exp (1 - a) :=
        mul_le_mul_of_nonneg_left hexp_le (by positivity)
      linarith
  have hzsq : z ^ 2 * (n : ℝ) ^ 2 = a ^ 2 := by
    rw [← hzn]
    ring
  have hfinal : (n : ℝ) * Real.exp (-a + z) * (z ^ 2 / 2) ≤ 1 / (n : ℝ) := by
    have hprod2 : (n : ℝ) * Real.exp (-a + z) * (z ^ 2 / 2) * (n : ℝ) =
        Real.exp (-a + z) * (z ^ 2 * (n : ℝ) ^ 2) / 2 := by ring
    have hclear : (n : ℝ) * Real.exp (-a + z) * (z ^ 2 / 2) * (n : ℝ) ≤ 1 := by
      rw [hprod2, hzsq]
      linarith [hkey]
    have hstep := mul_le_mul_of_nonneg_right hclear (le_of_lt (inv_pos.mpr hnpos))
    rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hnpos), mul_one, one_mul] at hstep
    rwa [one_div]
  linarith [hstep2, hfinal]
  /- @proof-region region.target-node.session.3682ac47781fdb43 end -/
