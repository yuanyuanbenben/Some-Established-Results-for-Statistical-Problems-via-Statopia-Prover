import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q08.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q08.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q08.ProvedNodes.Node_1247330666_ee8168ea_f3a293de

open MeasureTheory Matrix ProbabilityTheory

open MeasureTheory Matrix ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_3084854362_14c87009 : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n d : ℕ) (hn : 1 ≤ n) (hd : 2 ≤ d)
    (sigma : ℝ) (hsigma : 0 < sigma)
    (X : Matrix (Fin n) (Fin d) ℝ)
    (hcols : ∀ j,
      dotProduct (fun i => X i j) (fun i => X i j) / (n : ℝ) ≤ 1)
    (w : Ω → Fin n → ℝ)
    (hw : ∀ a : Fin n → ℝ,
      HasLaw (fun ω => dotProduct a (w ω))
        (gaussianReal 0
          (Real.toNNReal (sigma ^ 2 * dotProduct a a))) P),
    let lambda := 4 * sigma *
      Real.sqrt (Real.log (d : ℝ) / (n : ℝ))
    P {ω | ∀ j : Fin d, |((Xᵀ *ᵥ w ω) j) / (n : ℝ)| ≤ lambda / 2} ≥
      ENNReal.ofReal (1 - 2 / (d : ℝ)) := by
  /- @proof-region region.target-node.session.cd5c99a4ea5bf370 begin -/
  intro Ω mΩ P hP n d hn hd sigma hsigma X hcols w hw
  let lambda := 4 * sigma * Real.sqrt (Real.log (d : ℝ) / (n : ℝ))
  change P {ω | ∀ j : Fin d, |((Xᵀ *ᵥ w ω) j) / (n : ℝ)| ≤ lambda / 2} ≥ ENNReal.ofReal (1 - 2 / (d : ℝ))
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd_gt : (1 : ℝ) < (d : ℝ) := by linarith
  have hd_pos : (0 : ℝ) < (d : ℝ) := by linarith
  have hlog_pos : 0 < Real.log (d : ℝ) := Real.log_pos hd_gt
  have hlambda_pos : 0 < lambda := by
    have hlam : lambda = 4 * sigma * Real.sqrt (Real.log (d : ℝ) / (n : ℝ)) := rfl
    rw [hlam]
    exact mul_pos (mul_pos (by norm_num) hsigma) (Real.sqrt_pos.mpr (div_pos hlog_pos hn_pos))
  have hTpos : 0 < (n : ℝ) * lambda / 2 := by
    have h : 0 < (n : ℝ) * lambda := mul_pos hn_pos hlambda_pos
    linarith
  have hmv : ∀ (j : Fin d) (ω : Ω), ((Xᵀ *ᵥ w ω) j) = dotProduct (fun i => X i j) (w ω) := by
    intro j ω
    rfl
  have key : ∀ j : Fin d, P {ω : Ω | lambda / 2 < |((Xᵀ *ᵥ w ω) j) / (n : ℝ)|} ≤ ENNReal.ofReal (2 / (d : ℝ) ^ 2) := by
    intro j
    have hcol : dotProduct (fun i => X i j) (fun i => X i j) ≤ (n : ℝ) := by
      have h := (div_le_iff₀ hn_pos).mp (hcols j)
      simpa using h
    have hdotnn : (0:ℝ) ≤ dotProduct (fun i => X i j) (fun i => X i j) := by
      have h := dotProduct_self_star_nonneg (fun i => X i j)
      simpa using h
    have hnn : (0:ℝ) ≤ sigma ^ 2 * dotProduct (fun i => X i j) (fun i => X i j) :=
      mul_nonneg (sq_nonneg sigma) hdotnn
    have hvle : (Real.toNNReal (sigma ^ 2 * dotProduct (fun i => X i j) (fun i => X i j)) : ℝ) ≤ sigma ^ 2 * (n : ℝ) := by
      rw [Real.coe_toNNReal]
      · exact mul_le_mul_of_nonneg_left hcol (sq_nonneg sigma)
      · exact hnn
    have hYj : HasLaw (fun ω => dotProduct (fun i => X i j) (w ω))
        (gaussianReal 0 (Real.toNNReal (sigma ^ 2 * dotProduct (fun i => X i j) (fun i => X i j)))) P := hw (fun i => X i j)
    have hT2 : ((n : ℝ) * lambda / 2) ^ 2 = 4 * (n : ℝ) * sigma ^ 2 * Real.log (d : ℝ) := by
      have hlam : lambda = 4 * sigma * Real.sqrt (Real.log (d : ℝ) / (n : ℝ)) := rfl
      rw [hlam]
      have hsq : Real.sqrt (Real.log (d : ℝ) / (n : ℝ)) * Real.sqrt (Real.log (d : ℝ) / (n : ℝ)) * (n : ℝ) = Real.log (d : ℝ) := by
        rw [← sq, Real.sq_sqrt (le_of_lt (div_pos hlog_pos hn_pos))]
        field_simp
      nlinarith [hsq, hn_pos]
    have hset : {ω : Ω | lambda / 2 < |((Xᵀ *ᵥ w ω) j) / (n : ℝ)|}
        = {ω : Ω | (n : ℝ) * lambda / 2 < |dotProduct (fun i => X i j) (w ω)|} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      rw [hmv j ω, abs_div, abs_of_pos hn_pos]
      rw [lt_div_iff₀ hn_pos]
      constructor <;> intro h <;> nlinarith [h]
    rw [hset]
    obtain ⟨h0, hpos⟩ := statopia_math_node_1247330666_ee8168ea P
      (Real.toNNReal (sigma ^ 2 * dotProduct (fun i => X i j) (fun i => X i j)))
      ((n : ℝ) * lambda / 2) hTpos (fun ω => dotProduct (fun i => X i j) (w ω)) hYj
    by_cases hv0 : Real.toNNReal (sigma ^ 2 * dotProduct (fun i => X i j) (fun i => X i j)) = 0
    · rw [h0 hv0]; exact zero_le _
    · have hvpos_nn : (0 : NNReal) < Real.toNNReal (sigma ^ 2 * dotProduct (fun i => X i j) (fun i => X i j)) :=
        lt_of_le_of_ne (zero_le _) (Ne.symm hv0)
      have hvpos : (0 : ℝ) < (Real.toNNReal (sigma ^ 2 * dotProduct (fun i => X i j) (fun i => X i j)) : ℝ) := by
        exact_mod_cast hvpos_nn
      refine le_trans (hpos hvpos_nn) (ENNReal.ofReal_le_ofReal ?_)
      have harg : 2 * Real.log (d : ℝ) ≤ ((n : ℝ) * lambda / 2) ^ 2 / (2 * (Real.toNNReal (sigma ^ 2 * dotProduct (fun i => X i j) (fun i => X i j)) : ℝ)) := by
        rw [hT2]
        rw [le_div_iff₀ (mul_pos (by norm_num : (0:ℝ) < 2) hvpos)]
        nlinarith [mul_le_mul_of_nonneg_left hvle (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hlog_pos.le)]
      have hexp : Real.exp (-(((n : ℝ) * lambda / 2) ^ 2 / (2 * (Real.toNNReal (sigma ^ 2 * dotProduct (fun i => X i j) (fun i => X i j)) : ℝ)))) ≤ 1 / (d : ℝ) ^ 2 := by
        have hle : -(((n : ℝ) * lambda / 2) ^ 2 / (2 * (Real.toNNReal (sigma ^ 2 * dotProduct (fun i => X i j) (fun i => X i j)) : ℝ))) ≤ -(2 * Real.log (d : ℝ)) := by linarith [harg]
        have heq : Real.exp (-(2 * Real.log (d : ℝ))) = 1 / (d : ℝ) ^ 2 := by
          have hdne : (d : ℝ) ≠ 0 := ne_of_gt hd_pos
          rw [show -(2 * Real.log (d : ℝ)) = -Real.log (d : ℝ) + -Real.log (d : ℝ) by ring]
          rw [Real.exp_add, Real.exp_neg, Real.exp_log hd_pos]
          field_simp
        calc Real.exp (-(((n : ℝ) * lambda / 2) ^ 2 / (2 * (Real.toNNReal (sigma ^ 2 * dotProduct (fun i => X i j) (fun i => X i j)) : ℝ)))) ≤ Real.exp (-(2 * Real.log (d : ℝ))) := Real.exp_le_exp.mpr hle
          _ = 1 / (d : ℝ) ^ 2 := heq
      calc 2 * Real.exp (-(((n : ℝ) * lambda / 2) ^ 2 / (2 * (Real.toNNReal (sigma ^ 2 * dotProduct (fun i => X i j) (fun i => X i j)) : ℝ)))) ≤ 2 * (1 / (d : ℝ) ^ 2) := by nlinarith [hexp]
        _ = 2 / (d : ℝ) ^ 2 := by ring
  have hUnion_eq : {ω : Ω | ∀ j : Fin d, |((Xᵀ *ᵥ w ω) j) / (n : ℝ)| ≤ lambda / 2}ᶜ
      = ⋃ j : Fin d, {ω : Ω | lambda / 2 < |((Xᵀ *ᵥ w ω) j) / (n : ℝ)|} := by
    ext ω
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_iUnion, not_forall, not_le]
  have hsum : (∑ j : Fin d, ENNReal.ofReal (2 / (d : ℝ) ^ 2)) = ENNReal.ofReal (2 / (d : ℝ)) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (f := fun _ => (2 : ℝ) / (d : ℝ) ^ 2)
      (fun _ _ => div_nonneg (by norm_num) (sq_nonneg (d : ℝ)))]
    congr 1
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hdne : (d : ℝ) ≠ 0 := ne_of_gt hd_pos
    field_simp
  have hUnion : P {ω : Ω | ∀ j : Fin d, |((Xᵀ *ᵥ w ω) j) / (n : ℝ)| ≤ lambda / 2}ᶜ
      ≤ ENNReal.ofReal (2 / (d : ℝ)) := by
    rw [hUnion_eq]
    calc P (⋃ j : Fin d, {ω : Ω | lambda / 2 < |((Xᵀ *ᵥ w ω) j) / (n : ℝ)|})
        ≤ ∑' j : Fin d, P {ω : Ω | lambda / 2 < |((Xᵀ *ᵥ w ω) j) / (n : ℝ)|} := measure_iUnion_le (μ := P) _
      _ = ∑ j : Fin d, P {ω : Ω | lambda / 2 < |((Xᵀ *ᵥ w ω) j) / (n : ℝ)|} := by rw [tsum_fintype]
      _ ≤ ∑ j : Fin d, ENNReal.ofReal (2 / (d : ℝ) ^ 2) := Finset.sum_le_sum (fun j _ => key j)
      _ = ENNReal.ofReal (2 / (d : ℝ)) := hsum
  have hcompl : (1 : ENNReal) ≤ P {ω : Ω | ∀ j : Fin d, |((Xᵀ *ᵥ w ω) j) / (n : ℝ)| ≤ lambda / 2}
      + P ({ω : Ω | ∀ j : Fin d, |((Xᵀ *ᵥ w ω) j) / (n : ℝ)| ≤ lambda / 2}ᶜ) := by
    have h := measure_union_le (μ := P)
      {ω : Ω | ∀ j : Fin d, |((Xᵀ *ᵥ w ω) j) / (n : ℝ)| ≤ lambda / 2}
      ({ω : Ω | ∀ j : Fin d, |((Xᵀ *ᵥ w ω) j) / (n : ℝ)| ≤ lambda / 2}ᶜ)
    have hU : {ω : Ω | ∀ j : Fin d, |((Xᵀ *ᵥ w ω) j) / (n : ℝ)| ≤ lambda / 2}
        ∪ ({ω : Ω | ∀ j : Fin d, |((Xᵀ *ᵥ w ω) j) / (n : ℝ)| ≤ lambda / 2}ᶜ) = Set.univ := by
      simp
    rw [hU, measure_univ] at h
    exact h
  have h2d : (2 : ℝ) / (d : ℝ) ≤ 1 := by
    rw [div_le_iff₀ hd_pos]
    simpa using hd2
  have hmain : (1 : ENNReal) ≤ P {ω : Ω | ∀ j : Fin d, |((Xᵀ *ᵥ w ω) j) / (n : ℝ)| ≤ lambda / 2}
      + ENNReal.ofReal (2 / (d : ℝ)) :=
    le_trans hcompl (add_le_add le_rfl hUnion)
  have hkey : ENNReal.ofReal (1 - 2 / (d : ℝ)) = 1 - ENNReal.ofReal (2 / (d : ℝ)) := by
    rw [ENNReal.ofReal_sub 1 (div_nonneg (by norm_num : (0:ℝ) ≤ 2) (le_of_lt hd_pos) : (0:ℝ) ≤ 2 / (d : ℝ)), ENNReal.ofReal_one]
  have hfin : ENNReal.ofReal (1 - 2 / (d : ℝ))
      ≤ P {ω : Ω | ∀ j : Fin d, |((Xᵀ *ᵥ w ω) j) / (n : ℝ)| ≤ lambda / 2} := by
    rw [hkey]
    exact tsub_le_iff_right.mpr hmain
  exact hfin
  /- @proof-region region.target-node.session.cd5c99a4ea5bf370 end -/
