import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q12.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q12.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q12.ProvedNodes.Node_3754312584_2556f128_aac4c978
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q12.ProvedNodes.Node_4023382197_14c17dfb_9ed69871


open MeasureTheory ProbabilityTheory

open MeasureTheory ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_3608866754_ebb2fee6 : ∀ (n : ℕ) (hn : 1 ≤ n)
    (h : ℝ) (hh : 0 < h)
    (K : ℝ → ℝ) (hK_meas : Measurable K)
    (hK_nonneg : ∀ u, 0 ≤ K u)
    (hK_int : Integrable K)
    (hK_one : ∫ u, K u = 1)
    (f : ℝ → ℝ) (hf_meas : Measurable f)
    (hf_int : Integrable f),
    ∀ (k : Fin n) (a : Fin n → ℝ) (t : ℝ),
      |(∫ x, |((n : ℝ) * h)⁻¹ * ∑ i : Fin n, K ((x - a i) / h) - f x|)
        - (∫ x, |((n : ℝ) * h)⁻¹ * ∑ i : Fin n,
            K ((x - Function.update a k t i) / h) - f x|)|
      ≤ 2 / (n : ℝ) := by
  /- @proof-region region.target-node.session.585f6c2f5d9df983 begin -/
  intro n hn h hh K hK_meas hK_nonneg hK_int hK_one f hf_meas hf_int
  intro k a t
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hh0 : h ≠ 0 := ne_of_gt hh
  have hc : (0 : ℝ) < ((n : ℝ) * h)⁻¹ := inv_pos.mpr (mul_pos hnpos hh)
  have hdep := statopia_math_node_4023382197_14c17dfb n hn h hh K hK_meas hK_nonneg hK_int hK_one
  have hF_int : Integrable (fun x : ℝ => ((n : ℝ) * h)⁻¹ * ∑ i : Fin n, K ((x - a i) / h)) :=
    (hdep a).1
  have hG_int : Integrable (fun x : ℝ => ((n : ℝ) * h)⁻¹ * ∑ i : Fin n,
      K ((x - Function.update a k t i) / h)) := (hdep (Function.update a k t)).1
  have htri : ∀ (u v : ℝ → ℝ), Integrable u → Integrable v →
      |(∫ x, |u x - f x|) - (∫ x, |v x - f x|)| ≤ ∫ x, |u x - v x| := by
    intro u v hu hv
    have hu1 : Integrable (fun x : ℝ => |u x - f x|) := (hu.sub hf_int).abs
    have hv1 : Integrable (fun x : ℝ => |v x - f x|) := (hv.sub hf_int).abs
    have huv : Integrable (fun x : ℝ => |u x - v x|) := (hu.sub hv).abs
    have hvu : Integrable (fun x : ℝ => |v x - u x|) := (hv.sub hu).abs
    have hA : (∫ x, |u x - f x|) - (∫ x, |v x - f x|) ≤ ∫ x, |u x - v x| := by
      have hmono : ∫ x, |u x - f x| ≤ ∫ x, (|v x - f x| + |u x - v x|) := by
        apply MeasureTheory.integral_mono
        · exact hu1
        · exact hv1.add huv
        · intro x
          show |u x - f x| ≤ |v x - f x| + |u x - v x|
          rw [show u x - f x = (v x - f x) + (u x - v x) from by ring]
          exact abs_add_le _ _
      rw [MeasureTheory.integral_add hv1 huv] at hmono
      linarith
    have hB : (∫ x, |v x - f x|) - (∫ x, |u x - f x|) ≤ ∫ x, |u x - v x| := by
      have hmono : ∫ x, |v x - f x| ≤ ∫ x, (|u x - f x| + |v x - u x|) := by
        apply MeasureTheory.integral_mono
        · exact hv1
        · exact hu1.add hvu
        · intro x
          show |v x - f x| ≤ |u x - f x| + |v x - u x|
          rw [show v x - f x = (u x - f x) + (v x - u x) from by ring]
          exact abs_add_le _ _
      rw [MeasureTheory.integral_add hu1 hvu] at hmono
      have habs : ∫ x, |v x - u x| = ∫ x, |u x - v x| := by
        congr 1
        funext x
        exact abs_sub_comm _ _
      rw [habs] at hmono
      linarith
    refine abs_le.mpr ⟨?_, ?_⟩
    · linarith
    · linarith
  have hoff : ∀ i : Fin n, i ≠ k → Function.update a k t i = a i := by
    intro i hik
    simp only [Function.update, dif_neg hik]
  have hdiff : ∀ x : ℝ, ((n : ℝ) * h)⁻¹ * ∑ i : Fin n, K ((x - a i) / h)
      - ((n : ℝ) * h)⁻¹ * ∑ i : Fin n, K ((x - Function.update a k t i) / h)
      = ((n : ℝ) * h)⁻¹ * (K ((x - a k) / h) - K ((x - Function.update a k t k) / h)) := by
    intro x
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_eq_single k ?_ ?_
    · intro i _ hik
      rw [hoff i hik, sub_self]
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  have hC : ∫ x, |(((n : ℝ) * h)⁻¹ * ∑ i : Fin n, K ((x - a i) / h))
      - ((n : ℝ) * h)⁻¹ * ∑ i : Fin n, K ((x - Function.update a k t i) / h)|
      = ((n : ℝ) * h)⁻¹ * ∫ x, |K ((x - a k) / h) - K ((x - Function.update a k t k) / h)| := by
    have hpt : ∀ x : ℝ, |(((n : ℝ) * h)⁻¹ * ∑ i : Fin n, K ((x - a i) / h))
        - ((n : ℝ) * h)⁻¹ * ∑ i : Fin n, K ((x - Function.update a k t i) / h)|
        = ((n : ℝ) * h)⁻¹ * |K ((x - a k) / h) - K ((x - Function.update a k t k) / h)| := by
      intro x
      rw [hdiff x, abs_mul, abs_of_pos hc]
    simp only [hpt]
    rw [MeasureTheory.integral_const_mul]
  have hcoef : ∀ y : ℝ, ((n : ℝ) * h)⁻¹ * ((n : ℝ) * y) = h⁻¹ * y := by
    intro y
    rw [mul_inv_rev, mul_assoc, ← mul_assoc (n : ℝ)⁻¹ (n : ℝ) y, inv_mul_cancel₀ hn0, one_mul]
  have hsumc : ∀ (c x : ℝ), ∑ i : Fin n, K ((x - c) / h) = (n : ℝ) * K ((x - c) / h) := by
    intro c x
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hKshift_int : ∀ c : ℝ, Integrable (fun x : ℝ => K ((x - c) / h)) := by
    intro c
    have hi0 : Integrable (fun x : ℝ => ((n : ℝ) * h)⁻¹ * ∑ i : Fin n, K ((x - c) / h)) :=
      (hdep (fun _ : Fin n => c)).1
    have hi : Integrable (fun x : ℝ => h⁻¹ * K ((x - c) / h)) := by
      refine hi0.congr ?_
      filter_upwards with x
      show ((n : ℝ) * h)⁻¹ * ∑ i : Fin n, K ((x - c) / h) = h⁻¹ * K ((x - c) / h)
      rw [hsumc c x]
      exact hcoef _
    have h4 := hi.const_mul h
    refine h4.congr ?_
    filter_upwards with x
    show h * (h⁻¹ * K ((x - c) / h)) = K ((x - c) / h)
    rw [← mul_assoc, mul_inv_cancel₀ hh0, one_mul]
  have hKshift_val : ∀ c : ℝ, ∫ x, K ((x - c) / h) ≤ h := by
    intro c
    have hle0 : (0 : ℝ) ≤ h⁻¹ := le_of_lt (inv_pos.mpr hh)
    have h1 : ∫ x, |h⁻¹ * K ((x - c) / h)| = h⁻¹ * ∫ x, K ((x - c) / h) := by
      have hpt : ∀ x : ℝ, |h⁻¹ * K ((x - c) / h)| = h⁻¹ * K ((x - c) / h) := by
        intro x
        exact abs_of_nonneg (mul_nonneg hle0 (hK_nonneg _))
      simp only [hpt]
      rw [MeasureTheory.integral_const_mul]
    have h2 : ∫ x, |h⁻¹ * K ((x - c) / h)| ≤ 1 := by
      have hbase : ∫ x, |((n : ℝ) * h)⁻¹ * ∑ i : Fin n, K ((x - c) / h)| ≤ 1 :=
        (hdep (fun _ : Fin n => c)).2
      rw [show ∫ x, |((n : ℝ) * h)⁻¹ * ∑ i : Fin n, K ((x - c) / h)|
          = ∫ x, |h⁻¹ * K ((x - c) / h)| from by
        congr 1
        funext x
        rw [hsumc c x, hcoef]] at hbase
      exact hbase
    have h3 : h⁻¹ * ∫ x, K ((x - c) / h) ≤ 1 := by
      rw [← h1]
      exact h2
    calc ∫ x, K ((x - c) / h) = h * (h⁻¹ * ∫ x, K ((x - c) / h)) := by
          rw [← mul_assoc, mul_inv_cancel₀ hh0, one_mul]
      _ ≤ h * 1 := mul_le_mul_of_nonneg_left h3 hh.le
      _ = h := by ring
  have hbound : ∀ c : ℝ, ∫ x, |K ((x - a k) / h) - K ((x - c) / h)| ≤ 2 * h := by
    intro c
    have h1 : Integrable (fun x : ℝ => K ((x - a k) / h)) := hKshift_int (a k)
    have h2 : Integrable (fun x : ℝ => K ((x - c) / h)) := hKshift_int c
    have habs : Integrable (fun x : ℝ => |K ((x - a k) / h) - K ((x - c) / h)|) := (h1.sub h2).abs
    have hsum : Integrable (fun x : ℝ => K ((x - a k) / h) + K ((x - c) / h)) := h1.add h2
    have hmono : ∫ x, |K ((x - a k) / h) - K ((x - c) / h)|
        ≤ ∫ x, (K ((x - a k) / h) + K ((x - c) / h)) := by
      apply MeasureTheory.integral_mono
      · exact habs
      · exact hsum
      · intro x
        have hp1 : (0 : ℝ) ≤ K ((x - a k) / h) := hK_nonneg _
        have hp2 : (0 : ℝ) ≤ K ((x - c) / h) := hK_nonneg _
        show |K ((x - a k) / h) - K ((x - c) / h)| ≤ K ((x - a k) / h) + K ((x - c) / h)
        rw [show K ((x - a k) / h) - K ((x - c) / h)
            = K ((x - a k) / h) + -K ((x - c) / h) from by ring]
        calc |K ((x - a k) / h) + -K ((x - c) / h)|
            ≤ |K ((x - a k) / h)| + |-K ((x - c) / h)| := abs_add_le _ _
          _ = K ((x - a k) / h) + K ((x - c) / h) := by
              rw [abs_neg, abs_of_nonneg hp1, abs_of_nonneg hp2]
    calc ∫ x, |K ((x - a k) / h) - K ((x - c) / h)|
        ≤ ∫ x, (K ((x - a k) / h) + K ((x - c) / h)) := hmono
      _ = (∫ x, K ((x - a k) / h)) + ∫ x, K ((x - c) / h) := MeasureTheory.integral_add h1 h2
      _ ≤ h + h := add_le_add (hKshift_val (a k)) (hKshift_val c)
      _ = 2 * h := by ring
  have hfinal : ((n : ℝ) * h)⁻¹ * (2 * h) = 2 / (n : ℝ) := by
    field_simp
  have key : |(∫ x, |((n : ℝ) * h)⁻¹ * ∑ i : Fin n, K ((x - a i) / h) - f x|)
      - (∫ x, |((n : ℝ) * h)⁻¹ * ∑ i : Fin n, K ((x - Function.update a k t i) / h) - f x|)|
      ≤ ((n : ℝ) * h)⁻¹ * (2 * h) :=
    le_trans (htri _ _ hF_int hG_int)
      (le_trans (le_of_eq hC)
        (mul_le_mul_of_nonneg_left (hbound (Function.update a k t k)) (le_of_lt hc)))
  rw [← hfinal]
  exact key
  /- @proof-region region.target-node.session.585f6c2f5d9df983 end -/
