import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q12.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q12.Base

open MeasureTheory ProbabilityTheory

open MeasureTheory ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_4023382197_14c17dfb : ∀ (n : ℕ) (hn : 1 ≤ n)
    (h : ℝ) (hh : 0 < h)
    (K : ℝ → ℝ) (hK_meas : Measurable K)
    (hK_nonneg : ∀ u, 0 ≤ K u)
    (hK_int : Integrable K)
    (hK_one : ∫ u, K u = 1),
    ∀ a : Fin n → ℝ,
      Integrable (fun x ↦ ((n : ℝ) * h)⁻¹ * ∑ i : Fin n, K ((x - a i) / h)) ∧
        ∫ x, |((n : ℝ) * h)⁻¹ * ∑ i : Fin n, K ((x - a i) / h)| ∂volume ≤ 1 := by
  /- @proof-region region.target-node.session.a44a4e604cd3c12c begin -/
  intro n hn h hh K hK_meas hK_nonneg hK_int hK_one a
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le zero_lt_one hn1
  have hnh : (0 : ℝ) < (n : ℝ) * h := mul_pos hnpos hh
  have hnhne : (n : ℝ) * h ≠ 0 := ne_of_gt hnh
  have hcpos : (0 : ℝ) < ((n : ℝ) * h)⁻¹ := inv_pos.2 hnh
  have htrans : ∀ (c : ℝ) (f : ℝ → ℝ), ∫ x, f (x - c) = ∫ x, f x := by
    intro c f
    first
      | exact MeasureTheory.integral_sub_right_eq_self f c
      | exact MeasureTheory.Measure.integral_comp_sub_right f c
      | exact MeasureTheory.integral_sub_right_eq_self volume f c
  have htrans_intble : ∀ (c : ℝ) (f : ℝ → ℝ), Integrable f → Integrable (fun x => f (x - c)) := by
    intro c f hf
    first
      | exact MeasureTheory.Integrable.comp_sub_right hf c
      | simpa [sub_eq_add_neg] using MeasureTheory.Integrable.comp_add_right hf (-c)
  have hK_abs_one : ∫ u : ℝ, |K u| = 1 := by
    rw [← hK_one]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    exact abs_of_nonneg (hK_nonneg y)
  have hsub : ∀ c : ℝ, ∫ x, |K ((x - c) / h)| = h := by
    intro c
    calc ∫ x, |K ((x - c) / h)|
        = ∫ x, (fun y : ℝ => |K (y - c / h)|) (x / h) := by simp only [sub_div]
      _ = |h| • ∫ y : ℝ, |K (y - c / h)| := MeasureTheory.Measure.integral_comp_div (fun y : ℝ => |K (y - c / h)|) h
      _ = h * ∫ y : ℝ, |K (y - c / h)| := by rw [abs_of_pos hh, smul_eq_mul]
      _ = h * ∫ y : ℝ, |K y| := by
            simpa using congrArg (fun t : ℝ => h * t) (htrans (c / h) (fun y : ℝ => |K y|))
      _ = h := by rw [hK_abs_one, mul_one]
  have hscale_intble : ∀ (f : ℝ → ℝ), Integrable f → Integrable (fun x : ℝ => f (x / h)) := by
    intro f hf
    have h := hf.comp_mul_left' (R := h⁻¹) (inv_ne_zero (ne_of_gt hh))
    simpa [div_eq_inv_mul] using h
  have hInt_each : ∀ i : Fin n, Integrable (fun x : ℝ => K ((x - a i) / h)) := by
    intro i
    have h1 : Integrable (fun y : ℝ => K (y - a i / h)) := htrans_intble (a i / h) K hK_int
    have h2 : Integrable (fun x : ℝ => (fun y : ℝ => K (y - a i / h)) (x / h)) :=
      hscale_intble _ h1
    simpa [sub_div] using h2
  have hInt_abs_i : ∀ i : Fin n, Integrable (fun x : ℝ => |K ((x - a i) / h)|) := by
    intro i
    first
      | exact (hInt_each i).abs
      | exact MeasureTheory.Integrable.abs (hInt_each i)
  have hInt_sum : Integrable (fun x : ℝ => ∑ i : Fin n, K ((x - a i) / h)) := by
    first
      | exact MeasureTheory.integrable_finset_sum Finset.univ (fun i _ => hInt_each i)
      | simpa using MeasureTheory.integrable_finset_sum Finset.univ (fun i _ => hInt_each i)
  have hInt_abs_sum : Integrable (fun x : ℝ => ∑ i : Fin n, |K ((x - a i) / h)|) := by
    first
      | exact MeasureTheory.integrable_finset_sum Finset.univ (fun i _ => hInt_abs_i i)
      | simpa using MeasureTheory.integrable_finset_sum Finset.univ (fun i _ => hInt_abs_i i)
  have hsum_int : ∫ x, ∑ i : Fin n, |K ((x - a i) / h)| = (n : ℝ) * h := by
    have h1 : ∫ x, ∑ i : Fin n, |K ((x - a i) / h)| = ∑ i : Fin n, ∫ x, |K ((x - a i) / h)| := by
      first
        | exact MeasureTheory.integral_finset_sum Finset.univ (fun i _ => hInt_abs_i i)
        | simpa using MeasureTheory.integral_finset_sum Finset.univ (fun i _ => hInt_abs_i i)
    rw [h1]
    simp only [hsub]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hbound : ∫ x, |∑ i : Fin n, K ((x - a i) / h)| ≤ (n : ℝ) * h := by
    have hpt : ∀ x : ℝ, |∑ i : Fin n, K ((x - a i) / h)| ≤ ∑ i : Fin n, |K ((x - a i) / h)| := by
      intro x
      have h₁ : ∑ i : Fin n, K ((x - a i) / h) ≤ ∑ i : Fin n, |K ((x - a i) / h)| :=
        Finset.sum_le_sum (fun i _ => le_abs_self (K ((x - a i) / h)))
      have h₂ : -(∑ i : Fin n, K ((x - a i) / h)) ≤ ∑ i : Fin n, |K ((x - a i) / h)| := by
        have h₃ := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => neg_le_abs (K ((x - a i) / h)))
        simpa [Finset.sum_neg_distrib] using h₃
      exact abs_le.mpr ⟨by linarith, h₁⟩
    have hle : ∫ x, |∑ i : Fin n, K ((x - a i) / h)|
        ≤ ∫ x, ∑ i : Fin n, |K ((x - a i) / h)| := by
      first
        | exact MeasureTheory.integral_mono hInt_sum.abs hInt_abs_sum hpt
        | exact MeasureTheory.integral_mono hpt
        | exact MeasureTheory.integral_mono hpt hInt_sum.abs hInt_abs_sum
        | exact MeasureTheory.integral_mono hInt_abs_sum hInt_sum.abs hpt
    rw [hsum_int] at hle
    exact hle
  refine ⟨?_, ?_⟩
  · first
      | simpa [smul_eq_mul] using hInt_sum.const_mul ((n : ℝ) * h)⁻¹
      | simpa [mul_comm] using hInt_sum.mul_const ((n : ℝ) * h)⁻¹
  · have hfun : ∀ x : ℝ, |((n : ℝ) * h)⁻¹ * ∑ i : Fin n, K ((x - a i) / h)|
        = ((n : ℝ) * h)⁻¹ * |∑ i : Fin n, K ((x - a i) / h)| := by
      intro x
      rw [abs_mul, abs_of_pos hcpos]
    have heq : ∫ x, |((n : ℝ) * h)⁻¹ * ∑ i : Fin n, K ((x - a i) / h)|
        = ((n : ℝ) * h)⁻¹ * ∫ x, |∑ i : Fin n, K ((x - a i) / h)| := by
      simp only [hfun]
      first
        | exact MeasureTheory.integral_const_mul _ _
        | simpa [smul_eq_mul] using
            MeasureTheory.integral_const_mul ((n : ℝ) * h)⁻¹
              (fun x => |∑ i : Fin n, K ((x - a i) / h)|)
    rw [heq]
    calc ((n : ℝ) * h)⁻¹ * ∫ x, |∑ i : Fin n, K ((x - a i) / h)|
        ≤ ((n : ℝ) * h)⁻¹ * ((n : ℝ) * h) := mul_le_mul_of_nonneg_left hbound (le_of_lt hcpos)
      _ = 1 := inv_mul_cancel₀ hnhne
  /- @proof-region region.target-node.session.a44a4e604cd3c12c end -/
