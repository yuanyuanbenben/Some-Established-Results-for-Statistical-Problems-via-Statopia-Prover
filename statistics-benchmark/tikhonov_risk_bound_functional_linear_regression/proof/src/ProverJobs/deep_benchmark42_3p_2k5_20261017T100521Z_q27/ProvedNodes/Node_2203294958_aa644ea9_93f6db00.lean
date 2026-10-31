import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q27.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q27.Base

open MeasureTheory

open MeasureTheory

set_option autoImplicit false in
theorem statopia_math_node_2203294958_aa644ea9 : ∀ {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [SecondCountableTopology H]
    (P : Measure Ω)
    (X : Ω → H) (Y : Ω → ℝ)
    (hXmeas : StronglyMeasurable X)
    (hYmeas : StronglyMeasurable Y)
    (hXsq : Integrable (fun ω ↦ ‖X ω‖ ^ 2) P)
    (hYsq : Integrable (fun ω ↦ (Y ω) ^ 2) P)
    (u w : H),
    Integrable (fun ω ↦ (Y ω) • X ω) P ∧
      Integrable (fun ω ↦ (inner ℝ (X ω) u) • X ω) P ∧
      Integrable (fun ω ↦ Y ω * inner ℝ (X ω) w) P ∧
      Integrable (fun ω ↦ (inner ℝ (X ω) u) * (inner ℝ (X ω) w)) P ∧
      Integrable (fun ω ↦ (Y ω - inner ℝ (X ω) u) ^ 2) P := by
  /- @proof-region region.target-node.session.c2e507b138f220ad begin -/
  intro Ω H _ _ _ _ _ P X Y hXmeas hYmeas hXsq hYsq u w
  have h1 : Integrable (fun ω => Y ω • X ω) P := by
    have hg : Integrable (fun ω => (1 / 2 : ℝ) * (Y ω) ^ 2 + (1 / 2 : ℝ) * ‖X ω‖ ^ 2) P :=
      (hYsq.const_mul (1 / 2 : ℝ)).add (hXsq.const_mul (1 / 2 : ℝ))
    refine hg.mono' ?_ ?_
    · measurability
    · filter_upwards with ω
      rw [norm_smul, Real.norm_eq_abs (Y ω)]
      nlinarith [sq_nonneg (|Y ω| - ‖X ω‖), sq_abs (Y ω)]
  have h2 : Integrable (fun ω => inner ℝ (X ω) u • X ω) P := by
    have hg : Integrable (fun ω => ‖u‖ * ‖X ω‖ ^ 2) P := hXsq.const_mul ‖u‖
    refine hg.mono' ?_ ?_
    · measurability
    · filter_upwards with ω
      rw [norm_smul, Real.norm_eq_abs (inner ℝ (X ω) u)]
      have hu : |inner ℝ (X ω) u| ≤ ‖X ω‖ * ‖u‖ := abs_real_inner_le_norm (X ω) u
      have hprod : |inner ℝ (X ω) u| * ‖X ω‖ ≤ (‖X ω‖ * ‖u‖) * ‖X ω‖ :=
        mul_le_mul_of_nonneg_right hu (norm_nonneg _)
      nlinarith [hprod]
  have h3 : Integrable (fun ω => Y ω * inner ℝ (X ω) w) P := by
    have hg : Integrable
        (fun ω => (1 / 2 : ℝ) * (Y ω) ^ 2 + (1 / 2 : ℝ) * (‖w‖ ^ 2 * ‖X ω‖ ^ 2)) P :=
      (hYsq.const_mul (1 / 2 : ℝ)).add ((hXsq.const_mul (‖w‖ ^ 2)).const_mul (1 / 2 : ℝ))
    refine hg.mono' ?_ ?_
    · measurability
    · filter_upwards with ω
      rw [norm_mul, Real.norm_eq_abs (Y ω), Real.norm_eq_abs (inner ℝ (X ω) w)]
      have hw : |inner ℝ (X ω) w| ≤ ‖X ω‖ * ‖w‖ := abs_real_inner_le_norm (X ω) w
      have hprod : |Y ω| * |inner ℝ (X ω) w| ≤ |Y ω| * (‖X ω‖ * ‖w‖) :=
        mul_le_mul_of_nonneg_left hw (abs_nonneg _)
      nlinarith [hprod, sq_nonneg (|Y ω| - ‖X ω‖ * ‖w‖), sq_abs (Y ω)]
  have h4 : Integrable (fun ω => inner ℝ (X ω) u * inner ℝ (X ω) w) P := by
    have hg : Integrable (fun ω => ‖u‖ * ‖w‖ * ‖X ω‖ ^ 2) P := hXsq.const_mul (‖u‖ * ‖w‖)
    refine hg.mono' ?_ ?_
    · measurability
    · filter_upwards with ω
      rw [norm_mul, Real.norm_eq_abs (inner ℝ (X ω) u), Real.norm_eq_abs (inner ℝ (X ω) w)]
      have hu : |inner ℝ (X ω) u| ≤ ‖X ω‖ * ‖u‖ := abs_real_inner_le_norm (X ω) u
      have hw : |inner ℝ (X ω) w| ≤ ‖X ω‖ * ‖w‖ := abs_real_inner_le_norm (X ω) w
      have hX0 : (0 : ℝ) ≤ ‖X ω‖ := norm_nonneg _
      calc |inner ℝ (X ω) u| * |inner ℝ (X ω) w|
          ≤ (‖X ω‖ * ‖u‖) * (‖X ω‖ * ‖w‖) :=
            mul_le_mul hu hw (abs_nonneg _) (mul_nonneg hX0 (norm_nonneg u))
        _ = ‖u‖ * ‖w‖ * ‖X ω‖ ^ 2 := by ring
  have h5 : Integrable (fun ω => (Y ω - inner ℝ (X ω) u) ^ 2) P := by
    have hg : Integrable (fun ω => 2 * (Y ω) ^ 2 + 2 * (‖u‖ ^ 2 * ‖X ω‖ ^ 2)) P :=
      (hYsq.const_mul 2).add ((hXsq.const_mul (‖u‖ ^ 2)).const_mul 2)
    refine hg.mono' ?_ ?_
    · measurability
    · filter_upwards with ω
      rw [Real.norm_eq_abs ((Y ω - inner ℝ (X ω) u) ^ 2),
        abs_of_nonneg (sq_nonneg (Y ω - inner ℝ (X ω) u))]
      have hu : |inner ℝ (X ω) u| ≤ ‖X ω‖ * ‖u‖ := abs_real_inner_le_norm (X ω) u
      have hstep : (Y ω - inner ℝ (X ω) u) ^ 2 ≤ (|Y ω| + ‖X ω‖ * ‖u‖) ^ 2 := by
        have h1' : |Y ω - inner ℝ (X ω) u| ≤ |Y ω| + ‖X ω‖ * ‖u‖ := by
          have habs : |Y ω + -(inner ℝ (X ω) u)| ≤ |Y ω| + |-(inner ℝ (X ω) u)| :=
            abs_add_le _ _
          rw [abs_neg] at habs
          rw [sub_eq_add_neg]
          linarith [habs, hu]
        calc (Y ω - inner ℝ (X ω) u) ^ 2 = (|Y ω - inner ℝ (X ω) u|) ^ 2 := (sq_abs _).symm
          _ ≤ (|Y ω| + ‖X ω‖ * ‖u‖) ^ 2 := by
              simpa [pow_two]
                using mul_self_le_mul_self (abs_nonneg (Y ω - inner ℝ (X ω) u)) h1'
      have hb : (‖X ω‖ * ‖u‖) ^ 2 = ‖u‖ ^ 2 * ‖X ω‖ ^ 2 := by ring
      have hcross : 2 * |Y ω| * (‖X ω‖ * ‖u‖) ≤ |Y ω| ^ 2 + (‖X ω‖ * ‖u‖) ^ 2 := by
        nlinarith [sq_nonneg (|Y ω| - ‖X ω‖ * ‖u‖)]
      have hexp : (|Y ω| + ‖X ω‖ * ‖u‖) ^ 2
          = |Y ω| ^ 2 + 2 * |Y ω| * (‖X ω‖ * ‖u‖) + (‖X ω‖ * ‖u‖) ^ 2 := by ring
      nlinarith [hstep, hb, hcross, hexp, sq_abs (Y ω)]
  exact ⟨h1, h2, h3, h4, h5⟩
  /- @proof-region region.target-node.session.c2e507b138f220ad end -/
