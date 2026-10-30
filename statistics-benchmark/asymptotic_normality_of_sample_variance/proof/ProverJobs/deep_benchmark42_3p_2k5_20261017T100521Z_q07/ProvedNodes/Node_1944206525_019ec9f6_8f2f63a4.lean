import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q07.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q07.Base

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

set_option autoImplicit false in
theorem statopia_math_node_1944206525_019ec9f6 : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (m sigma2 : ℝ)
    (hY_meas : ∀ i : ℕ, Measurable (Y i))
    (hY_ident : ∀ i : ℕ, IdentDistrib (Y i) (Y 0) P P)
    (hY_memLp : MemLp (Y 0) 2 P)
    (hY_mean : ∀ i : ℕ, ∫ ω, Y i ω ∂P = m)
    (hsigma2_pos : 0 < sigma2)
    (hY_var : ∫ ω, (Y 0 ω) ^ 2 ∂P - m ^ 2 = sigma2),
    ∀ ε > 0, Filter.Tendsto
      (fun n : ℕ =>
        Statlib.StatFoundation.Convergence.LindebergFeller.LindebergSum P
          (fun j : Fin (n + 1) => fun ω => (Y (j : ℕ) ω - m) / Real.sqrt sigma2)
          (Real.sqrt ((n : ℝ) + 1)) ε)
      Filter.atTop (nhds 0) := by
  /- @proof-region region.target-node.session.75364be0601ba0de begin -/
  intro Ω mΩ P hP Y m sigma2 hY_meas hY_ident hY_memLp hY_mean hsigma2_pos hY_var ε hε
  set σ : ℝ := Real.sqrt sigma2 with hσ_def
  have hσ_pos : 0 < σ := by
    rw [hσ_def]
    exact Real.sqrt_pos.2 hsigma2_pos
  have hsqrt_sq : ∀ n : ℕ, Real.sqrt ((n : ℝ) + 1) ^ 2 = (n : ℝ) + 1 := by
    intro n
    exact Real.sq_sqrt (by positivity)
  have hZ_meas : ∀ j : ℕ, Measurable (fun ω : Ω => (Y j ω - m) / σ) := by
    intro j
    exact ((hY_meas j).sub_const m).div_const σ
  have htrunc : ∀ (j : ℕ) (t : ℝ),
      (∫ ω in {ω : Ω | t < |(Y j ω - m) / σ|}, ((Y j ω - m) / σ) ^ 2 ∂P)
        = ∫ ω, (if t < |(Y 0 ω - m) / σ| then ((Y 0 ω - m) / σ) ^ 2 else 0) ∂P := by
    intro j t
    have hψ : Measurable (fun y : ℝ => (y - m) / σ) := (measurable_id.sub_const m).div_const σ
    have hmap : Measure.map (fun ω : Ω => (Y j ω - m) / σ) P
        = Measure.map (fun ω : Ω => (Y 0 ω - m) / σ) P := by
      have e1 : Measure.map (fun ω : Ω => (Y j ω - m) / σ) P
          = Measure.map (fun y : ℝ => (y - m) / σ) (Measure.map (Y j) P) :=
        (Measure.map_map hψ (hY_meas j)).symm
      have e2 : Measure.map (fun y : ℝ => (y - m) / σ) (Measure.map (Y j) P)
          = Measure.map (fun y : ℝ => (y - m) / σ) (Measure.map (Y 0) P) := by
        rw [(hY_ident j).map_eq]
      have e3 : Measure.map (fun y : ℝ => (y - m) / σ) (Measure.map (Y 0) P)
          = Measure.map (fun ω : Ω => (Y 0 ω - m) / σ) P :=
        Measure.map_map hψ (hY_meas 0)
      rw [e1, e2, e3]
    have hsetj : MeasurableSet {ω : Ω | t < |(Y j ω - m) / σ|} :=
      measurableSet_lt measurable_const (hZ_meas j).abs
    have hφ_meas : Measurable (fun y : ℝ => if t < |y| then y ^ 2 else 0) := by
      have hsq : Measurable (fun y : ℝ => y ^ 2) := by
        simpa [pow_two] using (measurable_id.mul measurable_id : Measurable fun y : ℝ => y * y)
      exact Measurable.ite (measurableSet_lt measurable_const measurable_id.abs) hsq measurable_const
    calc (∫ ω in {ω : Ω | t < |(Y j ω - m) / σ|}, ((Y j ω - m) / σ) ^ 2 ∂P)
        = ∫ ω, (if t < |(Y j ω - m) / σ| then ((Y j ω - m) / σ) ^ 2 else 0) ∂P := by
          rw [← MeasureTheory.integral_indicator hsetj]
          simp only [Set.indicator, Set.mem_setOf_eq]
      _ = ∫ y, (if t < |y| then y ^ 2 else 0) ∂Measure.map (fun ω : Ω => (Y j ω - m) / σ) P :=
          (MeasureTheory.integral_map (φ := fun ω : Ω => (Y j ω - m) / σ)
            (f := fun y : ℝ => if t < |y| then y ^ 2 else 0) (hZ_meas j).aemeasurable
            hφ_meas.aestronglyMeasurable).symm
      _ = ∫ y, (if t < |y| then y ^ 2 else 0) ∂Measure.map (fun ω : Ω => (Y 0 ω - m) / σ) P := by
          rw [hmap]
      _ = ∫ ω, (if t < |(Y 0 ω - m) / σ| then ((Y 0 ω - m) / σ) ^ 2 else 0) ∂P :=
          MeasureTheory.integral_map (φ := fun ω : Ω => (Y 0 ω - m) / σ)
            (f := fun y : ℝ => if t < |y| then y ^ 2 else 0) (hZ_meas 0).aemeasurable
            hφ_meas.aestronglyMeasurable
  have hmain : ∀ n : ℕ,
      Statlib.StatFoundation.Convergence.LindebergFeller.LindebergSum P
        (fun j : Fin (n + 1) => fun ω => (Y (j : ℕ) ω - m) / σ)
        (Real.sqrt ((n : ℝ) + 1)) ε
      = ∫ ω, (if ε * Real.sqrt ((n : ℝ) + 1) < |(Y 0 ω - m) / σ| then ((Y 0 ω - m) / σ) ^ 2 else 0) ∂P := by
    intro n
    have hsc : (∑ j : Fin (n + 1),
        ∫ ω, (if ε * Real.sqrt ((n : ℝ) + 1) < |(Y 0 ω - m) / σ| then ((Y 0 ω - m) / σ) ^ 2 else 0) ∂P)
        = ((n : ℝ) + 1) * ∫ ω, (if ε * Real.sqrt ((n : ℝ) + 1) < |(Y 0 ω - m) / σ| then ((Y 0 ω - m) / σ) ^ 2 else 0) ∂P := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
    unfold Statlib.StatFoundation.Convergence.LindebergFeller.LindebergSum
    rw [Finset.sum_congr rfl
      (fun (j : Fin (n + 1)) _ => htrunc (j : ℕ) (ε * Real.sqrt ((n : ℝ) + 1))), hsc]
    rw [hsqrt_sq n]
    have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
    rw [one_div, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  have hsqrt_eventually : ∀ C : ℝ, ∀ᶠ n : ℕ in atTop, C < Real.sqrt ((n : ℝ) + 1) := by
    intro C
    obtain ⟨N, hN⟩ := exists_nat_gt ((max C 0 + 1) ^ 2)
    refine Filter.eventually_atTop.2 ⟨N, fun n hn => ?_⟩
    have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h1 : (max C 0 + 1) ^ 2 < (n : ℝ) + 1 := by linarith
    have h2 : max C 0 + 1 < Real.sqrt ((n : ℝ) + 1) := by
      rw [Real.lt_sqrt (by positivity)]
      exact h1
    have h3 : C ≤ max C 0 := le_max_left C 0
    linarith
  have hpoint : ∀ ω : Ω, ∀ᶠ n : ℕ in atTop, ¬ (ε * Real.sqrt ((n : ℝ) + 1) < |(Y 0 ω - m) / σ|) := by
    intro ω
    filter_upwards [hsqrt_eventually (|(Y 0 ω - m) / σ| / ε)] with n hn
    intro hcon
    have h2 : |(Y 0 ω - m) / σ| < Real.sqrt ((n : ℝ) + 1) * ε := (div_lt_iff₀ hε).1 hn
    rw [mul_comm ε (Real.sqrt ((n : ℝ) + 1))] at hcon
    linarith
  have hsq_meas : Measurable (fun ω : Ω => ((Y 0 ω - m) / σ) ^ 2) := by
    simpa [pow_two] using (hZ_meas 0).mul (hZ_meas 0)
  have hF_meas : ∀ n : ℕ, AEStronglyMeasurable
      (fun ω : Ω => if ε * Real.sqrt ((n : ℝ) + 1) < |(Y 0 ω - m) / σ|
        then ((Y 0 ω - m) / σ) ^ 2 else 0) P := by
    intro n
    exact (Measurable.ite (measurableSet_lt measurable_const (hZ_meas 0).abs) hsq_meas
      measurable_const).aestronglyMeasurable
  have hint_sq : Integrable (fun ω : Ω => (Y 0 ω - m) ^ 2) P := by
    have hmem : MemLp (fun ω : Ω => Y 0 ω - m) 2 P := hY_memLp.sub (memLp_const m)
    exact hmem.integrable_sq
  have hbound_int : Integrable (fun ω : Ω => ((Y 0 ω - m) / σ) ^ 2) P := by
    have h1 : Integrable (fun ω : Ω => (Y 0 ω - m) ^ 2 / σ ^ 2) P := hint_sq.div_const (σ ^ 2)
    simpa only [div_pow] using h1
  have hF_bound : ∀ n : ℕ, ∀ᵐ ω ∂P,
      ‖(if ε * Real.sqrt ((n : ℝ) + 1) < |(Y 0 ω - m) / σ|
        then ((Y 0 ω - m) / σ) ^ 2 else 0)‖ ≤ ((Y 0 ω - m) / σ) ^ 2 := by
    intro n
    exact Filter.Eventually.of_forall (fun ω => by
      by_cases h : (ε * Real.sqrt ((n : ℝ) + 1) < |(Y 0 ω - m) / σ|)
      · rw [if_pos h, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ((Y 0 ω - m) / σ))]
      · rw [if_neg h, norm_zero]
        exact sq_nonneg _)
  have hF_lim : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ =>
      (if ε * Real.sqrt ((n : ℝ) + 1) < |(Y 0 ω - m) / σ|
        then ((Y 0 ω - m) / σ) ^ 2 else 0)) atTop (nhds 0) := by
    refine Filter.Eventually.of_forall (fun ω => ?_)
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [hpoint ω] with n hn
    rw [if_neg hn]
  have hDC : Tendsto (fun n : ℕ => ∫ ω, (if ε * Real.sqrt ((n : ℝ) + 1) < |(Y 0 ω - m) / σ|
      then ((Y 0 ω - m) / σ) ^ 2 else 0) ∂P) atTop (nhds 0) := by
    have h := MeasureTheory.tendsto_integral_of_dominated_convergence (μ := P)
      (F := fun (n : ℕ) (ω : Ω) => if ε * Real.sqrt ((n : ℝ) + 1) < |(Y 0 ω - m) / σ|
        then ((Y 0 ω - m) / σ) ^ 2 else 0)
      (f := fun ω : Ω => 0) (fun ω : Ω => ((Y 0 ω - m) / σ) ^ 2)
      hF_meas hbound_int hF_bound hF_lim
    simpa using h
  have hfun : (fun n : ℕ => Statlib.StatFoundation.Convergence.LindebergFeller.LindebergSum P
        (fun j : Fin (n + 1) => fun ω => (Y (j : ℕ) ω - m) / σ)
        (Real.sqrt ((n : ℝ) + 1)) ε)
      = fun n : ℕ => ∫ ω, (if ε * Real.sqrt ((n : ℝ) + 1) < |(Y 0 ω - m) / σ|
          then ((Y 0 ω - m) / σ) ^ 2 else 0) ∂P := funext hmain
  rw [hfun]
  exact hDC
  /- @proof-region region.target-node.session.75364be0601ba0de end -/
