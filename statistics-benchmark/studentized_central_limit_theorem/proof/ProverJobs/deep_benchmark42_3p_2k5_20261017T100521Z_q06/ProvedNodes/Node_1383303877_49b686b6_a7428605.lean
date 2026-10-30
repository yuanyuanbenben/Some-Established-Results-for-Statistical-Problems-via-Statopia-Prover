import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q06.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q06.Base

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

set_option autoImplicit false in
theorem statopia_math_node_1383303877_49b686b6 : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (mean sigma : ℝ)
    (hX_meas : ∀ i : ℕ, Measurable (X i))
    (hX_ident : ∀ i : ℕ, IdentDistrib (X i) (X 0) P P)
    (hX_memLp : ∀ i : ℕ, MemLp (X i) 2 P)
    (hX_mean : ∀ i : ℕ, ∫ ω, X i ω ∂P = mean)
    (hX_sq : ∀ i : ℕ, ∫ ω, (X i ω) ^ 2 ∂P = mean ^ 2 + sigma ^ 2)
    (hsigma : 0 < sigma),
    ∀ ε : ℝ, 0 < ε →
      Tendsto
        (fun n : ℕ =>
          Statlib.StatFoundation.Convergence.LindebergFeller.LindebergSum P
            (fun (j : Fin (n + 1)) (ω : Ω) => X (j : ℕ) ω - mean)
            (sigma * Real.sqrt ((n : ℝ) + 1)) ε)
        atTop (𝓝 0) := by
  /- @proof-region region.target-node.session.389805762d205d46 begin -/
  intro Ω _ P _ X mean sigma hX_meas hX_ident hX_memLp hX_mean hX_sq hsigma ε hε
  unfold Statlib.StatFoundation.Convergence.LindebergFeller.LindebergSum
  let Y : ℕ → Ω → ℝ := fun i ω => X i ω - mean
  let s : ℕ → ℝ := fun n => sigma * Real.sqrt ((n : ℝ) + 1)
  let a : ℕ → ℝ := fun n => ε * s n
  change Tendsto (fun n => 1 / (s n)^2 * ∑ j : Fin (n+1), ∫ ω in {ω : Ω | a n < |Y (j:ℕ) ω|}, (Y (j:ℕ) ω)^2 ∂P) atTop (𝓝 0)
  let g : ℕ → ℝ → ℝ := fun n x => x^2 * Set.indicator {y : ℝ | a n < |y|} (fun _ => (1:ℝ)) x
  let c : ℕ → ℝ := fun n => ∫ ω, g n (Y 0 ω) ∂P
  have hY_ident : ∀ i : ℕ, IdentDistrib (Y i) (Y 0) P P := fun i => (hX_ident i).comp (measurable_id.sub measurable_const)
  have hg_meas : ∀ n, Measurable (g n) := by
    intro n
    show Measurable (fun x : ℝ => x ^ 2 * Set.indicator {y : ℝ | a n < |y|} (fun _ => (1:ℝ)) x)
    have hs : MeasurableSet {y : ℝ | a n < |y|} := by measurability
    exact (Measurable.pow_const measurable_id 2).mul (Measurable.indicator measurable_const hs)
  have hterm : ∀ (n : ℕ) (j : Fin (n+1)), (∫ ω in {ω : Ω | a n < |Y (j:ℕ) ω|}, (Y (j:ℕ) ω)^2 ∂P) = c n := by
    intro n j
    have hYmeas : Measurable (Y (j:ℕ)) := (hX_meas (j:ℕ)).sub measurable_const
    have hconv : (∫ ω in {ω : Ω | a n < |Y (j:ℕ) ω|}, (Y (j:ℕ) ω)^2 ∂P) = ∫ ω, g n (Y (j:ℕ) ω) ∂P := by
      have hs : MeasurableSet {ω : Ω | a n < |Y (j:ℕ) ω|} := by measurability
      rw [← MeasureTheory.integral_indicator hs]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with ω
      simp only [g, Set.indicator, Set.mem_setOf_eq]
      by_cases h : a n < |Y (j:ℕ) ω| <;> simp [h]
    rw [hconv]
    have h2 : ∫ ω, g n (Y (j:ℕ) ω) ∂P = ∫ ω, g n (Y 0 ω) ∂P := by
      have hbase := ((hY_ident (j:ℕ)).comp (hg_meas n)).integral_eq
      simpa only [Function.comp_apply] using hbase
    rw [h2]
  have hc_lim : Tendsto c atTop (𝓝 0) := by
    have hY0_meas : Measurable (Y 0) := (hX_meas 0).sub measurable_const
    have hInt : Integrable (fun ω => (Y 0 ω)^2) P :=
      MeasureTheory.MemLp.integrable_sq (MeasureTheory.MemLp.sub (hX_memLp 0) (memLp_const mean))
    have hlim_pt : ∀ A : ℝ, Tendsto (fun n : ℕ => g n A) atTop (𝓝 0) := by
      intro A
      have h1 : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
      have hεσ : 0 < ε * sigma := mul_pos hε hsigma
      have hc : ∀ᶠ n : ℕ in atTop, |A| ≤ a n := by
        have hsqrt : ∀ᶠ n : ℕ in atTop, |A| / (ε * sigma) ≤ Real.sqrt ((n:ℝ)) :=
          h1.eventually (Real.tendsto_sqrt_atTop.eventually_ge_atTop (|A| / (ε * sigma)))
        filter_upwards [hsqrt] with n hn
        have hle : Real.sqrt ((n:ℝ)) ≤ Real.sqrt ((n:ℝ) + 1) :=
          Real.sqrt_le_sqrt (by linarith)
        have hmul : (ε * sigma) * (|A| / (ε * sigma)) ≤ (ε * sigma) * Real.sqrt ((n:ℝ) + 1) :=
          mul_le_mul_of_nonneg_left (le_trans hn hle) (le_of_lt hεσ)
        have hcancel : (ε * sigma) * (|A| / (ε * sigma)) = |A| := by
          field_simp
        rw [hcancel] at hmul
        simpa only [a, s, mul_assoc] using hmul
      have hge : (fun n : ℕ => g n A) =ᶠ[atTop] (fun _ => (0:ℝ)) := by
        filter_upwards [hc] with n hn
        have hmem : A ∉ {y : ℝ | a n < |y|} := by
          simp only [Set.mem_setOf_eq]; linarith
        rw [show g n A = A^2 * Set.indicator {y : ℝ | a n < |y|} (fun _ => (1:ℝ)) A from rfl,
            Set.indicator, if_neg hmem, mul_zero]
      exact Filter.Tendsto.congr' hge.symm tendsto_const_nhds
    have hbound : ∀ n, ∀ᵐ A ∂P, ‖g n (Y 0 A)‖ ≤ (Y 0 A)^2 := by
      intro n
      filter_upwards with ω
      by_cases h : a n < |Y 0 ω|
      · have hg : g n (Y 0 ω) = (Y 0 ω)^2 := by
          simp [g, Set.indicator, Set.mem_setOf_eq, h]
        rw [hg, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      · have hg : g n (Y 0 ω) = 0 := by
          simp [g, Set.indicator, Set.mem_setOf_eq, h]
        rw [hg, norm_zero]
        positivity
    have key := MeasureTheory.tendsto_integral_of_dominated_convergence
      (F := fun n ω => g n (Y 0 ω)) (f := fun _ => (0:ℝ)) (bound := fun ω => (Y 0 ω)^2)
      (fun n => ((hg_meas n).comp hY0_meas).aestronglyMeasurable)
      hInt hbound (by filter_upwards with ω; exact hlim_pt (Y 0 ω))
    simpa using key
  have hsum : ∀ n, (∑ j : Fin (n+1), (∫ ω in {ω : Ω | a n < |Y (j:ℕ) ω|}, (Y (j:ℕ) ω)^2 ∂P)) = (n+1 : ℝ) * c n := by
    intro n
    rw [Finset.sum_congr rfl (fun j _ => hterm n j), Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    simp only [Nat.cast_add, Nat.cast_one]
  have halg : ∀ n : ℕ, 1 / (s n)^2 * ((n+1 : ℝ) * c n) = (1/sigma^2) * c n := by
    intro n
    have hsq : (s n)^2 = sigma^2 * ((n:ℝ)+1) := by
      show (sigma * Real.sqrt ((n:ℝ)+1))^2 = sigma^2 * ((n:ℝ)+1)
      rw [mul_pow, Real.sq_sqrt (by positivity)]
    rw [hsq]
    push_cast
    field_simp
  have hfinal : Tendsto (fun n => 1 / (s n)^2 * (∑ j : Fin (n+1), (∫ ω in {ω : Ω | a n < |Y (j:ℕ) ω|}, (Y (j:ℕ) ω)^2 ∂P))) atTop (𝓝 0) := by
    have h1 : (fun n => 1 / (s n)^2 * (∑ j : Fin (n+1), (∫ ω in {ω : Ω | a n < |Y (j:ℕ) ω|}, (Y (j:ℕ) ω)^2 ∂P))) = (fun n => 1 / (s n)^2 * ((n+1 : ℝ) * c n)) := by
      funext n; rw [hsum n]
    rw [h1]
    have h2 : (fun n => 1 / (s n)^2 * ((n+1 : ℝ) * c n)) = (fun n => (1/sigma^2) * c n) := by
      funext n; exact halg n
    rw [h2]
    have h3 := hc_lim.const_mul (1/sigma^2)
    simpa using h3
  exact hfinal
  /- @proof-region region.target-node.session.389805762d205d46 end -/
