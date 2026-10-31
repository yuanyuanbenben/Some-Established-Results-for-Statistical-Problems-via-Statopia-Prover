import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q06.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q06.ProvedNodes
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q06.Base

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

theorem studentized_central_limit_theorem
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ)
    (mean sigma : ℝ)
    (G : Ω → ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X P)
    (hX_ident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hmean : ∫ ω, X 0 ω ∂P = mean)
    (hvar : variance (X 0) P = sigma ^ 2)
    (hsigma : 0 < sigma)
    (hG_meas : Measurable G)
    (hG_law : IdentDistrib G id P (gaussianReal 0 1)) :
    let Xbar : ℕ → Ω → ℝ :=
      fun n ω ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, X i ω
    let S : ℕ → Ω → ℝ :=
      fun n ω ↦
        Real.sqrt
          ((n : ℝ)⁻¹ *
            ∑ i ∈ Finset.range n, (X i ω - Xbar n ω) ^ 2)
    let T : ℕ → Ω → ℝ :=
      fun n ω ↦
        if 0 < S n ω then
          Real.sqrt (n : ℝ) * (Xbar n ω - mean) / S n ω
        else 0
    TendstoInDistribution T atTop G P
:= by
  /- @proof-region region.root.e309b167dce5 begin -/
  let Xbar : ℕ → Ω → ℝ := fun n ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, X i ω
  let V : ℕ → Ω → ℝ := fun n ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, (X i ω - Xbar n ω) ^ 2
  let S : ℕ → Ω → ℝ := fun n ω => Real.sqrt (V n ω)
  let T : ℕ → Ω → ℝ := fun n ω => if 0 < S n ω then Real.sqrt (n : ℝ) * (Xbar n ω - mean) / S n ω else 0
  let U : ℕ → Ω → ℝ := fun n ω => Real.sqrt (n : ℝ) * (Xbar n ω - mean) / sigma
  let W : ℕ → Ω → ℝ := fun n ω => S n ω / sigma
  let Q : ℕ → Ω → ℝ := fun n ω => if 0 < W n ω then U n ω / W n ω else 0
  change TendstoInDistribution T atTop G P
  obtain ⟨hX_memLp, hX_mean, hX_sq, hX0_int, hX0_sq_int⟩ :=
    statopia_math_node_980666557_257fc9e4 P X mean sigma hX_meas hX_ident hmean hvar hsigma
  have hXbar_meas : ∀ n, Measurable (Xbar n) := by
    intro n
    have hsum : Measurable (fun ω => ∑ i ∈ Finset.range n, X i ω) := by
      induction (Finset.range n) using Finset.induction with
      | empty => simpa using measurable_const
      | insert a s ha ih => simpa [Finset.sum_insert, ha] using (hX_meas a).add ih
    simpa only [Xbar] using hsum.const_mul ((n : ℝ)⁻¹)
  have hV_meas : ∀ n, Measurable (V n) := by
    intro n
    have hsum : Measurable (fun ω => ∑ i ∈ Finset.range n, (X i ω - Xbar n ω) ^ 2) := by
      induction (Finset.range n) using Finset.induction with
      | empty => simpa using measurable_const
      | insert a s ha ih =>
          have hsub : Measurable (fun ω => X a ω - Xbar n ω) := (hX_meas a).sub (hXbar_meas n)
          have hterm : Measurable (fun ω => (X a ω - Xbar n ω) ^ 2) := by
            simpa only [pow_two] using hsub.mul hsub
          simpa [Finset.sum_insert, ha] using hterm.add ih
    simpa only [V] using hsum.const_mul ((n : ℝ)⁻¹)
  have hS_meas : ∀ n, Measurable (S n) := by
    intro n
    exact Real.continuous_sqrt.measurable.comp (hV_meas n)
  have hU_meas : ∀ n, Measurable (U n) := by
    intro n
    have hconst : Measurable (fun _ : Ω => mean) := measurable_const
    have h1 : Measurable (fun ω => Real.sqrt (n : ℝ) * (Xbar n ω - mean)) :=
      (measurable_const : Measurable fun _ : Ω => Real.sqrt (n : ℝ)).mul ((hXbar_meas n).sub hconst)
    have h2 : Measurable (fun ω => Real.sqrt (n : ℝ) * (Xbar n ω - mean) * sigma⁻¹) := h1.mul_const _
    simpa only [U, div_eq_mul_inv] using h2
  have hW_meas : ∀ n, Measurable (W n) := by
    intro n
    have h1 : Measurable (fun ω => S n ω * sigma⁻¹) := (hS_meas n).mul_const _
    simpa only [W, div_eq_mul_inv] using h1
  have hXbar_memLp : ∀ n, MemLp (Xbar n) 2 P := by
    intro n
    have hsum : MemLp (fun ω => ∑ i ∈ Finset.range n, X i ω) 2 P :=
      memLp_finset_sum (Finset.range n) (fun i _ => hX_memLp i)
    simpa only [Xbar] using hsum.const_mul ((n : ℝ)⁻¹)
  have hU_mem : ∀ n, 1 ≤ n → MemLp (U n) 2 P := by
    intro n _
    have h1 : MemLp (fun ω => Xbar n ω - mean) 2 P :=
      (hXbar_memLp n).sub (memLp_const mean)
    have h2 : MemLp (fun ω => (Real.sqrt (n : ℝ) / sigma) * (Xbar n ω - mean)) 2 P :=
      h1.const_mul (Real.sqrt (n : ℝ) / sigma)
    have hfun : U n = fun ω => (Real.sqrt (n : ℝ) / sigma) * (Xbar n ω - mean) := by
      funext ω
      simp only [U]
      field_simp [ne_of_gt hsigma]
    rwa [hfun]
  obtain ⟨hU_second_eq_raw, _⟩ :=
    statopia_math_node_1690793443_44c42ea2 P X mean sigma hX_meas hX_indep hX_ident hmean hvar hsigma hX_memLp hX_mean hX_sq
  have hU_second : ∀ n, 1 ≤ n → ∫ ω, (U n ω) ^ 2 ∂P ≤ 1 := by
    intro n hn
    have h := hU_second_eq_raw n (lt_of_lt_of_le zero_lt_one hn)
    simpa only [Xbar, U] using le_of_eq h
  obtain ⟨_, _, hW_conv_raw, _⟩ :=
    statopia_math_node_3827306998_2acd3346 P X mean sigma hX_meas hX_indep hX_ident hmean hvar hsigma hX_memLp hX_mean hX_sq hX0_int hX0_sq_int
  have hW_conv : TendstoInMeasure P W atTop (fun _ => (1 : ℝ)) := by
    simpa only [Xbar, V, S, W] using hW_conv_raw
  have hW_prob : ∀ eps : ℝ, 0 < eps →
      Tendsto (fun n => P {ω | eps ≤ |W n ω - 1|}) atTop (𝓝 0) := by
    intro eps heps
    have hreal : Tendsto (fun n => P.real {ω | eps ≤ |W n ω - 1|}) atTop (𝓝 0) := by
      simpa only [Real.norm_eq_abs] using
        (Statlib.StatFoundation.Convergence.tendstoInMeasure_iff_measureReal_norm.mp hW_conv) eps heps
    rw [ENNReal.tendsto_nhds_zero]
    intro b hb
    by_cases hb_top : b = ⊤
    · rw [hb_top]
      filter_upwards with n
      exact le_top
    · have hb_lt_top : b < ⊤ := lt_top_iff_ne_top.mpr hb_top
      have hb_real_pos : 0 < b.toReal := ENNReal.toReal_pos hb.ne' hb_top
      have hev : ∀ᶠ n in atTop, P.real {ω | eps ≤ |W n ω - 1|} < b.toReal :=
        (tendsto_order.1 hreal).2 b.toReal hb_real_pos
      filter_upwards [hev] with n hn
      have ha_ne_top : P {ω | eps ≤ |W n ω - 1|} ≠ ⊤ := measure_ne_top P _
      have hlt : P {ω | eps ≤ |W n ω - 1|} < b := by
        rw [← ENNReal.toReal_lt_toReal ha_ne_top hb_top]
        simpa [MeasureTheory.measureReal_def] using hn
      exact le_of_lt hlt
  have hU_clt : ∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n => ∫ ω, f (U n ω) ∂P) atTop
        (𝓝 (∫ x, f x ∂(gaussianReal 0 1))) := by
    intro f
    have hf_cont : Continuous (fun x : ℝ => f x) := f.continuous_toFun
    have hf_bound : ∃ C : ℝ, ∀ x : ℝ, |f x| ≤ C := by
      refine ⟨‖f‖, ?_⟩
      intro x
      simpa only [Real.norm_eq_abs] using BoundedContinuousFunction.norm_coe_le_norm f x
    simpa only [Xbar, U] using
      statopia_math_node_3313409290_5ba764b5 P X mean sigma hX_meas hX_indep hX_ident hmean hvar hsigma hX_memLp hX_mean hX_sq (fun x => f x) hf_cont hf_bound
  have hQ : ∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n => ∫ ω, f (Q n ω) ∂P) atTop
        (𝓝 (∫ x, f x ∂(gaussianReal 0 1))) := by
    intro f
    have hq := statopia_math_node_460667716_1894c750 P U W hU_meas hW_meas hU_mem hU_second hU_clt hW_prob
    simpa only [Q] using hq f
  have hT_eq_Q : ∀ n ω, T n ω = Q n ω := by
    intro n ω
    dsimp only [T, Q, U, W]
    by_cases hS : 0 < S n ω
    · have hWpos : 0 < S n ω / sigma := div_pos hS hsigma
      rw [if_pos hS, if_pos hWpos]
      field_simp [ne_of_gt hsigma, ne_of_gt hS]
    · have hWnonpos : ¬ 0 < S n ω / sigma :=
        not_lt.mpr (div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hS) (le_of_lt hsigma))
      rw [if_neg hS, if_neg hWnonpos]
  have hT_integral : ∀ (f : BoundedContinuousFunction ℝ ℝ) (n : ℕ),
      ∫ ω, f (T n ω) ∂P = ∫ ω, f (Q n ω) ∂P := by
    intro f n
    simp only [hT_eq_Q]
  have hT_conv : ∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n => ∫ ω, f (T n ω) ∂P) atTop
        (𝓝 (∫ x, f x ∂(gaussianReal 0 1))) := by
    intro f
    simpa only [hT_integral f] using hQ f
  have hG_map : Measure.map G P = gaussianReal 0 1 := by
    have hmap : Measure.map G P = Measure.map id (gaussianReal 0 1) := by
      ext s hs
      rw [Measure.map_apply hG_meas hs, Measure.map_apply measurable_id hs]
      exact ProbabilityTheory.IdentDistrib.measure_mem_eq hG_law hs
    simpa [hmap]
  have hT_meas : ∀ n, Measurable (T n) := by
    intro n
    have hset : MeasurableSet {ω | 0 < S n ω} := (hS_meas n) measurableSet_Ioi
    have hnum : Measurable (fun ω => Real.sqrt (n : ℝ) * (Xbar n ω - mean)) :=
      (measurable_const : Measurable fun _ : Ω => Real.sqrt (n : ℝ)).mul ((hXbar_meas n).sub (measurable_const : Measurable fun _ : Ω => mean))
    have hdiv : Measurable (fun ω => Real.sqrt (n : ℝ) * (Xbar n ω - mean) / S n ω) := hnum.div (hS_meas n)
    simpa only [T] using Measurable.ite hset hdiv (measurable_const : Measurable fun _ : Ω => (0 : ℝ))
  rw [Statlib.StatFoundation.Convergence.tendstoInDistribution_iff_weakConvergence_law P T G (fun n => (hT_meas n).aemeasurable) hG_meas.aemeasurable]
  unfold Statlib.StatFoundation.Convergence.WeakConvergence
  rw [MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  change Tendsto (fun n => ∫ ω, f ω ∂(Measure.map (T n) P)) atTop
    (𝓝 (∫ ω, f ω ∂(Measure.map G P)))
  rw [hG_map]
  have hmapT : ∀ n, ∫ x, f x ∂(Measure.map (T n) P) = ∫ ω, f (T n ω) ∂P := by
    intro n
    exact MeasureTheory.integral_map_of_stronglyMeasurable (hT_meas n) f.continuous_toFun.stronglyMeasurable
  simp only [hmapT]
  exact hT_conv f
  /- @proof-region region.root.e309b167dce5 end -/
