import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q06.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q06.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q06.ProvedNodes.Node_980666557_257fc9e4_2034ac47

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

set_option autoImplicit false in
theorem statopia_math_node_3827306998_2acd3346 : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ)
    (mean sigma : ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X P)
    (hX_ident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hmean : ∫ ω, X 0 ω ∂P = mean)
    (hvar : variance (X 0) P = sigma ^ 2)
    (hsigma : 0 < sigma)
    (hX_memLp : ∀ i, MemLp (X i) 2 P)
    (hX_mean : ∀ i, ∫ ω, X i ω ∂P = mean)
    (hX_second : ∀ i, ∫ ω, (X i ω) ^ 2 ∂P = mean ^ 2 + sigma ^ 2)
    (hX0_int : Integrable (X 0) P)
    (hX0_sq_int : Integrable (fun ω => (X 0 ω) ^ 2) P),
    let Xbar : ℕ → Ω → ℝ :=
      fun n ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, X i ω
    let V : ℕ → Ω → ℝ :=
      fun n ω =>
        (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, (X i ω - Xbar n ω) ^ 2
    let S : ℕ → Ω → ℝ := fun n ω => Real.sqrt (V n ω)
    let W : ℕ → Ω → ℝ := fun n ω => S n ω / sigma
    TendstoInMeasure P V atTop (fun _ => sigma ^ 2) ∧
    TendstoInMeasure P S atTop (fun _ => sigma) ∧
    TendstoInMeasure P W atTop (fun _ => (1 : ℝ)) ∧
    Tendsto (fun n => P {ω | W n ω < 1 / 2}) atTop (𝓝 0) := by
  /- @proof-region region.target-node.session.efee3b5e3c504c9a begin -/
  intro Ω _ P _ X mean sigma hX_meas hX_indep hX_ident hmean hvar hsigma hX_memLp hX_mean hX_second
    hX0_int hX0_sq_int
  obtain ⟨hMemLp, hMean, hSecond, hInt, hSqInt⟩ :=
    statopia_math_node_980666557_257fc9e4 P X mean sigma hX_meas hX_ident hmean hvar hsigma
  classical
  let Xbar : ℕ → Ω → ℝ := fun n ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, X i ω
  let A : ℕ → Ω → ℝ := fun n ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, (X i ω) ^ 2
  let Y : ℕ → Ω → ℝ := fun i ω => (X i ω) ^ 2
  let V : ℕ → Ω → ℝ := fun n ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, (X i ω - Xbar n ω) ^ 2
  let S : ℕ → Ω → ℝ := fun n ω => Real.sqrt (V n ω)
  let W : ℕ → Ω → ℝ := fun n ω => S n ω / sigma
  have hpwX : Pairwise (Function.onFun (fun x1 x2 : Ω → ℝ => x1 ⟂ᵢ[P] x2) X) :=
    fun i j hij => hX_indep.indepFun hij
  have hSlaw1 : ∀ᵐ ω ∂P, Tendsto (fun n => Xbar n ω) atTop (𝓝 mean) := by
    have h := strong_law_ae X hInt hpwX hX_ident
    filter_upwards [h] with ω hω
    have hω' : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, X i ω) atTop (𝓝 mean) := by
      simpa [hmean, smul_eq_mul] using hω
    simpa [Xbar] using hω'
  have hY_indep : iIndepFun Y P := by
    have h := hX_indep.comp (fun (_ : ℕ) (x : ℝ) => x ^ 2) (fun _ => by measurability)
    simpa [Y, Function.comp_def] using h
  have hpwY : Pairwise (Function.onFun (fun x1 x2 : Ω → ℝ => x1 ⟂ᵢ[P] x2) Y) :=
    fun i j hij => hY_indep.indepFun hij
  have hYident : ∀ i, IdentDistrib (Y i) (Y 0) P P := by
    intro i
    simpa [Y] using (hX_ident i).sq
  have hSlaw2 : ∀ᵐ ω ∂P, Tendsto (fun n => A n ω) atTop (𝓝 (mean ^ 2 + sigma ^ 2)) := by
    have h := strong_law_ae Y hSqInt hpwY hYident
    filter_upwards [h] with ω hω
    have h0 : ∫ x, (X 0 x) ^ 2 ∂P = mean ^ 2 + sigma ^ 2 := hSecond 0
    have hω' : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, (X i ω) ^ 2) atTop
        (𝓝 (mean ^ 2 + sigma ^ 2)) := by
      simpa [Y, h0, smul_eq_mul] using hω
    simpa [A] using hω'
  have hValg : ∀ (n : ℕ) (ω : Ω), V n ω = A n ω - (Xbar n ω) ^ 2 := by
    have hkey : ∀ (n : ℕ) (ω : Ω),
        ∑ i ∈ Finset.range n, (X i ω - Xbar n ω) ^ 2
          = (∑ i ∈ Finset.range n, (X i ω) ^ 2)
              - 2 * Xbar n ω * (∑ i ∈ Finset.range n, X i ω) + (n : ℝ) * (Xbar n ω) ^ 2 := by
      intro n ω
      have h1 : ∑ i ∈ Finset.range n, (X i ω - Xbar n ω) ^ 2
          = ∑ i ∈ Finset.range n, ((X i ω) ^ 2 - 2 * Xbar n ω * X i ω + (Xbar n ω) ^ 2) :=
        Finset.sum_congr rfl (fun i _ => by ring)
      rw [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul]
    intro n ω
    by_cases hn : (n : ℝ) = 0
    · simp [V, A, Xbar, hn]
    · have hk := hkey n ω
      have hc : Xbar n ω = (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, X i ω := rfl
      show (n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, (X i ω - Xbar n ω) ^ 2)
          = (n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, (X i ω) ^ 2) - (Xbar n ω) ^ 2
      rw [hk, hc]
      field_simp
      ring
  have hV_ae : ∀ᵐ ω ∂P, Tendsto (fun n => V n ω) atTop (𝓝 (sigma ^ 2)) := by
    filter_upwards [hSlaw1, hSlaw2] with ω h1 h2
    have h3 : Tendsto (fun n => A n ω - (Xbar n ω) ^ 2) atTop
        (𝓝 (mean ^ 2 + sigma ^ 2 - mean ^ 2)) :=
      h2.sub (h1.pow 2)
    have h4 : mean ^ 2 + sigma ^ 2 - mean ^ 2 = sigma ^ 2 := by ring
    rw [h4] at h3
    have hfun : (fun n => V n ω) = (fun n => A n ω - (Xbar n ω) ^ 2) :=
      funext fun n => hValg n ω
    rw [hfun]
    exact h3
  have hS_ae : ∀ᵐ ω ∂P, Tendsto (fun n => S n ω) atTop (𝓝 sigma) := by
    filter_upwards [hV_ae] with ω hω
    have hcont : Tendsto Real.sqrt (𝓝 (sigma ^ 2)) (𝓝 (Real.sqrt (sigma ^ 2))) :=
      Real.continuous_sqrt.continuousAt
    have h2 := hcont.comp hω
    rw [Real.sqrt_sq hsigma.le] at h2
    simpa [S] using h2
  have hW_ae : ∀ᵐ ω ∂P, Tendsto (fun n => W n ω) atTop (𝓝 1) := by
    filter_upwards [hS_ae] with ω hω
    have h2 := hω.div_const sigma
    have hσ : sigma / sigma = (1 : ℝ) := div_self hsigma.ne'
    rw [hσ] at h2
    simpa [W] using h2
  have hXb_meas : ∀ n, Measurable (Xbar n) := by
    intro n
    have hsum : Measurable (fun ω => ∑ i ∈ Finset.range n, X i ω) :=
      Finset.measurable_sum _ (fun i _ => hX_meas i)
    have h2 : Measurable (fun ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, X i ω) := hsum.const_mul _
    simpa [Xbar] using h2
  have hV_meas : ∀ n, Measurable (V n) := by
    intro n
    have hterm : ∀ i, Measurable (fun ω => (X i ω - Xbar n ω) ^ 2) := by
      intro i
      have h1 : Measurable (fun ω => X i ω - Xbar n ω) := (hX_meas i).sub (hXb_meas n)
      simpa [pow_two] using h1.mul h1
    have hsum : Measurable (fun ω => ∑ i ∈ Finset.range n, (X i ω - Xbar n ω) ^ 2) :=
      Finset.measurable_sum _ (fun i _ => hterm i)
    have h2 : Measurable (fun ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, (X i ω - Xbar n ω) ^ 2) :=
      hsum.const_mul _
    simpa [V] using h2
  have hS_meas : ∀ n, Measurable (S n) := by
    intro n
    have h : Measurable (fun ω => Real.sqrt (V n ω)) :=
      Real.continuous_sqrt.measurable.comp (hV_meas n)
    simpa [S] using h
  have hW_meas : ∀ n, Measurable (W n) := by
    intro n
    have h : Measurable (fun ω => S n ω / sigma) := (hS_meas n).div_const sigma
    simpa [W] using h
  have hV_tim : TendstoInMeasure P V atTop (fun _ => sigma ^ 2) :=
    tendstoInMeasure_of_tendsto_ae (fun n => (hV_meas n).aestronglyMeasurable) hV_ae
  have hS_tim : TendstoInMeasure P S atTop (fun _ => sigma) :=
    tendstoInMeasure_of_tendsto_ae (fun n => (hS_meas n).aestronglyMeasurable) hS_ae
  have hW_tim : TendstoInMeasure P W atTop (fun _ => (1 : ℝ)) :=
    tendstoInMeasure_of_tendsto_ae (fun n => (hW_meas n).aestronglyMeasurable) hW_ae
  have hlast : Tendsto (fun n => P {ω | W n ω < 1 / 2}) atTop (𝓝 0) := by
    have hε : (0 : ℝ) < 1 / 2 := by norm_num
    have hreal :=
      (Statlib.StatFoundation.Convergence.tendstoInMeasure_iff_measureReal_dist.mp hW_tim) (1 / 2) hε
    have hsub : ∀ n, {ω : Ω | W n ω < 1 / 2} ⊆ {ω : Ω | (1 / 2 : ℝ) ≤ dist (W n ω) 1} := by
      intro n ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      rw [Real.dist_eq, abs_sub_comm]
      have h1 : (0 : ℝ) ≤ 1 - W n ω := by linarith
      rw [abs_of_nonneg h1]
      linarith
    have hbound : Tendsto (fun n => P.real {ω | W n ω < 1 / 2}) atTop (𝓝 0) :=
      squeeze_zero (fun n => measureReal_nonneg)
        (fun n => measureReal_mono (hsub n) (measure_ne_top P _)) hreal
    have hgoal : (fun n => P {ω | W n ω < 1 / 2})
        = fun n => ENNReal.ofReal (P.real {ω | W n ω < 1 / 2}) := by
      funext n
      exact (MeasureTheory.ofReal_measureReal (measure_ne_top P _)).symm
    have hcomp : Tendsto (fun n => ENNReal.ofReal (P.real {ω | W n ω < 1 / 2})) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n => ENNReal.ofReal (P.real {ω | W n ω < 1 / 2})) atTop
          (𝓝 (ENNReal.ofReal 0)) :=
        (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hbound
      simpa using h1
    rw [hgoal]
    exact hcomp
  exact ⟨hV_tim, hS_tim, hW_tim, hlast⟩
  /- @proof-region region.target-node.session.efee3b5e3c504c9a end -/
