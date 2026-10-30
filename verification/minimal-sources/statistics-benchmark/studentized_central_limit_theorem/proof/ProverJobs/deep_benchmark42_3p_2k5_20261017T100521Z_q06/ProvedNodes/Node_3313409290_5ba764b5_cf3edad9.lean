import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q06.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q06.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q06.ProvedNodes.Node_1383303877_49b686b6_a7428605
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q06.ProvedNodes.Node_980666557_257fc9e4_2034ac47

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

set_option autoImplicit false in
theorem statopia_math_node_3313409290_5ba764b5 : ∀ {Ω : Type*} [MeasurableSpace Ω]
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
    (hX_sq : ∀ i, ∫ ω, (X i ω) ^ 2 ∂P = mean ^ 2 + sigma ^ 2),
    let Xbar : ℕ → Ω → ℝ :=
      fun n ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, X i ω
    let U : ℕ → Ω → ℝ :=
      fun n ω => Real.sqrt (n : ℝ) * (Xbar n ω - mean) / sigma
    ∀ f : ℝ → ℝ, Continuous f → (∃ C : ℝ, ∀ x : ℝ, |f x| ≤ C) →
      Tendsto (fun n : ℕ => ∫ ω, f (U n ω) ∂P) atTop
        (𝓝 (∫ x, f x ∂(gaussianReal 0 1))) := by
  /- @proof-region region.target-node.session.f79c35a0efda260c begin -/
  intro Ω instΩ P instP X mean sigma hX_meas hX_indep hX_ident hmean hvar hsigma hX_memLp
    hX_mean hX_sq Xbar U f hf hfb
  obtain ⟨C, hC⟩ := hfb
  let Xf : (n : ℕ) → Fin (n + 1) → Ω → ℝ := fun n j ω => X (j : ℕ) ω - mean
  let sF : ℕ → ℝ := fun n => sigma * Real.sqrt ((n : ℝ) + 1)
  have hsFpos : ∀ n, 0 < sF n := by
    intro n
    exact mul_pos hsigma (Real.sqrt_pos.mpr (by positivity))
  have hmeas : ∀ (n : ℕ) (j : Fin (n + 1)), Measurable (fun ω => X (j : ℕ) ω - mean) :=
    fun n j => (hX_meas (j : ℕ)).sub measurable_const
  have hmem : ∀ (n : ℕ) (j : Fin (n + 1)), MemLp (fun ω => X (j : ℕ) ω - mean) 2 P :=
    fun n j => (hX_memLp (j : ℕ)).sub (memLp_const mean)
  have hzero : ∀ (n : ℕ) (j : Fin (n + 1)), ∫ ω, (X (j : ℕ) ω - mean) ∂P = 0 := by
    intro n j
    have h1 : Integrable (fun ω => X (j : ℕ) ω) P :=
      MemLp.integrable (by norm_num) (hX_memLp (j : ℕ))
    have h2 : Integrable (fun _ : Ω => mean) P := integrable_const mean
    rw [integral_sub h1 h2, hX_mean (j : ℕ), integral_const]
    simp
  have hindep : ∀ n, iIndepFun (fun j : Fin (n + 1) => fun ω => X (j : ℕ) ω - mean) P := by
    intro n
    have h1 : iIndepFun (fun j : Fin (n + 1) => fun ω => X (j : ℕ) ω) P :=
      ProbabilityTheory.iIndepFun.precomp (g := fun j : Fin (n + 1) => (j : ℕ))
        (fun a b hab => Fin.ext hab) hX_indep
    exact ProbabilityTheory.iIndepFun.comp h1 (fun _ x => x - mean)
      (fun _ => measurable_id.sub measurable_const)
  have hsq : ∀ (n : ℕ) (j : Fin (n + 1)), ∫ ω, (X (j : ℕ) ω - mean) ^ 2 ∂P = sigma ^ 2 := by
    intro n j
    have h2 : Integrable (fun ω => (X (j : ℕ) ω) ^ 2) P := (hX_memLp (j : ℕ)).integrable_sq
    have h1 : Integrable (fun ω => X (j : ℕ) ω) P :=
      MemLp.integrable (by norm_num) (hX_memLp (j : ℕ))
    have h3 : Integrable (fun ω => (2 * mean) * X (j : ℕ) ω) P := h1.const_mul (2 * mean)
    have h4 : Integrable (fun _ : Ω => mean ^ 2) P := integrable_const _
    have hpt : ∀ ω : Ω, (X (j : ℕ) ω - mean) ^ 2
        = (X (j : ℕ) ω) ^ 2 - ((2 * mean) * X (j : ℕ) ω) + mean ^ 2 := by
      intro ω
      ring
    have e1 : ∫ ω, (X (j : ℕ) ω - mean) ^ 2 ∂P
        = ∫ ω, ((X (j : ℕ) ω) ^ 2 - ((2 * mean) * X (j : ℕ) ω) + mean ^ 2) ∂P :=
      integral_congr_ae (Eventually.of_forall hpt)
    have h5 : Integrable (fun ω => (X (j : ℕ) ω) ^ 2 - ((2 * mean) * X (j : ℕ) ω)) P := by
      simpa only [Pi.sub_apply] using h2.sub h3
    have e2 : ∫ ω, ((X (j : ℕ) ω) ^ 2 - ((2 * mean) * X (j : ℕ) ω) + mean ^ 2) ∂P
        = ∫ ω, ((X (j : ℕ) ω) ^ 2 - ((2 * mean) * X (j : ℕ) ω)) ∂P + ∫ ω, mean ^ 2 ∂P := by
      simpa only [Pi.add_apply] using integral_add h5 h4
    have e3 : ∫ ω, ((X (j : ℕ) ω) ^ 2 - ((2 * mean) * X (j : ℕ) ω)) ∂P
        = (mean ^ 2 + sigma ^ 2) - (2 * mean) * mean := by
      have h6 : ∫ ω, ((X (j : ℕ) ω) ^ 2 - ((2 * mean) * X (j : ℕ) ω)) ∂P
          = ∫ ω, (X (j : ℕ) ω) ^ 2 ∂P - ∫ ω, (2 * mean) * X (j : ℕ) ω ∂P := by
        simpa only [Pi.sub_apply] using integral_sub h2 h3
      rw [h6, hX_sq (j : ℕ), integral_const_mul, hX_mean (j : ℕ)]
    have e4 : ∫ ω, mean ^ 2 ∂P = mean ^ 2 := by
      rw [integral_const]
      simp
    rw [e1, e2, e3, e4]
    ring
  have hsum : ∀ n, ∑ j : Fin (n + 1), ∫ ω, (X (j : ℕ) ω - mean) ^ 2 ∂P = sF n ^ 2 := by
    intro n
    have h1 : ∑ j : Fin (n + 1), ∫ ω, (X (j : ℕ) ω - mean) ^ 2 ∂P
        = ∑ _j : Fin (n + 1), sigma ^ 2 :=
      Finset.sum_congr rfl (fun j _ => hsq n j)
    rw [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    simp only [sF]
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    push_cast
    ring
  have hlind := statopia_math_node_1383303877_49b686b6 (P := P) (X := X) (mean := mean)
    (sigma := sigma) hX_meas hX_ident hX_memLp hX_mean hX_sq hsigma
  have hLF := Statlib.StatFoundation.Convergence.LindebergFeller.lindeberg_feller_central_limit_theorem
    (μ := P) (k := fun n => n + 1) (fun n => Nat.succ_pos n) (X := Xf) (s := sF) hsFpos
    hmeas hindep hzero hmem hsum hlind
  obtain ⟨μ₀, hchar, htend⟩ := hLF
  have hμ : μ₀ = ⟨gaussianReal 0 1, inferInstance⟩ :=
    Statlib.StatFoundation.Convergence.probMeasure_eq_of_charFun_eq (fun t => hchar t)
  have hcoe3 : (↑(⟨gaussianReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ) : Measure ℝ)
      = gaussianReal 0 1 := rfl
  have hgC : ∀ x : ℝ, ‖f x‖ ≤ C := fun x => by
    simpa [Real.norm_eq_abs] using hC x
  let g : BoundedContinuousFunction ℝ ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroup f hf C hgC
  have hgbd : ∀ y : ℝ, g y = f y := fun y =>
    congrFun (BoundedContinuousFunction.coe_ofNormedAddCommGroup f hf C hgC) y
  have hgc : Continuous fun y : ℝ => g y := BoundedContinuousFunction.continuous g
  have hsum_meas : ∀ (n : ℕ), Measurable (fun ω : Ω => ∑ j : Fin (n + 1), Xf n j ω) := by
    intro n
    have key : ∀ t : Finset (Fin (n + 1)), Measurable (fun ω : Ω => ∑ j ∈ t, Xf n j ω) := by
      intro t
      induction t using Finset.induction_on with
      | empty => simpa using measurable_const
      | insert a t ha ih =>
          have hfun : (fun ω : Ω => ∑ j ∈ insert a t, Xf n j ω)
              = fun ω : Ω => Xf n a ω + ∑ j ∈ t, Xf n j ω := by
            funext ω
            rw [Finset.sum_insert ha]
          rw [hfun]
          exact (hmeas n a).add ih
    exact key Finset.univ
  have hgint := (MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp htend) g
  have hgc_eq : (∫ y : ℝ, g y ∂(gaussianReal 0 1)) = ∫ x : ℝ, f x ∂(gaussianReal 0 1) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    exact hgbd y
  have hlim : (∫ y : ℝ, g y ∂↑μ₀) = ∫ x : ℝ, f x ∂(gaussianReal 0 1) := by
    rw [hμ]
    exact hgc_eq
  rw [hlim] at hgint
  have hstep : Tendsto (fun n : ℕ => ∫ ω : Ω, f (U (n + 1) ω) ∂P) atTop
      (𝓝 (∫ x : ℝ, f x ∂(gaussianReal 0 1))) := by
    refine Filter.Tendsto.congr' (Filter.Eventually.of_forall (fun n => ?_)) hgint
    show ∫ y : ℝ, g y ∂(Measure.map (fun ω : Ω => (∑ j : Fin (n + 1), Xf n j ω) / sF n) P)
        = ∫ ω : Ω, f (U (n + 1) ω) ∂P
    rw [MeasureTheory.integral_map_of_stronglyMeasurable
      (φ := fun ω : Ω => (∑ j : Fin (n + 1), Xf n j ω) / sF n)
      ((hsum_meas n).div measurable_const) hgc.stronglyMeasurable]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
    show g ((∑ j : Fin (n + 1), Xf n j ω) / sF n) = f (U (n + 1) ω)
    rw [hgbd]
    congr 1
    show (∑ j : Fin (n + 1), (X (j : ℕ) ω - mean)) / (sigma * Real.sqrt ((n : ℝ) + 1))
        = Real.sqrt (↑(n + 1) : ℝ) * ((↑(n + 1) : ℝ)⁻¹ * ∑ i ∈ Finset.range (n + 1), X i ω - mean)
          / sigma
    rw [Fin.sum_univ_eq_sum_range (fun i => X i ω - mean) (n + 1)]
    have hsplit : ∑ i ∈ Finset.range (n + 1), (X i ω - mean)
        = (∑ i ∈ Finset.range (n + 1), X i ω) - ((n : ℝ) + 1) * mean := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring
    rw [hsplit]
    have hsq' : Real.sqrt ((n : ℝ) + 1) ^ 2 = (n : ℝ) + 1 := Real.sq_sqrt (by positivity)
    push_cast
    set h : ℝ := Real.sqrt ((n : ℝ) + 1) with hh_def
    set S : ℝ := ∑ i ∈ Finset.range (n + 1), X i ω with hS
    have hh2 : h * h = (↑n + 1 : ℝ) := by
      rw [hh_def, ← pow_two]
      exact hsq'
    have hhne : h ≠ 0 := by
      rw [hh_def]
      exact ne_of_gt (Real.sqrt_pos.mpr (by positivity))
    have hh2ne : h * h ≠ 0 := mul_ne_zero hhne hhne
    have hσne : sigma ≠ 0 := ne_of_gt hsigma
    rw [← hh2]
    field_simp
  have hshift : Tendsto (fun n : ℕ => n - 1) atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    exact ⟨b + 1, fun x hx => by omega⟩
  have h2 : Tendsto (fun n : ℕ => ∫ ω : Ω, f (U (n - 1 + 1) ω) ∂P) atTop
      (𝓝 (∫ x : ℝ, f x ∂(gaussianReal 0 1))) := by
    have hcomp := hstep.comp hshift
    simpa [Function.comp] using hcomp
  refine Filter.Tendsto.congr' ?_ h2
  refine Filter.eventually_atTop.mpr ⟨1, fun b hb => ?_⟩
  simp only [Nat.sub_add_cancel hb]
  /- @proof-region region.target-node.session.f79c35a0efda260c end -/
