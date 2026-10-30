import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q15.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q15.ProvedNodes
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q15.Base

open Filter MeasureTheory ProbabilityTheory

theorem arcsine_bernoulli_mean_clt
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (θ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (X : ℕ → Ω → Bool)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X P)
    (hX_law : ∀ i,
      HasLaw (X i)
        (PMF.bernoulli ⟨θ, hθ₀.le⟩ (by exact_mod_cast hθ₁.le)).toMeasure P)
    (Z : Ω → ℝ) (hZ_meas : Measurable Z)
    (hZ_law : HasLaw Z (gaussianReal 0 1) P) :
    let mean : ℕ → Ω → ℝ := fun r ω ↦
      ((r + 1 : ℕ) : ℝ)⁻¹ *
        ∑ i ∈ Finset.range (r + 1), if X i ω then 1 else 0
    TendstoInDistribution
      (fun (r : ℕ) ω ↦ 2 * Real.sqrt (((r + 1 : ℕ) : ℝ)) *
        (Real.arcsin (Real.sqrt (mean r ω)) -
          Real.arcsin (Real.sqrt θ)))
      atTop Z P
:= by
  /- @proof-region region.root.ca4e947e5eca begin -/
  dsimp only
  let s : ℝ := Real.sqrt (θ * (1 - θ))
  let Y : ℕ → Ω → ℝ := fun i ω => (if X i ω = true then (1 : ℝ) else 0) - θ
  let q : ℝ → ℝ := fun x => if x = θ then 1 / s
    else (2 * Real.arcsin (Real.sqrt x) - 2 * Real.arcsin (Real.sqrt θ)) / (x - θ)
  have hs : s = Real.sqrt (θ * (1 - θ)) := rfl
  have hderiv : HasDerivAt (fun x : ℝ => 2 * Real.arcsin (Real.sqrt x)) (1 / Real.sqrt (θ * (1 - θ))) θ ∧
      Real.sqrt (θ * (1 - θ)) > 0 ∧ Real.sqrt (θ * (1 - θ)) * (1 / Real.sqrt (θ * (1 - θ))) = 1 :=
    statopia_math_node_4073185746_5120f090 θ hθ₀ hθ₁
  have hderiv' : HasDerivAt (fun x : ℝ => 2 * Real.arcsin (Real.sqrt x)) (1 / s) θ := by
    simpa only [hs] using hderiv.1
  have hspos' : 0 < s := by rw [hs]; exact hderiv.2.1
  have hsL' : s * (1 / s) = 1 := by rw [hs]; exact hderiv.2.2
  have hqdef : q = fun x => if x = θ then 1 / s
      else (2 * Real.arcsin (Real.sqrt x) - 2 * Real.arcsin (Real.sqrt θ)) / (x - θ) := rfl
  have hqθ : q θ = 1 / s := by rw [hqdef]; simp
  have hθpos : 0 < θ * (1 - θ) := mul_pos hθ₀ (by linarith)
  have hsq : s * s = θ * (1 - θ) := by rw [hs, ← pow_two, Real.sq_sqrt hθpos.le]
  have hfmeas : Measurable (fun x : ℝ => 2 * Real.arcsin (Real.sqrt x)) :=
    measurable_const.mul (Real.continuous_arcsin.measurable.comp Real.continuous_sqrt.measurable)
  obtain ⟨-, hqmeas, hqtend⟩ := statopia_math_node_2301537299_8f42f7c7 θ (1 / s)
    (fun x : ℝ => 2 * Real.arcsin (Real.sqrt x)) hfmeas hderiv'
  have hξmeas : ∀ i, Measurable (fun ω => if X i ω = true then (1 : ℝ) else 0) := fun i =>
    (measurable_of_finite (fun b : Bool => if b = true then (1 : ℝ) else 0)).comp (hX_meas i)
  have hYmeas : ∀ i, Measurable (Y i) := by
    intro i
    have hval : Y i = fun ω => (if X i ω = true then (1 : ℝ) else 0) - θ := rfl
    rw [hval]
    simpa only [Pi.sub_apply] using (hξmeas i).sub (measurable_const : Measurable fun _ : Ω => θ)
  have hYbound : ∀ (i : ℕ) (ω : Ω), |Y i ω| ≤ 1 := by
    intro i ω
    have hval : Y i ω = (if X i ω = true then (1 : ℝ) else 0) - θ := rfl
    rw [hval, abs_le]
    constructor
    · by_cases h : X i ω = true
      · rw [if_pos h]; linarith
      · rw [if_neg h]; linarith
    · by_cases h : X i ω = true
      · rw [if_pos h]; linarith
      · rw [if_neg h]; linarith
  have hYint : ∀ i, Integrable (Y i) P := by
    intro i
    exact Integrable.of_bound (hYmeas i).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hYbound i ω)
  have hYsqint : ∀ i, Integrable (fun ω => (Y i ω) ^ 2) P := by
    intro i
    have hae : AEStronglyMeasurable (fun ω => (Y i ω) ^ 2) P := by
      first
        | exact ((hYmeas i).pow 2).aestronglyMeasurable
        | exact ((hYmeas i).pow_const 2).aestronglyMeasurable
    refine Integrable.of_bound hae 1 (Filter.Eventually.of_forall fun ω => ?_)
    have h2 : |(Y i ω) ^ 2| ≤ 1 := by
      have h1 : |Y i ω| ≤ 1 := hYbound i ω
      have h0 : 0 ≤ |Y i ω| := abs_nonneg _
      rw [abs_pow]
      nlinarith [h1, h0, mul_nonneg h0 (sub_nonneg.mpr h1)]
    simpa only [Real.norm_eq_abs] using h2
  have hYmemLp : ∀ i, MemLp (Y i) 3 P := by
    intro i
    exact MemLp.of_bound (hYmeas i).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hYbound i ω)
  have hYindep : iIndepFun Y P := by
    have hm : ∀ i : ℕ, Measurable (fun b : Bool => (if b = true then (1 : ℝ) else 0) - θ) := fun _ =>
      (measurable_of_finite (fun b : Bool => if b = true then (1 : ℝ) else 0)).sub measurable_const
    have h : iIndepFun (fun i ω => (if X i ω = true then (1 : ℝ) else 0) - θ) P := by
      first
        | exact hX_indep.comp (fun (_ : ℕ) (b : Bool) => (if b = true then (1 : ℝ) else 0) - θ) hm
        | exact hX_indep.comp hm
        | exact hX_indep.comp (g := fun (_ : ℕ) (b : Bool) => (if b = true then (1 : ℝ) else 0) - θ) hm
    simpa only [Function.comp_def] using h
  have huniv : P.real Set.univ = 1 := by simp
  have hbif : ∀ (b : Bool) (x y : ℝ), (if b = true then x else y) = bif b then x else y := by
    intro b x y
    cases b <;> rfl
  have hξint : ∀ i, ∫ ω, (if X i ω = true then (1 : ℝ) else 0) ∂P = θ := by
    intro i
    have h := ProbabilityTheory.HasLaw.integral_comp (hX_law i)
      (f := fun b : Bool => if b = true then (1 : ℝ) else 0)
      (measurable_of_finite (fun b : Bool => if b = true then (1 : ℝ) else 0)).aestronglyMeasurable
    have h2 : ∫ (b : Bool), (if b = true then (1 : ℝ) else 0)
        ∂(PMF.bernoulli ⟨θ, hθ₀.le⟩ (by exact_mod_cast hθ₁.le)).toMeasure = θ := by
      simpa only [hbif] using
        (PMF.bernoulli_expectation (p := ⟨θ, hθ₀.le⟩) (h := by exact_mod_cast hθ₁.le))
    simpa only [Function.comp_def] using h.trans h2
  have hξint_int : ∀ i, Integrable (fun ω => if X i ω = true then (1 : ℝ) else 0) P := by
    intro i
    refine Integrable.of_bound (hξmeas i).aestronglyMeasurable 1 (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    by_cases h : X i ω = true
    · rw [if_pos h]; norm_num
    · rw [if_neg h]; norm_num
  have hind_int : ∀ (i : ℕ) (a b : ℝ),
      ∫ ω, (if X i ω = true then a else b) ∂P = a * θ + b * (1 - θ) := by
    intro i a b
    have hpt : ∀ ω, (if X i ω = true then a else b)
        = b + (a - b) * (if X i ω = true then (1 : ℝ) else 0) := by
      intro ω
      by_cases h : X i ω = true
      · rw [if_pos h, if_pos h]; ring
      · rw [if_neg h, if_neg h]; ring
    have hint2 : Integrable (fun ω => (a - b) * (if X i ω = true then (1 : ℝ) else 0)) P := by
      refine Integrable.of_bound ?_ (|a - b|) (Filter.Eventually.of_forall fun ω => ?_)
      · exact (measurable_const.mul (hξmeas i)).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_mul]
        by_cases h : X i ω = true
        · rw [if_pos h, abs_one, mul_one]
        · rw [if_neg h, abs_zero, mul_zero]
          exact abs_nonneg _
    calc ∫ ω, (if X i ω = true then a else b) ∂P
        = ∫ ω, (b + (a - b) * (if X i ω = true then (1 : ℝ) else 0)) ∂P :=
          integral_congr_ae (Filter.Eventually.of_forall hpt)
      _ = ∫ _ : Ω, b ∂P + ∫ ω, (a - b) * (if X i ω = true then (1 : ℝ) else 0) ∂P :=
          integral_add (integrable_const b) hint2
      _ = a * θ + b * (1 - θ) := by
          rw [integral_const, integral_const_mul, hξint i, huniv, one_smul]
          ring
  have hYident : ∀ i j, IdentDistrib (Y i) (Y j) P P := by
    intro i j
    have hXi : IdentDistrib (X i) (X j) P P :=
      ⟨(hX_meas i).aemeasurable, (hX_meas j).aemeasurable,
        ((hX_law i).measurePreserving (hX_meas i)).map_eq.trans
          ((hX_law j).measurePreserving (hX_meas j)).map_eq.symm⟩
    exact IdentDistrib.comp hXi
      (measurable_of_finite (fun b : Bool => (if b = true then (1 : ℝ) else 0) - θ))
  have hYmean : ∀ i, ∫ ω, Y i ω ∂P = 0 := by
    intro i
    have hYfun : (fun ω => Y i ω) = fun ω => ((if X i ω = true then (1 : ℝ) else 0) - θ) := rfl
    have hsub : ∫ ω, ((if X i ω = true then (1 : ℝ) else 0) - θ) ∂P
        = ∫ ω, (if X i ω = true then (1 : ℝ) else 0) ∂P - ∫ _ : Ω, θ ∂P :=
      integral_sub (hξint_int i) (integrable_const θ)
    rw [hYfun, hsub, hξint i, integral_const, huniv, one_smul]
    ring
  have hYvar : ∀ i, ∫ ω, (Y i ω) ^ 2 ∂P = θ * (1 - θ) := by
    intro i
    have hpt : ∀ ω, (Y i ω) ^ 2 = (if X i ω = true then (1 - θ) ^ 2 else θ ^ 2) := by
      intro ω
      have hYv : Y i ω = (if X i ω = true then (1 : ℝ) else 0) - θ := rfl
      rw [hYv]
      by_cases h : X i ω = true
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h]; ring
    calc ∫ ω, (Y i ω) ^ 2 ∂P
        = ∫ ω, (if X i ω = true then (1 - θ) ^ 2 else θ ^ 2) ∂P :=
          integral_congr_ae (Filter.Eventually.of_forall hpt)
      _ = θ * (1 - θ) := by
          rw [hind_int i ((1 - θ) ^ 2) (θ ^ 2)]
          ring
  have hYthird : ∀ i, ∫ ω, |Y i ω| ^ 3 ∂P = θ * (1 - θ) ^ 3 + (1 - θ) * θ ^ 3 := by
    intro i
    have hpt : ∀ ω, |Y i ω| ^ 3 = (if X i ω = true then (1 - θ) ^ 3 else θ ^ 3) := by
      intro ω
      have hYv : Y i ω = (if X i ω = true then (1 : ℝ) else 0) - θ := rfl
      rw [hYv]
      by_cases h : X i ω = true
      · rw [if_pos h, if_pos h, abs_of_pos (by linarith : (0 : ℝ) < 1 - θ)]
      · rw [if_neg h, if_neg h, show (0 : ℝ) - θ = -θ by ring, abs_neg, abs_of_pos hθ₀]
    calc ∫ ω, |Y i ω| ^ 3 ∂P
        = ∫ ω, (if X i ω = true then (1 - θ) ^ 3 else θ ^ 3) ∂P :=
          integral_congr_ae (Filter.Eventually.of_forall hpt)
      _ = θ * (1 - θ) ^ 3 + (1 - θ) * θ ^ 3 := by
          rw [hind_int i ((1 - θ) ^ 3) (θ ^ 3)]
          ring
  obtain ⟨μ₀, hchar, hμtend⟩ := Statlib.StatFoundation.Convergence.CLT.iid_central_limit_theorem
    (μ := P) (Y := Y) (σ := s) (ρ := θ * (1 - θ) ^ 3 + (1 - θ) * θ ^ 3) hspos'
    hYmeas hYindep hYident hYmean
    (by intro i; rw [show s ^ 2 = θ * (1 - θ) by rw [pow_two]; exact hsq]; exact hYvar i)
    hYthird hYmemLp
  have hB : TendstoInDistribution
      (fun r ω => Statlib.StatFoundation.Convergence.CLT.standardizedSum Y s (r + 1) ω) atTop Z P := by
    refine Statlib.StatFoundation.Convergence.tendstoInDistribution_of_probabilityMeasure_tendsto_and_gaussianReal_charFun
      (X := fun r => Statlib.StatFoundation.Convergence.CLT.standardizedSum Y s (r + 1)) ?_ ?_ ?_ ⟨μ₀, hchar, hμtend⟩
    · intro r
      exact (Statlib.StatFoundation.Convergence.CLT.measurable_standardizedSum hYmeas).aemeasurable
    · exact hZ_meas.aemeasurable
    · exact (hZ_law.measurePreserving hZ_meas).map_eq
  obtain ⟨hmom2, hp_tendsto⟩ := statopia_math_node_4041512676_26716216 P θ hθ₀ hθ₁
    (fun i ω => (if X i ω = true then (1 : ℝ) else 0)) hYmeas hYindep hYint hYmean hYvar hYsqint hYbound
  have hmult : TendstoInMeasure P
      (fun r ω => s * q ((((r + 1 : ℕ) : ℝ))⁻¹ * ∑ i ∈ Finset.range (r + 1), (if X i ω = true then (1 : ℝ) else 0)))
      atTop (fun _ => 1) := by
    rw [Statlib.StatFoundation.Convergence.tendstoInMeasure_iff_measureReal_dist]
    intro ε hε
    have hc : ContinuousAt (fun x : ℝ => s * q x) θ := by
      have h1 : Tendsto (fun x : ℝ => s * q x) (nhds θ) (nhds (s * q θ)) := by
        have h0 : Tendsto (fun x : ℝ => s * q x) (nhds θ) (nhds (s * (1 / s))) := by
          first
            | exact hqtend.const_mul s
            | exact Tendsto.const_mul s hqtend
        simpa only [hqθ] using h0
      exact h1
    obtain ⟨δ, hδpos, hδ⟩ := by
      first
        | exact Metric.continuousAt_iff.1 hc ε hε
        | exact Metric.eventually_nhds_iff.1 (Metric.tendsto_nhds.1 hc ε hε)
    have hδ' : ∀ y : ℝ, dist y θ < δ → dist (s * q y) 1 < ε := by
      intro y hy
      first
        | simpa only [hqθ, hsL'] using hδ hy
        | simpa only [hqθ, hsL'] using hδ (y := y) hy
        | simpa only [hqθ, hsL'] using hδ y hy
    have hb : Tendsto (fun r : ℕ => P.real {ω : Ω | δ ≤ dist ((((r + 1 : ℕ) : ℝ))⁻¹ * ∑ i ∈ Finset.range (r + 1), (if X i ω = true then (1 : ℝ) else 0)) θ}) atTop (nhds 0) :=
      (Statlib.StatFoundation.Convergence.tendstoInMeasure_iff_measureReal_dist.1 hp_tendsto) δ hδpos
    refine squeeze_zero (fun r => ?_) (fun r => ?_) hb
    · first
        | exact MeasureTheory.measureReal_nonneg
        | exact MeasureTheory.measureReal_nonneg P _
        | positivity
    · have hsub : {ω : Ω | ε ≤ dist (s * q ((((r + 1 : ℕ) : ℝ))⁻¹ * ∑ i ∈ Finset.range (r + 1), (if X i ω = true then (1 : ℝ) else 0))) 1}
          ⊆ {ω : Ω | δ ≤ dist ((((r + 1 : ℕ) : ℝ))⁻¹ * ∑ i ∈ Finset.range (r + 1), (if X i ω = true then (1 : ℝ) else 0)) θ} := by
        intro ω hω
        simp only [Set.mem_setOf_eq] at hω ⊢
        by_contra hcon
        have h1 : dist ((((r + 1 : ℕ) : ℝ))⁻¹ * ∑ i ∈ Finset.range (r + 1), (if X i ω = true then (1 : ℝ) else 0)) θ < δ :=
          not_le.1 hcon
        linarith [hδ' _ h1, hω]
      first
        | exact measureReal_mono hsub (measure_ne_top P _)
        | exact MeasureTheory.measureReal_mono hsub (measure_ne_top P _)
        | exact measureReal_mono hsub
        | exact MeasureTheory.measureReal_mono hsub
  have hmult_ae : ∀ r, AEMeasurable
      (fun ω => s * q ((((r + 1 : ℕ) : ℝ))⁻¹ * ∑ i ∈ Finset.range (r + 1), (if X i ω = true then (1 : ℝ) else 0))) P := by
    intro r
    have hpm : Measurable (fun ω : Ω => (((r + 1 : ℕ) : ℝ))⁻¹ * ∑ i ∈ Finset.range (r + 1), (if X i ω = true then (1 : ℝ) else 0)) := by
      first
        | exact measurable_const.mul (Finset.measurable_sum (Finset.range (r + 1)) (fun i _ => hξmeas i))
        | exact Measurable.const_mul (Finset.measurable_sum (Finset.range (r + 1)) (fun i _ => hξmeas i)) _
        | exact measurable_const.mul (measurable_finset_sum (Finset.range (r + 1)) (fun i _ => hξmeas i))
    have hqm : Measurable (fun ω : Ω => s * q ((((r + 1 : ℕ) : ℝ))⁻¹ * ∑ i ∈ Finset.range (r + 1), (if X i ω = true then (1 : ℝ) else 0))) := by
      first
        | exact (hqmeas.comp hpm).const_mul s
        | exact measurable_const.mul (hqmeas.comp hpm)
    exact hqm.aemeasurable
  have hprod : TendstoInDistribution
      (fun r ω => (fun z : ℝ × ℝ => z.2 * z.1)
        (Statlib.StatFoundation.Convergence.CLT.standardizedSum Y s (r + 1) ω,
          s * q ((((r + 1 : ℕ) : ℝ))⁻¹ * ∑ i ∈ Finset.range (r + 1), (if X i ω = true then (1 : ℝ) else 0))))
      atTop (fun ω => 1 * Z ω) P :=
    MeasureTheory.TendstoInDistribution.continuous_comp_prodMk_of_tendstoInMeasure_const
      (l := atTop) (μ := P) (Z := Z)
      (X := fun r ω => Statlib.StatFoundation.Convergence.CLT.standardizedSum Y s (r + 1) ω)
      (Y := fun r ω => s * q ((((r + 1 : ℕ) : ℝ))⁻¹ * ∑ i ∈ Finset.range (r + 1), (if X i ω = true then (1 : ℝ) else 0)))
      (c := 1) (g := fun z : ℝ × ℝ => z.2 * z.1)
      (continuous_snd.mul continuous_fst) hB hmult hmult_ae
  have hBval : ∀ (r : ℕ) (ω : Ω), Statlib.StatFoundation.Convergence.CLT.standardizedSum Y s (r + 1) ω
      = (∑ i ∈ Finset.range (r + 1), Y i ω) / (s * Real.sqrt (((r + 1 : ℕ) : ℝ))) := by
    intro r ω
    have hsum : (∑ i : Fin (r + 1), Y i ω) = ∑ i ∈ Finset.range (r + 1), Y i ω := by
      first
        | exact Fin.sum_univ_eq_sum_range (fun i => Y i ω) (r + 1)
        | exact (Fin.sum_univ_eq_sum_range (fun i => Y i ω) (r + 1)).symm
    simp only [Statlib.StatFoundation.Convergence.CLT.standardizedSum, hsum]
  have hfact : ∀ (r : ℕ) (ω : Ω),
      (fun z : ℝ × ℝ => z.2 * z.1)
        (Statlib.StatFoundation.Convergence.CLT.standardizedSum Y s (r + 1) ω,
          s * q ((((r + 1 : ℕ) : ℝ))⁻¹ * ∑ i ∈ Finset.range (r + 1), (if X i ω = true then (1 : ℝ) else 0)))
      = 2 * Real.sqrt (((r + 1 : ℕ) : ℝ)) *
          (Real.arcsin (Real.sqrt ((((r + 1 : ℕ) : ℝ))⁻¹ * ∑ i ∈ Finset.range (r + 1), (if X i ω = true then (1 : ℝ) else 0))) - Real.arcsin (Real.sqrt θ)) := by
    intro r ω
    let n : ℝ := (((r + 1 : ℕ) : ℝ))
    let N : ℝ := Real.sqrt n
    let x : ℝ := n⁻¹ * ∑ i ∈ Finset.range (r + 1), (if X i ω = true then (1 : ℝ) else 0)
    have hnpos : 0 < n := by dsimp only [n]; push_cast; positivity
    have hnne : n ≠ 0 := ne_of_gt hnpos
    have hNpos : 0 < N := by
      have h : N = Real.sqrt n := rfl
      rw [h]
      first
        | exact Real.sqrt_pos.2 hnpos
        | exact Real.sqrt_pos_of_pos hnpos
        | positivity
    have hsne : s ≠ 0 := ne_of_gt hspos'
    have hN2 : N ^ 2 = n := by dsimp only [N]; rw [Real.sq_sqrt hnpos.le]
    have hconst : (∑ i ∈ Finset.range (r + 1), θ) = n * θ := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hS : ∑ i ∈ Finset.range (r + 1), Y i ω
        = (∑ i ∈ Finset.range (r + 1), (if X i ω = true then (1 : ℝ) else 0)) - n * θ := by
      have hsub : ∑ i ∈ Finset.range (r + 1), Y i ω
          = (∑ i ∈ Finset.range (r + 1), (if X i ω = true then (1 : ℝ) else 0))
            - (∑ i ∈ Finset.range (r + 1), θ) :=
        Finset.sum_sub_distrib (f := fun i => (if X i ω = true then (1 : ℝ) else 0))
          (g := fun _ => θ)
      rw [hsub, hconst]
    have hBv : Statlib.StatFoundation.Convergence.CLT.standardizedSum Y s (r + 1) ω
        = ((∑ i ∈ Finset.range (r + 1), (if X i ω = true then (1 : ℝ) else 0)) - n * θ) / (s * N) := by
      rw [hBval r ω, hS] <;>
        (first
          | rfl
          | simp only [show N = Real.sqrt n from rfl])
    have hnx : n * (x - θ)
        = (∑ i ∈ Finset.range (r + 1), (if X i ω = true then (1 : ℝ) else 0)) - n * θ := by
      dsimp only [x]
      field_simp <;> ring
    have hrescale : s * Statlib.StatFoundation.Convergence.CLT.standardizedSum Y s (r + 1) ω = N * (x - θ) := by
      rw [hBv, ← hnx]
      field_simp
      first
        | nlinarith [hN2]
        | (rw [hN2]; ring)
        | (ring_nf; rw [hN2]; ring)
    have hqrel : q x * (x - θ) = 2 * Real.arcsin (Real.sqrt x) - 2 * Real.arcsin (Real.sqrt θ) := by
      have hqx : q x = if x = θ then 1 / s
          else (2 * Real.arcsin (Real.sqrt x) - 2 * Real.arcsin (Real.sqrt θ)) / (x - θ) := rfl
      rw [hqx]
      by_cases hx : x = θ
      · rw [if_pos hx, hx]
        ring
      · rw [if_neg hx]
        have hxne : x - θ ≠ 0 := sub_ne_zero.mpr hx
        field_simp <;> ring
    show (s * q x) * Statlib.StatFoundation.Convergence.CLT.standardizedSum Y s (r + 1) ω
      = 2 * N * (Real.arcsin (Real.sqrt x) - Real.arcsin (Real.sqrt θ))
    calc (s * q x) * Statlib.StatFoundation.Convergence.CLT.standardizedSum Y s (r + 1) ω
        = q x * (s * Statlib.StatFoundation.Convergence.CLT.standardizedSum Y s (r + 1) ω) := by ring
      _ = q x * (N * (x - θ)) := by rw [hrescale]
      _ = N * (q x * (x - θ)) := by ring
      _ = N * (2 * Real.arcsin (Real.sqrt x) - 2 * Real.arcsin (Real.sqrt θ)) := by rw [hqrel]
      _ = 2 * N * (Real.arcsin (Real.sqrt x) - Real.arcsin (Real.sqrt θ)) := by ring
  have hstep : TendstoInDistribution
      (fun r ω => 2 * Real.sqrt (((r + 1 : ℕ) : ℝ)) *
        (Real.arcsin (Real.sqrt ((((r + 1 : ℕ) : ℝ))⁻¹ * ∑ i ∈ Finset.range (r + 1), (if X i ω = true then (1 : ℝ) else 0))) - Real.arcsin (Real.sqrt θ)))
      atTop (fun ω => 1 * Z ω) P :=
    Statlib.StatFoundation.Convergence.tendstoInDistribution_congr_left
      (X := fun r ω => (fun z : ℝ × ℝ => z.2 * z.1)
        (Statlib.StatFoundation.Convergence.CLT.standardizedSum Y s (r + 1) ω,
          s * q ((((r + 1 : ℕ) : ℝ))⁻¹ * ∑ i ∈ Finset.range (r + 1), (if X i ω = true then (1 : ℝ) else 0))))
      (fun r => Filter.Eventually.of_forall (hfact r)) hprod
  exact Statlib.StatFoundation.Convergence.tendstoInDistribution_congr_right
    (X := fun r ω => 2 * Real.sqrt (((r + 1 : ℕ) : ℝ)) *
        (Real.arcsin (Real.sqrt ((((r + 1 : ℕ) : ℝ))⁻¹ * ∑ i ∈ Finset.range (r + 1), (if X i ω = true then (1 : ℝ) else 0))) - Real.arcsin (Real.sqrt θ)))
    (Xlim := fun ω => 1 * Z ω) (Ylim := Z)
    (Filter.Eventually.of_forall fun ω => by simp) hstep
  /- @proof-region region.root.ca4e947e5eca end -/
