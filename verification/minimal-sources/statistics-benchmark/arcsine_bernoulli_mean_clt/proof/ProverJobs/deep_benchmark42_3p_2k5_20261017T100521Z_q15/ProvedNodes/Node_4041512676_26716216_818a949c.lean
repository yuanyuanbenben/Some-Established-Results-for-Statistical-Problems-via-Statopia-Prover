import Statlib.StatFoundation.BasicAnalysis.ENNRealBridge
import Statlib.StatFoundation.Convergence.AnalysisTools.ConvergenceModes
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q15.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q15.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q15.ProvedNodes.Node_3660083059_ee3ca287_a16ffa73
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q15.ProvedNodes.Node_3925726211_24458778_9ca02729


open Filter MeasureTheory ProbabilityTheory

open Filter MeasureTheory ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_4041512676_26716216 : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (θ : ℝ) (htheta_pos : 0 < θ) (htheta_lt_one : θ < 1)
    (ξ : ℕ → Ω → ℝ)
    (hY_meas : ∀ i, Measurable (fun ω => ξ i ω - θ))
    (hY_indep : iIndepFun (fun i ω => ξ i ω - θ) P)
    (hY_int : ∀ i, Integrable (fun ω => ξ i ω - θ) P)
    (hY_mean : ∀ i, ∫ ω, (ξ i ω - θ) ∂P = 0)
    (hY_var : ∀ i, ∫ ω, (ξ i ω - θ) ^ 2 ∂P = θ * (1 - θ))
    (hY_sq_int : ∀ i, Integrable (fun ω => (ξ i ω - θ) ^ 2) P)
    (hY_bound : ∀ i (ω : Ω), |ξ i ω - θ| ≤ 1),
    (∀ r : ℕ,
        ∫ ω, ((((r + 1 : ℕ) : ℝ)⁻¹ * (∑ i ∈ Finset.range (r + 1), ξ i ω)) - θ) ^ 2 ∂P
          = θ * (1 - θ) / ((r + 1 : ℕ) : ℝ))
      ∧ TendstoInMeasure P
          (fun (r : ℕ) (ω : Ω) =>
            ((r + 1 : ℕ) : ℝ)⁻¹ * ∑ i ∈ Finset.range (r + 1), ξ i ω)
          atTop (fun _ => θ) := by
  /- @proof-region region.target-node.session.4a9fdd2bf2f5dfa7 begin -/
  intro Ω _ P _ θ htheta_pos htheta_lt_one ξ hY_meas hY_indep hY_int hY_mean hY_var hY_sq_int hY_bound
  have hpair_int : ∀ i j : ℕ, Integrable (fun ω => (ξ i ω - θ) * (ξ j ω - θ)) P := by
    intro i j
    refine MeasureTheory.Integrable.of_bound ((hY_meas i).mul (hY_meas j)).aestronglyMeasurable (1 : ℝ) ?_
    filter_upwards with ω
    have h := mul_le_mul (hY_bound i ω) (hY_bound j ω) (abs_nonneg (ξ j ω - θ)) (zero_le_one : (0 : ℝ) ≤ 1)
    rw [Real.norm_eq_abs, abs_mul]
    simpa using h
  have hsum_int : ∀ (s : Finset ℕ) (g : ℕ → Ω → ℝ), (∀ i, Integrable (g i) P) →
      Integrable (fun ω => ∑ i ∈ s, g i ω) P := by
    intro s g hg
    classical
    induction s using Finset.induction_on with
    | empty => simpa using (MeasureTheory.integrable_zero (μ := P) : Integrable (fun _ : Ω => (0 : ℝ)) P)
    | insert a s ha ih =>
        simp only [Finset.sum_insert ha]
        exact (hg a).add ih
  have hdiag : ∀ i : ℕ, ∫ ω, (ξ i ω - θ) * (ξ i ω - θ) ∂P = θ * (1 - θ) := by
    intro i
    have h : ∫ ω, (ξ i ω - θ) * (ξ i ω - θ) ∂P = ∫ ω, (ξ i ω - θ) ^ 2 ∂P := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with ω
      ring
    rw [h, hY_var i]
  have hoff : ∀ i j : ℕ, i ≠ j → ∫ ω, (ξ i ω - θ) * (ξ j ω - θ) ∂P = 0 := by
    intro i j hij
    have hindep : (fun ω => ξ i ω - θ) ⟂ᵢ[P] (fun ω => ξ j ω - θ) := hY_indep.indepFun hij
    rw [ProbabilityTheory.IndepFun.integral_fun_mul_eq_mul_integral (X := fun ω => ξ i ω - θ)
      (Y := fun ω => ξ j ω - θ) hindep (hY_meas i).aestronglyMeasurable
      (hY_meas j).aestronglyMeasurable, hY_mean i, hY_mean j, mul_zero]
  have hpt : ∀ (r : ℕ) (ω : Ω), ((((r + 1 : ℕ) : ℝ)⁻¹ * (∑ i ∈ Finset.range (r + 1), ξ i ω)) - θ)
      = (((r + 1 : ℕ) : ℝ)⁻¹ * ∑ i ∈ Finset.range (r + 1), (ξ i ω - θ)) := by
    intro r ω
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hn : (((r + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    field_simp
  have hYexp : ∀ (r : ℕ) (ω : Ω), ((∑ i ∈ Finset.range (r + 1), (ξ i ω - θ))) ^ 2
      = ∑ i ∈ Finset.range (r + 1), ∑ j ∈ Finset.range (r + 1), (ξ i ω - θ) * (ξ j ω - θ) := by
    intro r ω
    rw [pow_two, Finset.sum_mul_sum]
  have hsq_int : ∀ r : ℕ,
      Integrable (fun ω => ((((r + 1 : ℕ) : ℝ)⁻¹ * (∑ i ∈ Finset.range (r + 1), ξ i ω)) - θ) ^ 2) P := by
    intro r
    have hbase : Integrable (fun ω => ∑ i ∈ Finset.range (r + 1),
        ∑ j ∈ Finset.range (r + 1), (ξ i ω - θ) * (ξ j ω - θ)) P :=
      hsum_int _ _ (fun i => hsum_int _ _ (fun j => hpair_int i j))
    refine (hbase.const_mul ((((r + 1 : ℕ) : ℝ)⁻¹) ^ 2)).congr ?_
    filter_upwards with ω
    rw [hpt r ω, mul_pow, hYexp r ω]
  have hsecond : ∀ r : ℕ,
      ∫ ω, ((((r + 1 : ℕ) : ℝ)⁻¹ * (∑ i ∈ Finset.range (r + 1), ξ i ω)) - θ) ^ 2 ∂P
        = θ * (1 - θ) / (((r + 1 : ℕ) : ℝ)) := by
    intro r
    have hfun : (fun ω => ((((r + 1 : ℕ) : ℝ)⁻¹ * (∑ i ∈ Finset.range (r + 1), ξ i ω)) - θ) ^ 2)
        = (fun ω => ((((r + 1 : ℕ) : ℝ)⁻¹) ^ 2 * ∑ i ∈ Finset.range (r + 1),
            ∑ j ∈ Finset.range (r + 1), (ξ i ω - θ) * (ξ j ω - θ))) := by
      funext ω
      rw [hpt r ω, mul_pow, hYexp r ω]
    have hinner : ∀ i ∈ Finset.range (r + 1),
        ∑ j ∈ Finset.range (r + 1), ∫ ω, (ξ i ω - θ) * (ξ j ω - θ) ∂P = θ * (1 - θ) := by
      intro i hi
      have hstep : ∑ j ∈ Finset.range (r + 1), ∫ ω, (ξ i ω - θ) * (ξ j ω - θ) ∂P
          = ∫ ω, (ξ i ω - θ) * (ξ i ω - θ) ∂P := by
        refine Finset.sum_eq_single (a := i) ?_ ?_
        · intro j hj hji
          exact hoff i j (fun h => hji h.symm)
        · intro hi'
          exact absurd hi hi'
      rw [hstep]
      exact hdiag i
    have hdbl : ∫ ω, ∑ i ∈ Finset.range (r + 1), ∑ j ∈ Finset.range (r + 1),
          (ξ i ω - θ) * (ξ j ω - θ) ∂P
        = ∑ i ∈ Finset.range (r + 1), ∑ j ∈ Finset.range (r + 1),
            ∫ ω, (ξ i ω - θ) * (ξ j ω - θ) ∂P := by
      rw [MeasureTheory.integral_finset_sum (Finset.range (r + 1))
        (fun i _ => hsum_int _ _ (fun j => hpair_int i j))]
      exact Finset.sum_congr rfl (fun i _ =>
        MeasureTheory.integral_finset_sum (Finset.range (r + 1)) (fun j _ => hpair_int i j))
    rw [hfun, MeasureTheory.integral_const_mul, hdbl, Finset.sum_congr rfl hinner,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hn : (((r + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    field_simp
  refine ⟨hsecond, ?_⟩
  rw [Statlib.StatFoundation.Convergence.tendstoInMeasure_iff_measureReal_norm]
  intro ε hε
  have hset : ∀ r : ℕ, {x : Ω | ε ≤ ‖(((r + 1 : ℕ) : ℝ)⁻¹ * ∑ i ∈ Finset.range (r + 1), ξ i x) - θ‖}
      = {x : Ω | ε ^ 2 ≤ ((((r + 1 : ℕ) : ℝ)⁻¹ * ∑ i ∈ Finset.range (r + 1), ξ i x) - θ) ^ 2} := by
    intro r
    ext ω
    simp only [Set.mem_setOf_eq, Real.norm_eq_abs]
    constructor
    · intro h
      have h2 : ε ^ 2 ≤ |(((r + 1 : ℕ) : ℝ)⁻¹ * ∑ i ∈ Finset.range (r + 1), ξ i ω) - θ| ^ 2 := by
        nlinarith [abs_nonneg ((((r + 1 : ℕ) : ℝ)⁻¹ * ∑ i ∈ Finset.range (r + 1), ξ i ω) - θ)]
      simpa [sq_abs] using h2
    · intro h
      have h2 : ε ^ 2 ≤ |(((r + 1 : ℕ) : ℝ)⁻¹ * ∑ i ∈ Finset.range (r + 1), ξ i ω) - θ| ^ 2 := by
        simpa [sq_abs] using h
      nlinarith [abs_nonneg ((((r + 1 : ℕ) : ℝ)⁻¹ * ∑ i ∈ Finset.range (r + 1), ξ i ω) - θ)]
  simp only [hset]
  have hbnd : ∀ r : ℕ,
      P.real {x : Ω | ε ^ 2 ≤ ((((r + 1 : ℕ) : ℝ)⁻¹ * ∑ i ∈ Finset.range (r + 1), ξ i x) - θ) ^ 2}
        ≤ θ * (1 - θ) / (((r + 1 : ℕ) : ℝ) * ε ^ 2) := by
    intro r
    have hnonneg : 0 ≤ᶠ[ae P] (fun x : Ω =>
        ((((r + 1 : ℕ) : ℝ)⁻¹ * ∑ i ∈ Finset.range (r + 1), ξ i x) - θ) ^ 2) :=
      Filter.Eventually.of_forall (fun x => sq_nonneg _)
    have hcheb := Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.measReal_ge_le_integral_div P
      (fun x : Ω => ((((r + 1 : ℕ) : ℝ)⁻¹ * ∑ i ∈ Finset.range (r + 1), ξ i x) - θ) ^ 2)
      hnonneg (hsq_int r) (ε ^ 2) (by positivity)
    rw [hsecond r] at hcheb
    exact le_trans hcheb (le_of_eq (div_div _ _ _))
  have hnn : ∀ r : ℕ,
      (0 : ℝ) ≤ P.real {x : Ω | ε ^ 2 ≤ ((((r + 1 : ℕ) : ℝ)⁻¹ * ∑ i ∈ Finset.range (r + 1), ξ i x) - θ) ^ 2} := by
    intro r
    exact ENNReal.toReal_nonneg
  have hB : Tendsto (fun r : ℕ => θ * (1 - θ) / (((r + 1 : ℕ) : ℝ) * ε ^ 2)) atTop (nhds 0) := by
    have hnat : Tendsto (fun r : ℕ => ((r + 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    have hinv : Tendsto (fun r : ℕ => (((r + 1 : ℕ) : ℝ))⁻¹) atTop (nhds 0) := by
      simpa using hnat.inv_tendsto_atTop
    have hmul := hinv.const_mul (θ * (1 - θ) / ε ^ 2)
    have hfun : (fun r : ℕ => θ * (1 - θ) / (((r + 1 : ℕ) : ℝ) * ε ^ 2))
        = (fun r : ℕ => (θ * (1 - θ) / ε ^ 2) * (((r + 1 : ℕ) : ℝ))⁻¹) := by
      funext r
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
      ring
    rw [hfun]
    simpa using hmul
  exact squeeze_zero hnn hbnd hB
  /- @proof-region region.target-node.session.4a9fdd2bf2f5dfa7 end -/
