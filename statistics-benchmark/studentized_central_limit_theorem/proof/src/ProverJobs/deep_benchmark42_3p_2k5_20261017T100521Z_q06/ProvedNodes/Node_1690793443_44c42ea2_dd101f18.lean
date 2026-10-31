import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q06.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q06.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q06.ProvedNodes.Node_980666557_257fc9e4_2034ac47

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

set_option autoImplicit false in
theorem statopia_math_node_1690793443_44c42ea2 : ∀ {Ω : Type*} [MeasurableSpace Ω]
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
    (hX_second : ∀ i, ∫ ω, (X i ω) ^ 2 ∂P = mean ^ 2 + sigma ^ 2),
    let Xbar : ℕ → Ω → ℝ :=
      fun n ω ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, X i ω
    let U : ℕ → Ω → ℝ :=
      fun n ω ↦ Real.sqrt (n : ℝ) * (Xbar n ω - mean) / sigma
    (∀ n : ℕ, 0 < n → ∫ ω, (U n ω) ^ 2 ∂P = 1) ∧
      (∀ (K : ℝ), 0 < K → ∀ n : ℕ, 0 < n →
        P {ω | K < |U n ω|} ≤ ENNReal.ofReal (1 / K ^ 2)) := by
  /- @proof-region region.target-node.session.f43b4a79eec4848d begin -/
  intro Ω _ P _ X mean sigma hX_meas hX_indep hX_ident hmean hvar hsigma hX_memLp hX_mean hX_second
  have hInt : ∀ i, Integrable (X i) P := fun i => (hX_memLp i).integrable (by norm_num)
  have key : ∀ n : ℕ, 0 < n →
      (∫ ω, (Real.sqrt (n:ℝ) * ((n:ℝ)⁻¹ * (∑ i ∈ Finset.range n, X i ω) - mean) / sigma) ^ 2 ∂P = 1) ∧
      (∀ K : ℝ, 0 < K →
        P {ω | K < |Real.sqrt (n:ℝ) * ((n:ℝ)⁻¹ * (∑ i ∈ Finset.range n, X i ω) - mean) / sigma|} ≤
          ENNReal.ofReal (1 / K ^ 2)) := by
    intro n hn
    set V : Ω → ℝ :=
      fun ω => Real.sqrt (n:ℝ) * ((n:ℝ)⁻¹ * (∑ i ∈ Finset.range n, X i ω) - mean) / sigma with hV
    have hne : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hσ2 : sigma ^ 2 ≠ 0 := pow_ne_zero 2 hsigma.ne'
    have hprod : (n : ℝ) * sigma ^ 2 ≠ 0 := mul_ne_zero hne hσ2
    have hS_memLp : MemLp (fun ω => ∑ i ∈ Finset.range n, X i ω) 2 P :=
      memLp_finset_sum _ (fun i _ => hX_memLp i)
    have hS_aem : AEMeasurable (fun ω => ∑ i ∈ Finset.range n, X i ω) P :=
      hS_memLp.aestronglyMeasurable.aemeasurable
    have hS_int : ∫ ω, (∑ i ∈ Finset.range n, X i ω) ∂P = (n : ℝ) * mean := by
      rw [integral_finset_sum _ (fun i _ => hInt i)]
      simp [hX_mean, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hvar_i : ∀ i ∈ Finset.range n, variance (X i) P = sigma ^ 2 := by
      intro i _
      rw [variance_eq_sub (hX_memLp i)]
      simp only [Pi.pow_apply]
      rw [hX_second i, hX_mean i]
      ring
    have hvsum : variance (fun ω => ∑ i ∈ Finset.range n, X i ω) P = (n : ℝ) * sigma ^ 2 := by
      rw [show (fun ω => ∑ i ∈ Finset.range n, X i ω) = ∑ i ∈ Finset.range n, X i from by
            funext ω
            simp]
      rw [IndepFun.variance_sum (s := Finset.range n) (X := X) (μ := P)
        (fun i _ => hX_memLp i) (fun i _ j _ hij => hX_indep.indepFun hij),
        Finset.sum_congr rfl hvar_i, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hvint : ∫ ω, ((∑ i ∈ Finset.range n, X i ω) - (n : ℝ) * mean) ^ 2 ∂P
        = (n : ℝ) * sigma ^ 2 := by
      rw [← hvsum, variance_eq_integral hS_aem, hS_int]
    have hpt : ∀ ω : Ω, V ω ^ 2
        = ((n:ℝ) * sigma ^ 2)⁻¹ * ((∑ i ∈ Finset.range n, X i ω) - (n:ℝ) * mean) ^ 2 := by
      intro ω
      simp only [hV]
      have h2 : (n:ℝ)⁻¹ * (∑ i ∈ Finset.range n, X i ω) - mean
          = ((∑ i ∈ Finset.range n, X i ω) - (n:ℝ) * mean) * (n:ℝ)⁻¹ := by
        field_simp
      rw [h2, div_pow, mul_pow, Real.sq_sqrt (show (0:ℝ) ≤ (n:ℝ) by positivity)]
      field_simp
    have hcongr : ∫ ω, V ω ^ 2 ∂P
        = ∫ ω, ((n:ℝ) * sigma ^ 2)⁻¹ * ((∑ i ∈ Finset.range n, X i ω) - (n:ℝ) * mean) ^ 2 ∂P := by
      simp only [hpt]
    have hsq_eq : ∫ ω, V ω ^ 2 ∂P = 1 := by
      rw [hcongr, integral_const_mul, hvint, inv_mul_cancel₀ hprod]
    refine ⟨hsq_eq, ?_⟩
    intro K hK
    have hU2_int : Integrable (fun ω => V ω ^ 2) P := by
      have hc : MemLp (fun _ : Ω => (n:ℝ) * mean) 2 P := memLp_const ((n:ℝ) * mean)
      have hsub_memLp : MemLp (fun ω => (∑ i ∈ Finset.range n, X i ω) - (n:ℝ) * mean) 2 P :=
        hS_memLp.sub hc
      have hsq_int : Integrable (fun ω => ((∑ i ∈ Finset.range n, X i ω) - (n:ℝ) * mean) ^ 2) P :=
        hsub_memLp.integrable_sq
      have hfun : (fun ω => V ω ^ 2)
          = fun ω => ((n:ℝ) * sigma ^ 2)⁻¹ * ((∑ i ∈ Finset.range n, X i ω) - (n:ℝ) * mean) ^ 2 :=
        funext hpt
      rw [hfun]
      exact hsq_int.const_mul _
    have hf_meas : AEMeasurable (fun ω => ENNReal.ofReal (V ω ^ 2)) P :=
      ENNReal.measurable_ofReal.comp_aemeasurable hU2_int.aestronglyMeasurable.aemeasurable
    have hlin : ∫⁻ ω, ENNReal.ofReal (V ω ^ 2) ∂P = 1 := by
      rw [← ofReal_integral_eq_lintegral_ofReal hU2_int
            (Filter.Eventually.of_forall (fun ω => sq_nonneg (V ω)))]
      simp [hsq_eq]
    have hsub : {ω | K < |V ω|} ⊆ {ω | ENNReal.ofReal (K ^ 2) ≤ ENNReal.ofReal (V ω ^ 2)} := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      have hgt : K ^ 2 < V ω ^ 2 := by
        have h3 : K ^ 2 < |V ω| ^ 2 := by
          nlinarith [abs_nonneg (V ω), hω]
        rw [sq_abs] at h3
        exact h3
      exact ENNReal.ofReal_le_ofReal hgt.le
    calc P {ω | K < |V ω|}
        ≤ P {ω | ENNReal.ofReal (K ^ 2) ≤ ENNReal.ofReal (V ω ^ 2)} := measure_mono hsub
      _ ≤ (∫⁻ ω, ENNReal.ofReal (V ω ^ 2) ∂P) / ENNReal.ofReal (K ^ 2) :=
          meas_ge_le_lintegral_div hf_meas
            (ne_of_gt (ENNReal.ofReal_pos.mpr (show (0:ℝ) < K ^ 2 by positivity)))
            ENNReal.ofReal_ne_top
      _ = 1 / ENNReal.ofReal (K ^ 2) := by rw [hlin]
      _ = ENNReal.ofReal (1 / K ^ 2) := by
          rw [one_div, one_div, ENNReal.ofReal_inv_of_pos (show (0:ℝ) < K ^ 2 by positivity)]
  exact ⟨fun n hn => (key n hn).1, fun K hK n hn => (key n hn).2 K hK⟩
  /- @proof-region region.target-node.session.f43b4a79eec4848d end -/
