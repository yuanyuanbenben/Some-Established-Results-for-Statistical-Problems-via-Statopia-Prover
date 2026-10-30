import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q06.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q06.Base

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

set_option autoImplicit false in
theorem statopia_math_node_460667716_1894c750 : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : ℕ → Ω → ℝ) (W : ℕ → Ω → ℝ)
    (hU_meas : ∀ n, Measurable (U n))
    (hW_meas : ∀ n, Measurable (W n))
    (hU_mem : ∀ n, 1 ≤ n → MemLp (U n) 2 P)
    (hU_second : ∀ n, 1 ≤ n → ∫ ω, (U n ω) ^ 2 ∂P ≤ 1)
    (hU_clt : ∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n => ∫ ω, f (U n ω) ∂P) atTop
        (𝓝 (∫ x, f x ∂(gaussianReal 0 1))))
    (hW_prob : ∀ eps : ℝ, 0 < eps →
      Tendsto (fun n => P {ω | eps ≤ |W n ω - 1|}) atTop (𝓝 0)),
    let Q : ℕ → Ω → ℝ := fun n ω => if 0 < W n ω then U n ω / W n ω else 0
    ∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n => ∫ ω, f (Q n ω) ∂P) atTop
        (𝓝 (∫ x, f x ∂(gaussianReal 0 1))) := by
  /- @proof-region region.target-node.session.e8cb01af3efa176b begin -/
  intro Ω instΩ P instP U W hU_meas hW_meas hU_mem hU_second hU_clt hW_prob Q f
  have hQdef : ∀ n ω, Q n ω = if 0 < W n ω then U n ω / W n ω else 0 := fun n ω => rfl
  obtain ⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, |f x| ≤ M :=
    ⟨‖f‖, norm_nonneg f, fun x => by
      simpa using BoundedContinuousFunction.norm_coe_le_norm (f := f) x⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K, hK1, hK⟩ : ∃ K : ℝ, 1 ≤ K ∧ 6 * M / ε < K ^ 2 := by
    obtain ⟨N, hN⟩ := exists_nat_gt (max (6 * M / ε) 1)
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
      have h : (1 : ℝ) < (N : ℝ) := lt_of_le_of_lt (le_max_right (6 * M / ε) 1) hN
      linarith
    have hN2 : 6 * M / ε < (N : ℝ) := lt_of_le_of_lt (le_max_left (6 * M / ε) 1) hN
    have hsq : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith [hN1, sq_nonneg ((N : ℝ) - 1)]
    exact ⟨(N : ℝ), hN1, lt_of_lt_of_le hN2 hsq⟩
  have hKpos : (0 : ℝ) < K := by linarith
  have hK2pos : (0 : ℝ) < K ^ 2 := by nlinarith
  have hMK : 2 * M / K ^ 2 < ε / 3 := by
    have h6 : 6 * M < ε * K ^ 2 := by
      have h := (div_lt_iff₀ hε).mp hK
      nlinarith
    rw [div_lt_iff₀ hK2pos]
    nlinarith
  have hcpt : IsCompact (Set.Icc (-(2 * K + 2)) (2 * K + 2)) := isCompact_Icc
  haveI : CompactSpace (Set.Icc (-(2 * K + 2)) (2 * K + 2)) := isCompact_iff_compactSpace.mp hcpt
  have huc : UniformContinuous (fun p : Set.Icc (-(2 * K + 2)) (2 * K + 2) => f (p : ℝ)) :=
    CompactSpace.uniformContinuous_of_continuous (f.continuous.comp continuous_subtype_val)
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := Metric.uniformContinuous_iff.mp huc (ε / 3) (by linarith)
  set δ : ℝ := min δ₀ (1 / (2 * K)) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact lt_min hδ₀pos (div_pos one_pos (by linarith))
  have hδle : δ ≤ δ₀ := by
    rw [hδdef]
    exact min_le_left _ _
  have hδleK : δ ≤ 1 / (2 * K) := by
    rw [hδdef]
    exact min_le_right _ _
  set δ' : ℝ := min (1 / 2) (δ / (2 * K)) with hδ'def
  have hδ'pos : 0 < δ' := by
    rw [hδ'def]
    exact lt_min (by norm_num) (div_pos hδpos (by linarith))
  have hδ'1 : δ' ≤ 1 / 2 := by
    rw [hδ'def]
    exact min_le_left _ _
  have hδ'2 : δ' ≤ δ / (2 * K) := by
    rw [hδ'def]
    exact min_le_right _ _
  set G : ℕ → Set Ω :=
    fun n => {ω | |U n ω| < K ∧ 1 / 2 ≤ W n ω ∧ 2 * K * |1 - W n ω| < δ} with hGdef
  have hgood : ∀ n ω, ω ∈ G n → |f (Q n ω) - f (U n ω)| ≤ ε / 3 := by
    intro n ω hω
    rw [hGdef] at hω
    simp only [Set.mem_setOf_eq] at hω
    obtain ⟨hU, hW, hWδ⟩ := hω
    have hWpos : 0 < W n ω := by linarith
    have hQ : Q n ω = U n ω / W n ω := by
      rw [hQdef n ω, if_pos hWpos]
    have hdiff : |Q n ω - U n ω| < δ := by
      rw [hQ]
      have h1 : U n ω / W n ω - U n ω = U n ω * (1 - W n ω) / W n ω := by
        have hWne : W n ω ≠ 0 := ne_of_gt hWpos
        field_simp
      rw [h1, abs_div, abs_mul, abs_of_pos hWpos]
      rw [div_lt_iff₀ hWpos]
      have hstep : |U n ω| * |1 - W n ω| ≤ 2 * K * |1 - W n ω| * W n ω := by
        have ha : |U n ω| * |1 - W n ω| ≤ K * |1 - W n ω| :=
          mul_le_mul_of_nonneg_right (le_of_lt hU) (abs_nonneg _)
        have hb : K * |1 - W n ω| ≤ 2 * K * |1 - W n ω| * W n ω := by
          have h3 : (1 : ℝ) ≤ 2 * W n ω := by linarith
          have h0 : (0 : ℝ) ≤ K * |1 - W n ω| :=
            mul_nonneg (le_of_lt hKpos) (abs_nonneg _)
          nlinarith [h3, h0]
        linarith
      nlinarith [hstep, hWδ, hWpos]
    have htri : |Q n ω| ≤ |U n ω| + |Q n ω - U n ω| := by
      have h : U n ω + (Q n ω - U n ω) = Q n ω := by ring
      calc |Q n ω| = |U n ω + (Q n ω - U n ω)| := by rw [h]
        _ ≤ |U n ω| + |Q n ω - U n ω| := abs_add_le _ _
    have hQ2 : |Q n ω| ≤ 2 * K + 2 := by
      have hδ1 : δ ≤ 1 := by
        have h : 1 / (2 * K) ≤ 1 := by
          rw [div_le_one (by linarith : (0 : ℝ) < 2 * K)]
          linarith
        linarith
      nlinarith [htri, hU, hdiff, hδ1, hK1]
    have hm1 : U n ω ∈ Set.Icc (-(2 * K + 2)) (2 * K + 2) :=
      ⟨by linarith [neg_abs_le (U n ω)], by linarith [le_abs_self (U n ω)]⟩
    have hm2 : Q n ω ∈ Set.Icc (-(2 * K + 2)) (2 * K + 2) :=
      ⟨by linarith [neg_abs_le (Q n ω)], by linarith [le_abs_self (Q n ω)]⟩
    have hdist :
        dist (⟨U n ω, hm1⟩ : Set.Icc (-(2 * K + 2)) (2 * K + 2)) ⟨Q n ω, hm2⟩ < δ₀ := by
      have heq :
          dist (⟨U n ω, hm1⟩ : Set.Icc (-(2 * K + 2)) (2 * K + 2)) ⟨Q n ω, hm2⟩
            = |U n ω - Q n ω| := by
        rw [Subtype.dist_eq, Real.dist_eq]
      rw [heq, abs_sub_comm]
      exact lt_of_lt_of_le hdiff hδle
    have hd := hδ₀ hdist
    rw [Real.dist_eq, abs_sub_comm] at hd
    exact le_of_lt hd
  have hWreal : Tendsto (fun n => P.real {ω | δ' ≤ |W n ω - 1|}) atTop (𝓝 0) := by
    have hcont : ContinuousAt ENNReal.toReal (0 : ENNReal) := ENNReal.continuousAt_toReal (by simp)
    have h := hcont.tendsto.comp (hW_prob δ' hδ'pos)
    simpa [MeasureTheory.measureReal_def] using h
  have hPb : Tendsto (fun n => 2 * M * P.real {ω | δ' ≤ |W n ω - 1|}) atTop (𝓝 0) := by
    simpa using hWreal.const_mul (2 * M)
  have hCLT :
      Tendsto (fun n => |∫ ω, f (U n ω) ∂P - ∫ x, f x ∂(gaussianReal 0 1)|) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => ∫ ω, f (U n ω) ∂P - ∫ x, f x ∂(gaussianReal 0 1))
        atTop (𝓝 0) := by
      simpa using (hU_clt f).sub_const (∫ x, f x ∂(gaussianReal 0 1))
    simpa using h1.abs
  have hint : ∀ n, 1 ≤ n →
      |∫ ω, f (Q n ω) ∂P - ∫ x, f x ∂(gaussianReal 0 1)| ≤
        ε / 3 + 2 * M / K ^ 2 + 2 * M * P.real {ω | δ' ≤ |W n ω - 1|} +
          |∫ ω, f (U n ω) ∂P - ∫ x, f x ∂(gaussianReal 0 1)| := by
    intro n hn
    have hif : Measurable (fun ω : Ω => if 0 < W n ω then U n ω / W n ω else 0) :=
      Measurable.ite ((hW_meas n) measurableSet_Ioi)
        ((hU_meas n).div (hW_meas n)) measurable_const
    have hfQm : Measurable fun ω => f (Q n ω) := f.continuous.measurable.comp hif
    have hfUm : Measurable fun ω => f (U n ω) := f.continuous.measurable.comp (hU_meas n)
    have hIntQ : Integrable (fun ω => f (Q n ω)) P := by
      refine Integrable.of_bound hfQm.aestronglyMeasurable M ?_
      filter_upwards with ω
      simpa using hM (Q n ω)
    have hIntU : Integrable (fun ω => f (U n ω)) P := by
      refine Integrable.of_bound hfUm.aestronglyMeasurable M ?_
      filter_upwards with ω
      simpa using hM (U n ω)
    have hAnorm := MeasureTheory.norm_integral_le_integral_norm (μ := P)
      (f := fun ω => f (Q n ω) - f (U n ω))
    have hA : |∫ ω, f (Q n ω) ∂P - ∫ ω, f (U n ω) ∂P|
        ≤ ∫ ω, |f (Q n ω) - f (U n ω)| ∂P := by
      rw [← MeasureTheory.integral_sub hIntQ hIntU]
      simpa using hAnorm
    have hGm : MeasurableSet (G n) := by
      have h1 : MeasurableSet {ω : Ω | |U n ω| < K} := (hU_meas n).abs measurableSet_Iio
      have h2 : MeasurableSet {ω : Ω | (1 : ℝ) / 2 ≤ W n ω} := (hW_meas n) measurableSet_Ici
      have hm : Measurable fun ω => 2 * K * |1 - W n ω| :=
        measurable_const.mul ((measurable_const.sub (hW_meas n)).abs)
      have h3 : MeasurableSet {ω : Ω | 2 * K * |1 - W n ω| < δ} := hm measurableSet_Iio
      rw [hGdef]
      exact h1.inter (h2.inter h3)
    have hbd : ∀ ω, |f (Q n ω) - f (U n ω)| ≤ 2 * M := by
      intro ω
      have h5 : |f (Q n ω) - f (U n ω)| ≤ |f (Q n ω)| + |f (U n ω)| := by
        simpa [sub_eq_add_neg] using abs_add_le (f (Q n ω)) (-(f (U n ω)))
      have h2 := hM (Q n ω)
      have h3 := hM (U n ω)
      linarith
    have hIntg : Integrable (fun ω => |f (Q n ω) - f (U n ω)|) P := by
      simpa using (hIntQ.sub hIntU).abs
    have hsplit : ∫ ω, |f (Q n ω) - f (U n ω)| ∂P
        = ∫ ω in G n, |f (Q n ω) - f (U n ω)| ∂P
          + ∫ ω in (G n)ᶜ, |f (Q n ω) - f (U n ω)| ∂P :=
      (MeasureTheory.integral_add_compl hGm hIntg).symm
    have hIntgG : Integrable (fun ω => |f (Q n ω) - f (U n ω)|) (P.restrict (G n)) :=
      hIntg.integrableOn
    have hIntgGc : Integrable (fun ω => |f (Q n ω) - f (U n ω)|) (P.restrict ((G n)ᶜ)) :=
      hIntg.integrableOn
    have hb1 : ∫ ω in G n, |f (Q n ω) - f (U n ω)| ∂P ≤ ∫ ω in G n, (ε / 3 : ℝ) ∂P := by
      refine MeasureTheory.integral_mono_ae hIntgG (integrable_const (ε / 3)) ?_
      have key : ∀ᵐ ω ∂(P.restrict (G n)), |f (Q n ω) - f (U n ω)| ≤ ε / 3 := by
        rw [MeasureTheory.ae_restrict_iff' hGm]
        exact Filter.Eventually.of_forall (fun ω hω => hgood n ω hω)
      exact key
    have hb2 : ∫ ω in (G n)ᶜ, |f (Q n ω) - f (U n ω)| ∂P
        ≤ ∫ ω in (G n)ᶜ, (2 * M : ℝ) ∂P := by
      refine MeasureTheory.integral_mono_ae hIntgGc (integrable_const (2 * M)) ?_
      have key : ∀ᵐ ω ∂(P.restrict ((G n)ᶜ)), |f (Q n ω) - f (U n ω)| ≤ 2 * M := by
        rw [MeasureTheory.ae_restrict_iff' hGm.compl]
        exact Filter.Eventually.of_forall (fun ω _ => hbd ω)
      exact key
    have hv1 : ∫ ω in G n, (ε / 3 : ℝ) ∂P = P.real (G n) * (ε / 3) := by
      rw [MeasureTheory.setIntegral_const, smul_eq_mul]
    have hv2 : ∫ ω in (G n)ᶜ, (2 * M : ℝ) ∂P = P.real ((G n)ᶜ) * (2 * M) := by
      rw [MeasureTheory.setIntegral_const, smul_eq_mul]
    have hP1 : P.real (G n) ≤ 1 := by
      have h := MeasureTheory.measureReal_mono (μ := P) (Set.subset_univ (G n))
      simpa using h
    have hval : ∫ ω, |f (Q n ω) - f (U n ω)| ∂P ≤ ε / 3 + 2 * M * P.real ((G n)ᶜ) := by
      rw [hsplit]
      have hstep1 : ∫ ω in G n, |f (Q n ω) - f (U n ω)| ∂P ≤ P.real (G n) * (ε / 3) := by
        rw [← hv1]
        exact hb1
      have hstep2 :
          ∫ ω in (G n)ᶜ, |f (Q n ω) - f (U n ω)| ∂P ≤ P.real ((G n)ᶜ) * (2 * M) := by
        rw [← hv2]
        exact hb2
      have hstep3 : P.real (G n) * (ε / 3) ≤ 1 * (ε / 3) :=
        mul_le_mul_of_nonneg_right hP1 (by linarith)
      linarith
    have hbad : P.real ((G n)ᶜ) ≤ 1 / K ^ 2 + P.real {ω | δ' ≤ |W n ω - 1|} := by
      have hsub : (G n)ᶜ ⊆ {ω | K ^ 2 ≤ (U n ω) ^ 2} ∪ {ω | δ' ≤ |W n ω - 1|} := by
        intro ω hω
        rw [hGdef] at hω
        simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_and_or, not_lt, not_le] at hω
        simp only [Set.mem_union, Set.mem_setOf_eq]
        rcases hω with h | h | h
        · refine Or.inl ?_
          rw [sq_le_sq, abs_of_pos hKpos]
          exact h
        · refine Or.inr ?_
          have h1 : W n ω - 1 < 0 := by linarith
          rw [abs_of_neg h1]
          linarith
        · refine Or.inr ?_
          have hK2 : (0 : ℝ) < 2 * K := by linarith
          have h2 : δ / (2 * K) ≤ |1 - W n ω| := by
            rw [div_le_iff₀ hK2]
            nlinarith
          rw [abs_sub_comm]
          linarith
      have hmono := MeasureTheory.measureReal_mono (μ := P) hsub
      have hunion := MeasureTheory.measureReal_union_le (μ := P)
        {ω | K ^ 2 ≤ (U n ω) ^ 2} {ω | δ' ≤ |W n ω - 1|}
      have hmarkov : P.real {ω | K ^ 2 ≤ (U n ω) ^ 2} ≤ 1 / K ^ 2 := by
        have hmar : K ^ 2 * P.real {ω | K ^ 2 ≤ (U n ω) ^ 2} ≤ ∫ ω, (U n ω) ^ 2 ∂P :=
          MeasureTheory.mul_meas_ge_le_integral_of_nonneg
            (μ := P) (f := fun ω => (U n ω) ^ 2)
            (Filter.Eventually.of_forall (fun ω => sq_nonneg (U n ω)))
            ((hU_mem n hn).integrable_sq) (K ^ 2)
        have h2 := hU_second n hn
        rw [le_div_iff₀ hK2pos]
        linarith
      linarith
    have hmul :
        2 * M * P.real ((G n)ᶜ) ≤
          2 * M / K ^ 2 + 2 * M * P.real {ω | δ' ≤ |W n ω - 1|} := by
      have h2M : (0 : ℝ) ≤ 2 * M := by linarith
      have h := mul_le_mul_of_nonneg_left hbad h2M
      calc 2 * M * P.real ((G n)ᶜ)
          ≤ 2 * M * (1 / K ^ 2 + P.real {ω | δ' ≤ |W n ω - 1|}) := h
        _ = 2 * M / K ^ 2 + 2 * M * P.real {ω | δ' ≤ |W n ω - 1|} := by ring
    have htri2 : |∫ ω, f (Q n ω) ∂P - ∫ x, f x ∂(gaussianReal 0 1)|
        ≤ |∫ ω, f (Q n ω) ∂P - ∫ ω, f (U n ω) ∂P|
          + |∫ ω, f (U n ω) ∂P - ∫ x, f x ∂(gaussianReal 0 1)| := by
      have h : ∫ ω, f (Q n ω) ∂P - ∫ x, f x ∂(gaussianReal 0 1)
          = (∫ ω, f (Q n ω) ∂P - ∫ ω, f (U n ω) ∂P)
            + (∫ ω, f (U n ω) ∂P - ∫ x, f x ∂(gaussianReal 0 1)) := by ring
      rw [h]
      exact abs_add_le _ _
    linarith [hA, hval, hmul, htri2]
  have hbound : ∀ᶠ n in atTop,
      dist (∫ ω, f (Q n ω) ∂P) (∫ x, f x ∂(gaussianReal 0 1)) < ε := by
    have hb : ∀ᶠ n in atTop, 2 * M * P.real {ω | δ' ≤ |W n ω - 1|} < ε / 6 :=
      hPb.eventually (Iio_mem_nhds (by linarith))
    have hc : ∀ᶠ n in atTop,
        |∫ ω, f (U n ω) ∂P - ∫ x, f x ∂(gaussianReal 0 1)| < ε / 6 :=
      hCLT.eventually (Iio_mem_nhds (by linarith))
    filter_upwards [hb, hc, eventually_ge_atTop 1] with n hbn hcn hn1
    have h1 := hint n hn1
    have hsmall : ε / 3 + 2 * M / K ^ 2 + 2 * M * P.real {ω | δ' ≤ |W n ω - 1|} +
        |∫ ω, f (U n ω) ∂P - ∫ x, f x ∂(gaussianReal 0 1)| < ε := by
      have e1 : ε / 3 + 2 * M / K ^ 2 + 2 * M * P.real {ω | δ' ≤ |W n ω - 1|} +
          |∫ ω, f (U n ω) ∂P - ∫ x, f x ∂(gaussianReal 0 1)|
          < ε / 3 + ε / 3 + ε / 6 + ε / 6 := by
        linarith only [hMK, hbn, hcn]
      have e2 : ε / 3 + ε / 3 + ε / 6 + ε / 6 = ε := by ring
      linarith only [e1, e2]
    rw [Real.dist_eq]
    exact lt_of_le_of_lt h1 hsmall
  exact eventually_atTop.mp hbound

  /- @proof-region region.target-node.session.e8cb01af3efa176b end -/
