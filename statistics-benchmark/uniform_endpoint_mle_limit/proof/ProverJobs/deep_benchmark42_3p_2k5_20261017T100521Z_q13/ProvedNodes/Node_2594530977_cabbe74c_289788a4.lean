import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q13.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q13.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q13.ProvedNodes.Node_2623459540_991fa23d_0292b80c
open Filter MeasureTheory ProbabilityTheory
open scoped Topology

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

set_option autoImplicit false in
theorem statopia_math_node_2594530977_cabbe74c : ∀ (mu : ℕ → Measure ℝ) (hmu : ∀ r : ℕ, IsProbabilityMeasure (mu r))
    (nu : Measure ℝ) (hnu : IsProbabilityMeasure nu)
    (hconv : ∀ t : ℝ,
      Tendsto (fun r : ℕ => mu r (Set.Iic t)) atTop (𝓝 (nu (Set.Iic t)))),
    @Tendsto ℕ (ProbabilityMeasure ℝ)
      (fun r : ℕ => (⟨mu r, hmu r⟩ : ProbabilityMeasure ℝ)) atTop
      (@nhds (ProbabilityMeasure ℝ)
        Statlib.StatFoundation.Convergence.instTopologicalSpace_ProbabilityMeasure_Real
        (⟨nu, hnu⟩ : ProbabilityMeasure ℝ)) := by
  /- @proof-region region.target-node.session.4fd4a37cd8d59600 begin -/
  intro mu hmu nu hnu hconv
  refine (MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto (F := atTop)
    (μs := fun r => (⟨mu r, hmu r⟩ : ProbabilityMeasure ℝ)) (μ := ⟨nu, hnu⟩)).mpr ?_
  intro f
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hcoeν : ((↑(⟨nu, hnu⟩ : ProbabilityMeasure ℝ) : Measure ℝ)) = nu := rfl
  have hF : ∀ t : ℝ, Tendsto (fun r : ℕ => (mu r).real (Set.Iic t)) atTop (𝓝 ((nu).real (Set.Iic t))) := by
    intro t
    have h := (ENNReal.tendsto_toReal (MeasureTheory.measure_ne_top nu (Set.Iic t))).comp (hconv t)
    simpa [MeasureTheory.Measure.real] using h
  have hcompl : ∀ (ρ : Measure ℝ), IsProbabilityMeasure ρ → ∀ t : ℝ,
      ρ.real (Set.Ioi t) = 1 - ρ.real (Set.Iic t) := by
    intro ρ hρ t
    have hcoe : Set.Ioi t = (Set.Iic t)ᶜ := by
      ext x
      simp only [Set.mem_Ioi, Set.mem_compl_iff, Set.mem_Iic, not_le]
    simp only [MeasureTheory.Measure.real]
    rw [hcoe, MeasureTheory.measure_compl measurableSet_Iic (MeasureTheory.measure_ne_top ρ (Set.Iic t))]
    rw [ENNReal.toReal_sub_of_le (MeasureTheory.measure_mono (Set.subset_univ _))
      (MeasureTheory.measure_ne_top ρ Set.univ)]
    rw [MeasureTheory.measure_univ]
    norm_num
  have htail_lo : ∀ η' : ℝ, 0 < η' → ∃ T : ℝ, 0 ≤ T ∧ nu.real (Set.Iic (-T)) < η' := by
    intro η' hη'
    have hmono : Antitone (fun n : ℕ => (Set.Iic (-(n:ℝ)) : Set ℝ)) := by
      intro m n hmn x hx
      simp only [Set.mem_Iic] at hx ⊢
      have hmn' : (m:ℝ) ≤ (n:ℝ) := by exact_mod_cast hmn
      linarith
    have hlim := MeasureTheory.tendsto_measure_iInter_atTop
      (s := fun n : ℕ => (Set.Iic (-(n:ℝ)) : Set ℝ))
      (fun n => measurableSet_Iic.nullMeasurableSet) hmono ⟨0, MeasureTheory.measure_ne_top nu _⟩
    have hempty : (⋂ n : ℕ, (Set.Iic (-(n:ℝ)) : Set ℝ)) = ∅ := by
      apply le_antisymm _ (Set.empty_subset _)
      intro x hx
      rw [Set.mem_iInter] at hx
      obtain ⟨n, hn⟩ := exists_nat_gt (-x)
      exact absurd (hx n) (by simp only [Set.mem_Iic]; linarith)
    rw [hempty, MeasureTheory.measure_empty] at hlim
    have hreal : Tendsto (fun n : ℕ => (nu (Set.Iic (-(n:ℝ)))).toReal) atTop (𝓝 0) := by
      have h := (ENNReal.tendsto_toReal (by simp : (0:ENNReal) ≠ ⊤)).comp hlim
      simpa [Function.comp] using h
    have hev : ∀ᶠ n : ℕ in atTop, (nu (Set.Iic (-(n:ℝ)))).toReal < η' := by
      have h2 := (Metric.tendsto_nhds.1 hreal) η' hη'
      filter_upwards [h2] with n hn
      rw [Real.dist_eq, sub_zero] at hn
      rwa [abs_of_nonneg ENNReal.toReal_nonneg] at hn
    obtain ⟨n, hn⟩ := Filter.eventually_atTop.1 hev
    refine ⟨(n:ℝ), Nat.cast_nonneg n, ?_⟩
    simp only [MeasureTheory.Measure.real]
    exact hn n le_rfl
  have htail_hi : ∀ η' : ℝ, 0 < η' → ∃ T : ℝ, 0 ≤ T ∧ nu.real (Set.Ioi T) < η' := by
    intro η' hη'
    have hmono : Antitone (fun n : ℕ => (Set.Ioi (n:ℝ) : Set ℝ)) := by
      intro m n hmn x hx
      simp only [Set.mem_Ioi] at hx ⊢
      have hmn' : (m:ℝ) ≤ (n:ℝ) := by exact_mod_cast hmn
      linarith
    have hlim := MeasureTheory.tendsto_measure_iInter_atTop
      (s := fun n : ℕ => (Set.Ioi (n:ℝ) : Set ℝ))
      (fun n => measurableSet_Ioi.nullMeasurableSet) hmono ⟨0, MeasureTheory.measure_ne_top nu _⟩
    have hempty : (⋂ n : ℕ, (Set.Ioi (n:ℝ) : Set ℝ)) = ∅ := by
      apply le_antisymm _ (Set.empty_subset _)
      intro x hx
      rw [Set.mem_iInter] at hx
      obtain ⟨n, hn⟩ := exists_nat_gt x
      exact absurd (hx n) (by simp only [Set.mem_Ioi]; linarith)
    rw [hempty, MeasureTheory.measure_empty] at hlim
    have hreal : Tendsto (fun n : ℕ => (nu (Set.Ioi (n:ℝ))).toReal) atTop (𝓝 0) := by
      have h := (ENNReal.tendsto_toReal (by simp : (0:ENNReal) ≠ ⊤)).comp hlim
      simpa [Function.comp] using h
    have hev : ∀ᶠ n : ℕ in atTop, (nu (Set.Ioi (n:ℝ))).toReal < η' := by
      have h2 := (Metric.tendsto_nhds.1 hreal) η' hη'
      filter_upwards [h2] with n hn
      rw [Real.dist_eq, sub_zero] at hn
      rwa [abs_of_nonneg ENNReal.toReal_nonneg] at hn
    obtain ⟨n, hn⟩ := Filter.eventually_atTop.1 hev
    refine ⟨(n:ℝ), Nat.cast_nonneg n, ?_⟩
    simp only [MeasureTheory.Measure.real]
    exact hn n le_rfl
  set B : ℝ := ‖f‖ with hBdef
  have hB0 : 0 ≤ B := by rw [hBdef]; exact norm_nonneg _
  set η : ℝ := ε / (100 * (B + 1)) with hηdef
  have hηpos : 0 < η := by
    rw [hηdef]
    apply div_pos hε
    nlinarith
  obtain ⟨T₁, hT₁0, hT₁⟩ := htail_lo η hηpos
  obtain ⟨T₂, hT₂0, hT₂⟩ := htail_hi η hηpos
  set T : ℝ := max T₁ T₂ with hTdef
  have hT0 : 0 ≤ T := by rw [hTdef]; exact le_trans hT₁0 (le_max_left _ _)
  have hTlo : nu.real (Set.Iic (-T)) < η := by
    have hsub : Set.Iic (-T) ⊆ Set.Iic (-T₁) := by
      intro x hx
      simp only [Set.mem_Iic] at hx ⊢
      have h1 : T₁ ≤ T := by rw [hTdef]; exact le_max_left _ _
      linarith
    have h2 : nu.real (Set.Iic (-T)) ≤ nu.real (Set.Iic (-T₁)) := by
      simp only [MeasureTheory.Measure.real]
      exact ENNReal.toReal_mono (MeasureTheory.measure_ne_top nu _) (MeasureTheory.measure_mono hsub)
    linarith
  have hThi : nu.real (Set.Ioi T) < η := by
    have hsub : Set.Ioi T ⊆ Set.Ioi T₂ := by
      intro x hx
      simp only [Set.mem_Ioi] at hx ⊢
      have h1 : T₂ ≤ T := by rw [hTdef]; exact le_max_right _ _
      linarith
    have h2 : nu.real (Set.Ioi T) ≤ nu.real (Set.Ioi T₂) := by
      simp only [MeasureTheory.Measure.real]
      exact ENNReal.toReal_mono (MeasureTheory.measure_ne_top nu _) (MeasureTheory.measure_mono hsub)
    linarith
  obtain ⟨m, a, c, hm1, ha0, ham, hamono, happrox, hgbd, hgoff⟩ :=
    statopia_math_node_2623459540_991fa23d f T η hT0 hηpos
  set g : ℝ → ℝ := fun x => ∑ j ∈ Finset.range m, (Set.Ioc (a j) (a (j + 1))).indicator (fun _ : ℝ => c j) x with hgdef
  have hgapp : ∀ x ∈ Set.Ioc (-T) T, ‖f x - g x‖ ≤ η := by
    intro x hx
    simpa only [hgdef] using happrox x hx
  have hggb : ∀ x : ℝ, ‖g x‖ ≤ B := by
    intro x
    rw [hBdef]
    simpa only [hgdef] using hgbd x
  have hgoff' : ∀ x : ℝ, x ∉ Set.Ioc (-T) T → g x = 0 := by
    intro x hx
    simpa only [hgdef] using hgoff x hx
  have hIoc_eq : ∀ (ρ : Measure ℝ), IsProbabilityMeasure ρ → ∀ x y : ℝ, x ≤ y →
      ρ.real (Set.Ioc x y) = ρ.real (Set.Iic y) - ρ.real (Set.Iic x) := by
    intro ρ hρ x y hxy
    have hsub : Set.Iic x ⊆ Set.Iic y := by
      intro z hz
      simp only [Set.mem_Iic] at hz ⊢
      linarith
    have hset : Set.Ioc x y = Set.Iic y \ Set.Iic x := by
      ext z
      simp only [Set.mem_Ioc, Set.mem_diff, Set.mem_Iic, not_le]
      tauto
    have hdiff : ρ (Set.Ioc x y) = ρ (Set.Iic y) - ρ (Set.Iic x) := by
      rw [hset, MeasureTheory.measure_diff hsub measurableSet_Iic.nullMeasurableSet (MeasureTheory.measure_ne_top ρ _)]
    simp only [MeasureTheory.Measure.real]
    rw [hdiff, ENNReal.toReal_sub_of_le (MeasureTheory.measure_mono hsub) (MeasureTheory.measure_ne_top ρ _)]
  have hInt : ∀ (ρ : Measure ℝ), IsProbabilityMeasure ρ →
      ∫ x, g x ∂ρ = ∑ j ∈ Finset.range m, c j * ρ.real (Set.Ioc (a j) (a (j + 1))) := by
    intro ρ hρ
    have hgfun : ∀ x : ℝ, g x = ∑ j ∈ Finset.range m, (Set.Ioc (a j) (a (j + 1))).indicator (fun _ : ℝ => c j) x := by
      intro x
      simp only [hgdef]
    simp only [hgfun]
    have hstep : ∫ x, (∑ j ∈ Finset.range m, (Set.Ioc (a j) (a (j + 1))).indicator (fun _ : ℝ => c j) x) ∂ρ
        = ∑ j ∈ Finset.range m, ∫ x, (Set.Ioc (a j) (a (j + 1))).indicator (fun _ : ℝ => c j) x ∂ρ :=
      MeasureTheory.integral_finset_sum (Finset.range m)
        (fun j hj => MeasureTheory.Integrable.indicator (MeasureTheory.integrable_const (c j)) measurableSet_Ioc)
    rw [hstep]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [MeasureTheory.integral_indicator_const (c j) measurableSet_Ioc]
    simp only [smul_eq_mul]
    ring
  have hIocT : ∀ x y : ℝ, x ≤ y →
      Tendsto (fun r : ℕ => (mu r).real (Set.Ioc x y)) atTop (𝓝 (nu.real (Set.Ioc x y))) := by
    intro x y hxy
    have hfun : (fun r : ℕ => (mu r).real (Set.Ioc x y))
        = (fun r : ℕ => (mu r).real (Set.Iic y) - (mu r).real (Set.Iic x)) := by
      funext r
      exact hIoc_eq (mu r) (hmu r) x y hxy
    rw [hfun]
    have hsub := (hF y).sub (hF x)
    rw [← hIoc_eq nu hnu x y hxy] at hsub
    exact hsub
  have hsumT : ∀ (n : ℕ) (u : ℕ → ℕ → ℝ) (v : ℕ → ℝ),
      (∀ j < n, Tendsto (fun r : ℕ => u r j) atTop (𝓝 (v j))) →
      Tendsto (fun r : ℕ => ∑ j ∈ Finset.range n, u r j) atTop (𝓝 (∑ j ∈ Finset.range n, v j)) := by
    intro n
    induction n with
    | zero =>
      intro u v _
      simp
    | succ k ih =>
      intro u v h
      have h1 : Tendsto (fun r : ℕ => ∑ j ∈ Finset.range k, u r j) atTop
          (𝓝 (∑ j ∈ Finset.range k, v j)) :=
        ih u v (fun j hj => h j (Nat.lt_trans hj (Nat.lt_succ_self k)))
      have h2 : Tendsto (fun r : ℕ => u r k) atTop (𝓝 (v k)) := h k (Nat.lt_succ_self k)
      have h3 : Tendsto (fun r : ℕ => (∑ j ∈ Finset.range k, u r j) + u r k) atTop
          (𝓝 ((∑ j ∈ Finset.range k, v j) + v k)) := h1.add h2
      simpa [Finset.sum_range_succ] using h3
  have hstepT : Tendsto (fun r : ℕ => ∑ j ∈ Finset.range m, c j * (mu r).real (Set.Ioc (a j) (a (j + 1)))) atTop
      (𝓝 (∑ j ∈ Finset.range m, c j * nu.real (Set.Ioc (a j) (a (j + 1))))) :=
    hsumT m (fun r j => c j * (mu r).real (Set.Ioc (a j) (a (j + 1))))
      (fun j => c j * nu.real (Set.Ioc (a j) (a (j + 1))))
      (fun j hj => (hIocT (a j) (a (j + 1)) (hamono (Nat.le_succ j))).const_mul (c j))
  have hruniv : ∀ (ρ : Measure ℝ), IsProbabilityMeasure ρ → ρ.real Set.univ = 1 := by
    intro ρ hρ
    simp only [MeasureTheory.Measure.real]
    rw [MeasureTheory.measure_univ]
    norm_num
  have hSu : ∀ (ρ : Measure ℝ), IsProbabilityMeasure ρ →
      ρ.real (Set.Iic (-T) ∪ Set.Ioi T) = ρ.real (Set.Iic (-T)) + ρ.real (Set.Ioi T) := by
    intro ρ hρ
    have hc : Set.Iic (-T) ∪ Set.Ioi T = (Set.Ioc (-T) T)ᶜ := by
      ext x
      simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ioi, Set.mem_compl_iff, Set.mem_Ioc,
        not_and_or, not_lt, not_le]
    have hcomp : ρ.real (Set.Iic (-T) ∪ Set.Ioi T) = 1 - ρ.real (Set.Ioc (-T) T) := by
      rw [hc]
      simp only [MeasureTheory.Measure.real]
      rw [MeasureTheory.measure_compl measurableSet_Ioc (MeasureTheory.measure_ne_top ρ (Set.Ioc (-T) T))]
      rw [ENNReal.toReal_sub_of_le (MeasureTheory.measure_mono (Set.subset_univ _))
        (MeasureTheory.measure_ne_top ρ Set.univ)]
      rw [MeasureTheory.measure_univ]
      norm_num
    rw [hcomp, hIoc_eq ρ hρ (-T) T (by linarith), hcompl ρ hρ T]
    ring
  have hg_meas : Measurable g := by
    have hterm : ∀ j : ℕ, Measurable (fun x : ℝ => (Set.Ioc (a j) (a (j + 1))).indicator (fun _ : ℝ => c j) x) :=
      fun j => measurable_const.indicator measurableSet_Ioc
    have hsum : Measurable (fun x : ℝ => ∑ j ∈ Finset.range m, (Set.Ioc (a j) (a (j + 1))).indicator (fun _ : ℝ => c j) x) :=
      Finset.measurable_sum (Finset.range m) (fun j hj => hterm j)
    simpa only [hgdef] using hsum
  have hf_int : ∀ (ρ : Measure ℝ), IsProbabilityMeasure ρ → MeasureTheory.Integrable (fun x : ℝ => f x) ρ := by
    intro ρ hρ
    refine MeasureTheory.Integrable.of_bound ((BoundedContinuousFunction.continuous f).measurable.aestronglyMeasurable) ‖f‖ ?_
    exact Filter.Eventually.of_forall (fun x => BoundedContinuousFunction.norm_coe_le_norm f x)
  have hg_int : ∀ (ρ : Measure ℝ), IsProbabilityMeasure ρ → MeasureTheory.Integrable g ρ := by
    intro ρ hρ
    refine MeasureTheory.Integrable.of_bound hg_meas.aestronglyMeasurable B ?_
    exact Filter.Eventually.of_forall hggb
  have hbound_int : ∀ (ρ : Measure ℝ), IsProbabilityMeasure ρ →
      MeasureTheory.Integrable (fun x : ℝ => η + (Set.Iic (-T) ∪ Set.Ioi T).indicator (fun _ : ℝ => 2 * B) x) ρ := by
    intro ρ hρ
    exact MeasureTheory.Integrable.add (MeasureTheory.integrable_const η)
      (MeasureTheory.Integrable.indicator (MeasureTheory.integrable_const (2 * B))
        (measurableSet_Iic.union measurableSet_Ioi))
  have hpt : ∀ x : ℝ, ‖f x - g x‖ ≤ η + (Set.Iic (-T) ∪ Set.Ioi T).indicator (fun _ : ℝ => 2 * B) x := by
    intro x
    by_cases hx : x ∈ Set.Ioc (-T) T
    · have h1 : ‖f x - g x‖ ≤ η := hgapp x hx
      have hx1 : -T < x := (Set.mem_Ioc.1 hx).1
      have hx2 : x ≤ T := (Set.mem_Ioc.1 hx).2
      have h2 : (Set.Iic (-T) ∪ Set.Ioi T).indicator (fun _ : ℝ => 2 * B) x = 0 := by
        have hx' : x ∉ Set.Iic (-T) ∪ Set.Ioi T := by
          intro h
          rcases h with h | h
          · simp only [Set.mem_Iic] at h
            linarith
          · simp only [Set.mem_Ioi] at h
            linarith
        simp [Set.indicator, hx']
      rw [h2, add_zero]
      exact h1
    · have h1 : g x = 0 := hgoff' x hx
      have h2 : (Set.Iic (-T) ∪ Set.Ioi T).indicator (fun _ : ℝ => 2 * B) x = 2 * B := by
        have hx' : x ∈ Set.Iic (-T) ∪ Set.Ioi T := by
          by_cases h3 : x ≤ -T
          · exact Or.inl h3
          · refine Or.inr ?_
            simp only [Set.mem_Ioi]
            push_neg at h3
            by_contra h4
            simp only [not_lt] at h4
            exact hx (Set.mem_Ioc.2 ⟨h3, h4⟩)
        exact Set.indicator_of_mem hx' _
      have h3 : ‖f x‖ ≤ B := by
        rw [hBdef]
        exact BoundedContinuousFunction.norm_coe_le_norm f x
      have h4 : ‖f x - g x‖ ≤ B := by
        rw [h1, sub_zero]
        exact h3
      rw [h2]
      linarith
  have hInt_bound : ∀ (ρ : Measure ℝ), IsProbabilityMeasure ρ →
      ∫ x, (η + (Set.Iic (-T) ∪ Set.Ioi T).indicator (fun _ : ℝ => 2 * B) x) ∂ρ
        = η + 2 * B * (ρ.real (Set.Iic (-T)) + ρ.real (Set.Ioi T)) := by
    intro ρ hρ
    rw [MeasureTheory.integral_add (MeasureTheory.integrable_const η)
      (MeasureTheory.Integrable.indicator (MeasureTheory.integrable_const (2 * B))
        (measurableSet_Iic.union measurableSet_Ioi))]
    rw [MeasureTheory.integral_const]
    rw [MeasureTheory.integral_indicator_const (2 * B) (measurableSet_Iic.union measurableSet_Ioi)]
    rw [hruniv ρ hρ, hSu ρ hρ]
    simp only [smul_eq_mul]
    ring
  have hηε : 100 * (B + 1) * η = ε := by
    have hne : (100 : ℝ) * (B + 1) ≠ 0 := by
      have hpos : (0:ℝ) < 100 * (B + 1) := by nlinarith
      linarith
    rw [hηdef]
    field_simp
  have hmain : ∀ (ρ : Measure ℝ), IsProbabilityMeasure ρ →
      |∫ x, f x ∂ρ - ∫ x, g x ∂ρ| ≤ η + 2 * B * (ρ.real (Set.Iic (-T)) + ρ.real (Set.Ioi T)) := by
    intro ρ hρ
    have hle1 : ∫ x, f x ∂ρ ≤ ∫ x, g x ∂ρ + (η + 2 * B * (ρ.real (Set.Iic (-T)) + ρ.real (Set.Ioi T))) := by
      have h1 : ∫ x, f x ∂ρ ≤ ∫ x, (g x + (η + (Set.Iic (-T) ∪ Set.Ioi T).indicator (fun _ : ℝ => 2 * B) x)) ∂ρ := by
        refine MeasureTheory.integral_mono (hf_int ρ hρ) ?_ ?_
        · exact MeasureTheory.Integrable.add (hg_int ρ hρ) (hbound_int ρ hρ)
        · intro x
          have habs : |f x - g x| ≤ η + (Set.Iic (-T) ∪ Set.Ioi T).indicator (fun _ : ℝ => 2 * B) x := by
            simpa [Real.norm_eq_abs] using hpt x
          have h2 := (abs_le.1 habs).2
          linarith
      have h2 : ∫ x, (g x + (η + (Set.Iic (-T) ∪ Set.Ioi T).indicator (fun _ : ℝ => 2 * B) x)) ∂ρ
          = ∫ x, g x ∂ρ + (η + 2 * B * (ρ.real (Set.Iic (-T)) + ρ.real (Set.Ioi T))) := by
        rw [MeasureTheory.integral_add (hg_int ρ hρ) (hbound_int ρ hρ), hInt_bound ρ hρ]
      rw [h2] at h1
      exact h1
    have hle2 : ∫ x, g x ∂ρ ≤ ∫ x, f x ∂ρ + (η + 2 * B * (ρ.real (Set.Iic (-T)) + ρ.real (Set.Ioi T))) := by
      have h1 : ∫ x, g x ∂ρ ≤ ∫ x, (f x + (η + (Set.Iic (-T) ∪ Set.Ioi T).indicator (fun _ : ℝ => 2 * B) x)) ∂ρ := by
        refine MeasureTheory.integral_mono (hg_int ρ hρ) ?_ ?_
        · exact MeasureTheory.Integrable.add (hf_int ρ hρ) (hbound_int ρ hρ)
        · intro x
          have habs : |f x - g x| ≤ η + (Set.Iic (-T) ∪ Set.Ioi T).indicator (fun _ : ℝ => 2 * B) x := by
            simpa [Real.norm_eq_abs] using hpt x
          have h2 := (abs_le.1 habs).1
          linarith
      have h2 : ∫ x, (f x + (η + (Set.Iic (-T) ∪ Set.Ioi T).indicator (fun _ : ℝ => 2 * B) x)) ∂ρ
          = ∫ x, f x ∂ρ + (η + 2 * B * (ρ.real (Set.Iic (-T)) + ρ.real (Set.Ioi T))) := by
        rw [MeasureTheory.integral_add (hf_int ρ hρ) (hbound_int ρ hρ), hInt_bound ρ hρ]
      rw [h2] at h1
      exact h1
    rw [abs_le]
    constructor <;> linarith
  have hclose : ∀ᶠ r : ℕ in atTop,
      |(∑ j ∈ Finset.range m, c j * (mu r).real (Set.Ioc (a j) (a (j + 1)))) - (∑ j ∈ Finset.range m, c j * nu.real (Set.Ioc (a j) (a (j + 1))))| < η := by
    have h2 := (Metric.tendsto_nhds.1 hstepT) η hηpos
    filter_upwards [h2] with r hr
    rwa [Real.dist_eq] at hr
  have hμ_lo : ∀ᶠ r : ℕ in atTop, (mu r).real (Set.Iic (-T)) < 2 * η := by
    have hmem : Set.Iio (2 * η) ∈ 𝓝 ((nu).real (Set.Iic (-T))) :=
      IsOpen.mem_nhds isOpen_Iio (by show nu.real (Set.Iic (-T)) < 2 * η; linarith)
    exact (hF (-T)).eventually hmem
  have hμ_hi : ∀ᶠ r : ℕ in atTop, (mu r).real (Set.Ioi T) < 2 * η := by
    have hν : 1 - 2 * η < nu.real (Set.Iic T) := by
      have h1 := hcompl nu hnu T
      linarith
    have hmem : Set.Ioi (1 - 2 * η) ∈ 𝓝 ((nu).real (Set.Iic T)) :=
      IsOpen.mem_nhds isOpen_Ioi (by show 1 - 2 * η < nu.real (Set.Iic T); linarith)
    filter_upwards [(hF T).eventually hmem] with r hr
    have hr' : 1 - 2 * η < (mu r).real (Set.Iic T) := hr
    rw [hcompl (mu r) (hmu r) T]
    linarith
  simp only [Real.dist_eq]
  filter_upwards [hclose, hμ_lo, hμ_hi] with r hcl hlo hhi
  show |∫ x, f x ∂(mu r) - ∫ x, f x ∂nu| < ε
  have h1 := hmain (mu r) (hmu r)
  have h2 := hmain nu hnu
  have hmid : |∫ x, g x ∂(mu r) - ∫ x, g x ∂nu| < η := by
    rw [hInt (mu r) (hmu r), hInt nu hnu]
    exact hcl
  have hs1 : 2 * B * ((mu r).real (Set.Iic (-T)) + (mu r).real (Set.Ioi T)) ≤ 2 * B * (4 * η) := by
    have h0 : (0:ℝ) ≤ 2 * B := by linarith
    apply mul_le_mul_of_nonneg_left _ h0
    linarith
  have hs2 : 2 * B * (nu.real (Set.Iic (-T)) + nu.real (Set.Ioi T)) ≤ 2 * B * (2 * η) := by
    have h0 : (0:ℝ) ≤ 2 * B := by linarith
    apply mul_le_mul_of_nonneg_left _ h0
    linarith
  have hfin : |∫ x, f x ∂(mu r) - ∫ x, f x ∂nu| ≤ 3 * η + 12 * B * η := by
    have hb1 := abs_le.1 h1
    have hb2 := abs_le.1 h2
    have hb3 := abs_le.1 (le_of_lt hmid)
    rw [abs_le]
    constructor
    · linarith [hb1.1, hb2.2, hb3.1, hs1, hs2]
    · linarith [hb1.2, hb2.1, hb3.2, hs1, hs2]
  nlinarith [hfin, hηpos, hB0, hηε]
  /- @proof-region region.target-node.session.4fd4a37cd8d59600 end -/
