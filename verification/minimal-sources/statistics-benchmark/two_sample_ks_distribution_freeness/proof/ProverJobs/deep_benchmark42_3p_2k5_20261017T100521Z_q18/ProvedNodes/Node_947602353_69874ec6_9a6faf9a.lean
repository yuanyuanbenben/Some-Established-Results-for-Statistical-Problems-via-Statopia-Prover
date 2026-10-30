import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q18.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q18.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q18.ProvedNodes.Node_2816082626_d13a3ccf_acec968e

open MeasureTheory ProbabilityTheory Filter

open MeasureTheory ProbabilityTheory Filter

set_option autoImplicit false in
theorem statopia_math_node_947602353_69874ec6 : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (f : ℝ → ℝ)
    (hf_cont : Continuous f)
    (hf_strict : StrictMono f)
    (hf_bot : Tendsto f Filter.atBot (nhds (0 : ℝ)))
    (hf_top : Tendsto f Filter.atTop (nhds (1 : ℝ)))
    (k : ℕ) (Z : Fin k → Ω → ℝ)
    (hZ_meas : ∀ i : Fin k, Measurable (Z i))
    (hZ_cdf : ∀ (i : Fin k) (t : ℝ), (P {ω | Z i ω ≤ t}).toReal = f t),
    ∀ i : Fin k, Measure.map (fun ω => f (Z i ω)) P =
      ((volume : Measure ℝ) (Set.Ioo (0 : ℝ) 1))⁻¹ •
        (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1) := by
  /- @proof-region region.target-node.session.3997810b295d4707 begin -/
  intro Ω _instΩ P _instP f hf_cont hf_strict hf_bot hf_top k Z hZ_meas hZ_cdf i
  obtain ⟨hf01, hiff, hsurj, _⟩ :=
    statopia_math_node_2816082626_d13a3ccf f hf_cont hf_strict hf_bot hf_top
  have hmeas : Measurable (fun ω => f (Z i ω)) := hf_cont.measurable.comp (hZ_meas i)
  have hvol : (volume : Measure ℝ) (Set.Ioo (0 : ℝ) 1) = 1 := by
    rw [Real.volume_Ioo]
    simp
  have hΛ : ((volume : Measure ℝ) (Set.Ioo (0 : ℝ) 1))⁻¹ •
      (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1) =
      (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1) := by
    rw [hvol, inv_one, one_smul]
  have hpoint : ∀ u : ℝ, Measure.map (fun ω => f (Z i ω)) P (Set.Iic u) =
      (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1) (Set.Iic u) := by
    intro u
    rw [Measure.map_apply hmeas measurableSet_Iic, Measure.restrict_apply measurableSet_Iic]
    by_cases hu0 : u ≤ 0
    · have hset : (fun ω => f (Z i ω)) ⁻¹' Set.Iic u = (∅ : Set Ω) := by
        ext ω
        constructor
        · intro hω
          simp only [Set.mem_preimage, Set.mem_Iic] at hω
          exact absurd hω (not_le.mpr (lt_of_le_of_lt hu0 (hf01 (Z i ω)).1))
        · intro hω
          exact absurd hω (Set.notMem_empty ω)
      have hI : Set.Iic u ∩ Set.Ioo (0 : ℝ) 1 = (∅ : Set ℝ) := by
        ext x
        constructor
        · intro hx
          simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioo] at hx
          exact absurd (le_trans hx.1 hu0) (not_le.mpr hx.2.1)
        · intro hx
          exact absurd hx (Set.notMem_empty x)
      rw [hset, hI, measure_empty, measure_empty]
    · rcases lt_or_ge u 1 with hu1 | hu1
      · obtain ⟨t, ht⟩ := hsurj u (not_le.mp hu0) hu1
        have hset : (fun ω => f (Z i ω)) ⁻¹' Set.Iic u = {ω | Z i ω ≤ t} := by
          ext ω
          simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_setOf_eq, ← ht, hiff (Z i ω) t]
        have hI : Set.Iic u ∩ Set.Ioo (0 : ℝ) 1 = Set.Ioc (0 : ℝ) u := by
          ext x
          constructor
          · intro hx
            simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioo] at hx
            exact ⟨hx.2.1, hx.1⟩
          · intro hx
            simp only [Set.mem_Ioc] at hx
            exact ⟨hx.2, hx.1, lt_of_le_of_lt hx.2 hu1⟩
        have hP : P {ω | Z i ω ≤ t} = ENNReal.ofReal u := by
          have hle : P {ω | Z i ω ≤ t} ≤ 1 := by
            calc P {ω | Z i ω ≤ t} ≤ P Set.univ := measure_mono (Set.subset_univ _)
              _ = 1 := measure_univ
          have hne : P {ω | Z i ω ≤ t} ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hle
          rw [← ENNReal.ofReal_toReal hne, hZ_cdf i t, ht]
        have hVu : (volume : Measure ℝ) (Set.Ioc (0 : ℝ) u) = ENNReal.ofReal u := by
          rw [Real.volume_Ioc]
          simp
        rw [hset, hI, hP, hVu]
      · have hset : (fun ω => f (Z i ω)) ⁻¹' Set.Iic u = (Set.univ : Set Ω) := by
          ext ω
          constructor
          · intro _
            exact Set.mem_univ ω
          · intro _
            simp only [Set.mem_preimage, Set.mem_Iic]
            exact le_trans (le_of_lt (hf01 (Z i ω)).2) hu1
        have hI : Set.Iic u ∩ Set.Ioo (0 : ℝ) 1 = Set.Ioo (0 : ℝ) 1 := by
          ext x
          constructor
          · intro hx
            simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioo] at hx
            exact hx.2
          · intro hx
            simp only [Set.mem_Ioo] at hx
            exact ⟨le_trans (le_of_lt hx.2) hu1, hx.1, hx.2⟩
        rw [hset, hI, measure_univ, Real.volume_Ioo]
        simp
  rw [hΛ]
  have hμuniv : Measure.map (fun ω => f (Z i ω)) P Set.univ = 1 := by
    rw [Measure.map_apply hmeas MeasurableSet.univ]
    simp
  have hνuniv : (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1) Set.univ = 1 := by
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, hvol]
  have hIic_pi : IsPiSystem (Set.range (Set.Iic : ℝ → Set ℝ)) := by
    rintro s ⟨a, rfl⟩ t ⟨b, rfl⟩ -
    exact ⟨min a b, by ext x; simp [le_min_iff]⟩
  have key : ∀ t : Set ℝ, MeasurableSet t →
      Measure.map (fun ω => f (Z i ω)) P t =
        (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1) t := by
    refine MeasurableSpace.induction_on_inter (borel_eq_generateFrom_Iic ℝ) hIic_pi ?_ ?_ ?_ ?_
    · rw [measure_empty, measure_empty]
    · rintro t ⟨a, rfl⟩
      exact hpoint a
    · intro t ht hh
      have hνt : (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1) t ≠ ⊤ := by
        refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
        rw [← hνuniv]
        exact measure_mono (Set.subset_univ t)
      have hμt : Measure.map (fun ω => f (Z i ω)) P t ≠ ⊤ := by
        rw [hh]
        exact hνt
      rw [measure_compl ht hμt, measure_compl ht hνt, hh, hμuniv, hνuniv]
    · intro g' hdisj hfm hC
      rw [measure_iUnion hdisj hfm, measure_iUnion hdisj hfm]
      exact tsum_congr hC
  exact Measure.ext key
  /- @proof-region region.target-node.session.3997810b295d4707 end -/
