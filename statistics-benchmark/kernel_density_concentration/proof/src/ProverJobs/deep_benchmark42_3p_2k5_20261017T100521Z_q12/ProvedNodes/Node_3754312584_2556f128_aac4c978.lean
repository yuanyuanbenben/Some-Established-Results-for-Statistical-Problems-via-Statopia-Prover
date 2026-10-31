import Statlib.StatFoundation.BasicAnalysis.ENNRealBridge
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q12.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q12.Base

open MeasureTheory ProbabilityTheory

open MeasureTheory ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_3754312584_2556f128 : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 1 ≤ n)
    (X : Fin n → Ω → ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (f : ℝ → ℝ) (hf_meas : Measurable f)
    (hf_nonneg : ∀ᵐ x ∂volume, 0 ≤ f x)
    (hX_law : ∀ i,
      HasLaw (X i) (volume.withDensity (fun x => ENNReal.ofReal (f x))) P),
    (∫⁻ x, ENNReal.ofReal (f x) ∂volume) = 1 ∧
      Integrable f volume ∧
      (∫ x, f x ∂volume) = 1 ∧
      (∫ x, |f x| ∂volume) = 1 := by
  /- @proof-region region.target-node.session.58e69ac38b56f2a7 begin -/
  intro Ω _ P _ n hn X hX_meas f hf_meas hf_nonneg hX_law
  have hi : Fin n := ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hn⟩
  have hlaw := hX_law hi
  haveI hprob : IsProbabilityMeasure
      (volume.withDensity (fun x => ENNReal.ofReal (f x))) :=
    (ProbabilityTheory.HasLaw.isProbabilityMeasure_iff hlaw).mp (by infer_instance)
  have hmass : (volume.withDensity (fun x => ENNReal.ofReal (f x))) Set.univ = 1 :=
    MeasureTheory.measure_univ
  have hlin : ∫⁻ x, ENNReal.ofReal (f x) ∂volume = 1 := by
    have h := MeasureTheory.withDensity_apply (μ := volume)
      (fun x => ENNReal.ofReal (f x)) (s := Set.univ) MeasurableSet.univ
    rw [hmass] at h
    simpa using h.symm
  have h_enorm : ∫⁻ x, ‖f x‖ₑ ∂volume = 1 := by
    rw [← hlin]
    apply MeasureTheory.lintegral_congr_ae
    filter_upwards [hf_nonneg] with x hx
    exact Real.enorm_eq_ofReal hx
  have hfin : HasFiniteIntegral f volume := by
    unfold MeasureTheory.HasFiniteIntegral
    rw [h_enorm]
    simp
  have hint : Integrable f volume := ⟨hf_meas.aestronglyMeasurable, hfin⟩
  refine ⟨hlin, hint, ?_, ?_⟩
  · rw [Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.integral_eq_lintegral_toReal_of_nonneg
      hf_nonneg hint, hlin]
    simp
  · have hnonneg_abs : 0 ≤ᶠ[ae volume] (fun x => |f x|) := by
      filter_upwards with x using abs_nonneg (f x)
    have hlin_abs : ∫⁻ x, ENNReal.ofReal (|f x|) ∂volume = 1 := by
      rw [← h_enorm]
      apply MeasureTheory.lintegral_congr_ae
      filter_upwards with x
      exact (Real.enorm_eq_ofReal_abs (f x)).symm
    have hint_abs : Integrable (fun x => |f x|) volume := hint.abs
    rw [Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.integral_eq_lintegral_toReal_of_nonneg
      hnonneg_abs hint_abs, hlin_abs]
    simp
  /- @proof-region region.target-node.session.58e69ac38b56f2a7 end -/
