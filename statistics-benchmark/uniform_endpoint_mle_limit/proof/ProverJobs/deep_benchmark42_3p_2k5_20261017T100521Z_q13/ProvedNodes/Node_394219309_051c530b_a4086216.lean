import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q13.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q13.Base

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

set_option autoImplicit false in
theorem statopia_math_node_394219309_051c530b : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (θ : ℝ) (hθ : 0 < θ)
    (X : ℕ → Ω → ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X P)
    (hX_uniform : ∀ i, MeasureTheory.pdf.IsUniform (X i) (Set.Ioo 0 θ) P)
    (r : ℕ) (a : ℝ) (ha_pos : 0 < a) (ha_lt : a < θ),
    (P {ω | (Finset.univ : Finset (Fin (r + 1))).sup'
        Finset.univ_nonempty (fun i => X i.1 ω) < a}).toReal
      = (a / θ) ^ (r + 1) := by
  /- @proof-region region.target-node.session.ed3d9e405f1670cc begin -/
  intro Ω _ P _ θ hθ X hX_meas hX_indep hX_uniform r a ha_pos ha_lt
  have h_event : {ω | (Finset.univ : Finset (Fin (r + 1))).sup' Finset.univ_nonempty
        (fun i => X i.1 ω) < a}
      = ⋂ i ∈ Finset.range (r + 1), X i ⁻¹' Set.Iio a := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_Iio,
      Finset.mem_range]
    rw [Finset.sup'_lt_iff Finset.univ_nonempty]
    constructor
    · intro h i hi
      exact h ⟨i, hi⟩ (Finset.mem_univ _)
    · intro h i _
      exact h i.1 i.isLt
  have h_inter : Set.Ioo (0 : ℝ) θ ∩ Set.Iio a = Set.Ioo 0 a := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Iio]
    constructor
    · rintro ⟨⟨h0, _⟩, ha⟩; exact ⟨h0, ha⟩
    · rintro ⟨h0, ha⟩; exact ⟨⟨h0, lt_trans ha ha_lt⟩, ha⟩
  have hvolθ : (volume : Measure ℝ) (Set.Ioo 0 θ) = ENNReal.ofReal θ := by
    rw [Real.volume_Ioo, sub_zero]
  have hvolθ_ne0 : (volume : Measure ℝ) (Set.Ioo 0 θ) ≠ 0 := by
    rw [hvolθ]; exact (ENNReal.ofReal_pos.mpr hθ).ne'
  have hvolθ_ne_top : (volume : Measure ℝ) (Set.Ioo 0 θ) ≠ ⊤ := by
    rw [hvolθ]; exact ENNReal.ofReal_ne_top
  have h_div : ENNReal.ofReal a / ENNReal.ofReal θ = ENNReal.ofReal (a / θ) :=
    (ENNReal.ofReal_div_of_pos hθ).symm
  have h_marg : ∀ i : ℕ, P (X i ⁻¹' Set.Iio a) = ENNReal.ofReal (a / θ) := by
    intro i
    have hfac := MeasureTheory.pdf.IsUniform.measure_preimage hvolθ_ne0 hvolθ_ne_top
      (hX_uniform i) (A := Set.Iio a) measurableSet_Iio
    rw [hfac, h_inter, hvolθ, Real.volume_Ioo, sub_zero]
    exact h_div
  have h_factor : P (⋂ i ∈ Finset.range (r + 1), X i ⁻¹' Set.Iio a)
      = ∏ i ∈ Finset.range (r + 1), P (X i ⁻¹' Set.Iio a) :=
    (ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul.mp hX_indep)
      (Finset.range (r + 1)) (sets := fun _ => Set.Iio a) (fun i _ => measurableSet_Iio)
  have hratio : 0 < a / θ := div_pos ha_pos hθ
  rw [h_event, h_factor, Finset.prod_congr rfl (fun i _ => h_marg i)]
  rw [← ENNReal.ofReal_prod_of_nonneg (s := Finset.range (r + 1)) (f := fun _ => a / θ)
    (fun i _ => hratio.le)]
  rw [Finset.prod_const, Finset.card_range]
  rw [ENNReal.toReal_ofReal (pow_nonneg hratio.le _)]


  /- @proof-region region.target-node.session.ed3d9e405f1670cc end -/
