import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q17.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q17.Base

open MeasureTheory

open MeasureTheory

set_option autoImplicit false in
theorem statopia_math_node_444070725_2ef7631b : ∀ {Omega : Type*} {Zt : Type*}
    [MeasurableSpace Omega]
    [Fintype Zt]
    [MeasurableSpace Zt]
    [MeasurableSingletonClass Zt]
    (P : Measure Omega)
    [IsProbabilityMeasure P]
    (R : Omega → Bool)
    (Z : Omega → Zt)
    (Y : Omega → ℝ)
    (hRmeas : Measurable R)
    (hZmeas : Measurable Z)
    (hYmeas : Measurable Y)
    (hYint : Integrable Y P)
    (hZpos : ∀ z, 0 < P {ω | Z ω = z})
    (hMAR :
      ∀ (B : Set ℝ), MeasurableSet B → ∀ r z,
        P {ω | Y ω ∈ B ∧ R ω = r ∧ Z ω = z} * P {ω | Z ω = z} =
          P {ω | Y ω ∈ B ∧ Z ω = z} * P {ω | R ω = r ∧ Z ω = z}),
    ∀ z : Zt,
      ∫ ω in {ω | R ω = true ∧ Z ω = z}, Y ω ∂P =
        ((P {ω | R ω = true ∧ Z ω = z}).toReal / (P {ω | Z ω = z}).toReal) *
          ∫ ω in {ω | Z ω = z}, Y ω ∂P := by
  /- @proof-region region.target-node.session.08a1799950f690bd begin -/
  intro Omega Zt _ _ _ _ P _ R Z Y hRmeas hZmeas hYmeas hYint hZpos hMAR z
  set Tz : Set Omega := {ω | Z ω = z} with hTz_def
  set Sz : Set Omega := {ω | R ω = true ∧ Z ω = z} with hSz_def
  have hTz_pos : 0 < P Tz := by
    rw [hTz_def]
    exact hZpos z
  have hTz_lt_top : P Tz < ⊤ := by
    calc P Tz ≤ P Set.univ := measure_mono (Set.subset_univ Tz)
      _ = 1 := measure_univ
      _ < ⊤ := by simp
  have hTz_ne_top : P Tz ≠ ⊤ := ne_of_lt hTz_lt_top
  have hTz_ne_zero : P Tz ≠ 0 := ne_of_gt hTz_pos
  have hTz_toReal_pos : 0 < (P Tz).toReal := ENNReal.toReal_pos hTz_ne_zero hTz_ne_top
  have hTz_toReal_ne_zero : (P Tz).toReal ≠ 0 := ne_of_gt hTz_toReal_pos
  have hπ_nonneg : 0 ≤ (P Sz).toReal / (P Tz).toReal :=
    div_nonneg ENNReal.toReal_nonneg (le_of_lt hTz_toReal_pos)
  set ν : Measure ℝ := Measure.map Y (P.restrict Tz) with hν_def
  set μ : Measure ℝ := Measure.map Y (P.restrict Sz) with hμ_def
  have hprop : μ = ENNReal.ofReal ((P Sz).toReal / (P Tz).toReal) • ν := by
    refine Measure.ext fun B hB => ?_
    have hμB : μ B = P {ω | Y ω ∈ B ∧ R ω = true ∧ Z ω = z} := by
      rw [hμ_def, Measure.map_apply hYmeas hB, Measure.restrict_apply (hYmeas hB)]
      congr 1
    have hνB : ν B = P {ω | Y ω ∈ B ∧ Z ω = z} := by
      rw [hν_def, Measure.map_apply hYmeas hB, Measure.restrict_apply (hYmeas hB)]
      congr 1
    have hM : P {ω | Y ω ∈ B ∧ R ω = true ∧ Z ω = z} * P Tz =
        P {ω | Y ω ∈ B ∧ Z ω = z} * P Sz := by
      have h := hMAR B hB true z
      rwa [← hTz_def, ← hSz_def] at h
    have hsub1 : {ω | Y ω ∈ B ∧ R ω = true ∧ Z ω = z} ⊆ Tz := by
      rw [hTz_def]
      intro ω hω
      exact hω.2.2
    have hsub2 : {ω | Y ω ∈ B ∧ Z ω = z} ⊆ Tz := by
      rw [hTz_def]
      intro ω hω
      exact hω.2
    have hxfin : P {ω | Y ω ∈ B ∧ R ω = true ∧ Z ω = z} ≠ ⊤ :=
      ne_of_lt (lt_of_le_of_lt (measure_mono hsub1) hTz_lt_top)
    have hyfin : P {ω | Y ω ∈ B ∧ Z ω = z} ≠ ⊤ :=
      ne_of_lt (lt_of_le_of_lt (measure_mono hsub2) hTz_lt_top)
    have hkey : (P {ω | Y ω ∈ B ∧ R ω = true ∧ Z ω = z}).toReal =
        (P {ω | Y ω ∈ B ∧ Z ω = z}).toReal * ((P Sz).toReal / (P Tz).toReal) := by
      have h2 : (P {ω | Y ω ∈ B ∧ R ω = true ∧ Z ω = z}).toReal * (P Tz).toReal =
          (P {ω | Y ω ∈ B ∧ Z ω = z}).toReal * (P Sz).toReal := by
        rw [← ENNReal.toReal_mul, ← ENNReal.toReal_mul, hM]
      field_simp
      linarith [h2]
    have hz_top : ENNReal.ofReal ((P Sz).toReal / (P Tz).toReal) *
        ENNReal.ofReal (P {ω | Y ω ∈ B ∧ Z ω = z}).toReal ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    have hz_toReal : (ENNReal.ofReal ((P Sz).toReal / (P Tz).toReal) *
        ENNReal.ofReal (P {ω | Y ω ∈ B ∧ Z ω = z}).toReal).toReal =
        (P {ω | Y ω ∈ B ∧ R ω = true ∧ Z ω = z}).toReal := by
      rw [ENNReal.toReal_ofReal_mul _ _ hπ_nonneg,
        ENNReal.toReal_ofReal ENNReal.toReal_nonneg, mul_comm, ← hkey]
    rw [hμB, Measure.smul_apply, hνB, ← ENNReal.ofReal_toReal hxfin, ← hz_toReal,
      ENNReal.ofReal_toReal hz_top, ENNReal.ofReal_toReal hyfin]
    simp
  have hIntS : ∫ y : ℝ, y ∂μ = ∫ ω in Sz, Y ω ∂P := by
    have h := MeasureTheory.integral_map (μ := P.restrict Sz) (φ := Y) (f := fun y : ℝ => y)
      hYmeas.aemeasurable measurable_id.aestronglyMeasurable
    rw [hμ_def]
    exact h
  have hIntT : ∫ y : ℝ, y ∂ν = ∫ ω in Tz, Y ω ∂P := by
    have h := MeasureTheory.integral_map (μ := P.restrict Tz) (φ := Y) (f := fun y : ℝ => y)
      hYmeas.aemeasurable measurable_id.aestronglyMeasurable
    rw [hν_def]
    exact h
  calc ∫ ω in Sz, Y ω ∂P = ∫ y : ℝ, y ∂μ := hIntS.symm
    _ = ∫ y : ℝ, y ∂(ENNReal.ofReal ((P Sz).toReal / (P Tz).toReal) • ν) := by rw [hprop]
    _ = ((P Sz).toReal / (P Tz).toReal) * ∫ y : ℝ, y ∂ν := by
          rw [MeasureTheory.integral_smul_measure, ENNReal.toReal_ofReal hπ_nonneg]
          simp
    _ = ((P Sz).toReal / (P Tz).toReal) * ∫ ω in Tz, Y ω ∂P := by rw [hIntT]
  /- @proof-region region.target-node.session.08a1799950f690bd end -/
