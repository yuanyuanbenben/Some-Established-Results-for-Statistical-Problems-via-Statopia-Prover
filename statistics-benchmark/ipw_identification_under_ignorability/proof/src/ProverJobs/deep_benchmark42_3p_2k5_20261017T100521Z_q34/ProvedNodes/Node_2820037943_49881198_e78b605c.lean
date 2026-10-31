import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q34.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q34.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q34.ProvedNodes.Node_3366159575_484baf36_ffb3edf5

open MeasureTheory

open MeasureTheory

set_option autoImplicit false in
theorem statopia_math_node_2820037943_49881198 : ∀ {Ω 𝒵 : Type*}
    [MeasurableSpace Ω]
    [Fintype 𝒵]
    [MeasurableSpace 𝒵]
    [MeasurableSingletonClass 𝒵]
    (P : Measure Ω)
    [IsProbabilityMeasure P]
    (T : Ω → Bool)
    (Z : Ω → 𝒵)
    (Y0 Y1 : Ω → ℝ)
    (hTmeas : Measurable T)
    (hZmeas : Measurable Z)
    (hY0meas : Measurable Y0)
    (hY1meas : Measurable Y1)
    (hZpos : ∀ z : 𝒵, 0 < P {ω : Ω | Z ω = z})
    (hPositive :
      ∀ (a : Bool) (z : 𝒵),
        0 < (P {ω : Ω | T ω = a ∧ Z ω = z}).toReal /
          (P {ω : Ω | Z ω = z}).toReal)
    (hIgnorable :
      ∀ (a : Bool) (B : Set ℝ), MeasurableSet B → ∀ (t : Bool) (z : 𝒵),
        P {ω : Ω | (if a then Y1 ω else Y0 ω) ∈ B ∧ T ω = t ∧ Z ω = z} *
            P {ω : Ω | Z ω = z} =
          P {ω : Ω | (if a then Y1 ω else Y0 ω) ∈ B ∧ Z ω = z} *
            P {ω : Ω | T ω = t ∧ Z ω = z})
    (hInt : ∀ a : Bool, Integrable (fun ω : Ω => if a then Y1 ω else Y0 ω) P)
    (a : Bool) (z : 𝒵),
    ∫ ω in {ω : Ω | T ω = a ∧ Z ω = z}, (if a then Y1 ω else Y0 ω) ∂P =
      ((P {ω : Ω | T ω = a ∧ Z ω = z}).toReal /
          (P {ω : Ω | Z ω = z}).toReal) *
        ∫ ω in {ω : Ω | Z ω = z}, (if a then Y1 ω else Y0 ω) ∂P := by
  /- @proof-region region.target-node.session.4748fd9f112c724b begin -/
  intro Ω 𝒵 _ _ _ _ P _ T Z Y0 Y1 hTmeas hZmeas hY0meas hY1meas hZpos hPositive hIgnorable hInt a z
  have hAmeas : Measurable (fun ω : Ω => if a then Y1 ω else Y0 ω) := by
    by_cases ha : a = true
    · simpa [ha] using hY1meas
    · simpa [ha] using hY0meas
  have hS₁ : ∀ B : Set ℝ,
      (fun ω : Ω => if a then Y1 ω else Y0 ω) ⁻¹' B ∩ {ω : Ω | T ω = a ∧ Z ω = z}
        = {ω : Ω | (if a then Y1 ω else Y0 ω) ∈ B ∧ T ω = a ∧ Z ω = z} := by
    intro B
    ext ω
    simp [Set.mem_inter_iff]
  have hS₂ : ∀ B : Set ℝ,
      (fun ω : Ω => if a then Y1 ω else Y0 ω) ⁻¹' B ∩ {ω : Ω | Z ω = z}
        = {ω : Ω | (if a then Y1 ω else Y0 ω) ∈ B ∧ Z ω = z} := by
    intro B
    ext ω
    simp [Set.mem_inter_iff]
  have hmeasure :
      Measure.map (fun ω : Ω => if a then Y1 ω else Y0 ω)
          (P.restrict {ω : Ω | T ω = a ∧ Z ω = z})
        = ENNReal.ofReal ((P {ω : Ω | T ω = a ∧ Z ω = z}).toReal /
            (P {ω : Ω | Z ω = z}).toReal) •
          Measure.map (fun ω : Ω => if a then Y1 ω else Y0 ω)
            (P.restrict {ω : Ω | Z ω = z}) := by
    ext B hB
    have hdep := statopia_math_node_3366159575_484baf36 (Ω := Ω) (𝒵 := 𝒵)
      P T Z Y0 Y1 hZpos hIgnorable a B hB z
    dsimp only at hdep
    simp only [Measure.smul_apply, Measure.map_apply hAmeas hB,
      Measure.restrict_apply (hAmeas hB), hS₁ B, hS₂ B]
    simpa using hdep
  have hint₁ :
      ∫ x : ℝ, x ∂Measure.map (fun ω : Ω => if a then Y1 ω else Y0 ω)
          (P.restrict {ω : Ω | T ω = a ∧ Z ω = z}) =
        ∫ ω in {ω : Ω | T ω = a ∧ Z ω = z}, (if a then Y1 ω else Y0 ω) ∂P := by
    have h := MeasureTheory.integral_map (α := Ω) (β := ℝ) (G := ℝ)
      (μ := P.restrict {ω : Ω | T ω = a ∧ Z ω = z})
      (φ := fun ω : Ω => if a then Y1 ω else Y0 ω)
      hAmeas.aemeasurable (f := fun x : ℝ => x) measurable_id.aestronglyMeasurable
    simpa using h
  have hint₂ :
      ∫ x : ℝ, x ∂Measure.map (fun ω : Ω => if a then Y1 ω else Y0 ω)
          (P.restrict {ω : Ω | Z ω = z}) =
        ∫ ω in {ω : Ω | Z ω = z}, (if a then Y1 ω else Y0 ω) ∂P := by
    have h := MeasureTheory.integral_map (α := Ω) (β := ℝ) (G := ℝ)
      (μ := P.restrict {ω : Ω | Z ω = z})
      (φ := fun ω : Ω => if a then Y1 ω else Y0 ω)
      hAmeas.aemeasurable (f := fun x : ℝ => x) measurable_id.aestronglyMeasurable
    simpa using h
  rw [← hint₁, hmeasure,
    MeasureTheory.integral_smul_measure (fun x : ℝ => x)
      (ENNReal.ofReal ((P {ω : Ω | T ω = a ∧ Z ω = z}).toReal /
        (P {ω : Ω | Z ω = z}).toReal)),
    hint₂, ENNReal.toReal_ofReal (le_of_lt (hPositive a z))]
  simp
  /- @proof-region region.target-node.session.4748fd9f112c724b end -/
