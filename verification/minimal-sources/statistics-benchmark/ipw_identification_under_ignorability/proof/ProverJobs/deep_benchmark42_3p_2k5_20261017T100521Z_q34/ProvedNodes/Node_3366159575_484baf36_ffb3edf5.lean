import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q34.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q34.Base

open MeasureTheory

open MeasureTheory

set_option autoImplicit false in
theorem statopia_math_node_3366159575_484baf36 : ∀ {Ω 𝒵 : Type*}
    [MeasurableSpace Ω]
    [Fintype 𝒵]
    [MeasurableSpace 𝒵]
    [MeasurableSingletonClass 𝒵]
    (P : Measure Ω)
    [IsProbabilityMeasure P]
    (T : Ω → Bool)
    (Z : Ω → 𝒵)
    (Y0 Y1 : Ω → ℝ)
    (hZpos : ∀ z : 𝒵, 0 < P {ω | Z ω = z})
    (hIgnorable :
      ∀ (a : Bool) (B : Set ℝ), MeasurableSet B → ∀ (t : Bool) (z : 𝒵),
        P {ω | (if a then Y1 ω else Y0 ω) ∈ B ∧ T ω = t ∧ Z ω = z} *
            P {ω | Z ω = z} =
          P {ω | (if a then Y1 ω else Y0 ω) ∈ B ∧ Z ω = z} *
            P {ω | T ω = t ∧ Z ω = z}),
    let e : Bool → 𝒵 → ℝ := fun a z =>
      (P {ω | T ω = a ∧ Z ω = z}).toReal / (P {ω | Z ω = z}).toReal
    ∀ (a : Bool) (B : Set ℝ), MeasurableSet B → ∀ z : 𝒵,
      P {ω | (if a then Y1 ω else Y0 ω) ∈ B ∧ T ω = a ∧ Z ω = z} =
        ENNReal.ofReal (e a z) * P {ω | (if a then Y1 ω else Y0 ω) ∈ B ∧ Z ω = z} := by
  /- @proof-region region.target-node.session.6c56e083a9adaf07 begin -/
  intro Ω 𝒵 _ _ _ _ P _ T Z Y0 Y1 hZpos hIgnorable
  dsimp only
  intro a B hB z
  set M1 := P {ω | (if a then Y1 ω else Y0 ω) ∈ B ∧ T ω = a ∧ Z ω = z} with hM1def
  set M2 := P {ω | (if a then Y1 ω else Y0 ω) ∈ B ∧ Z ω = z} with hM2def
  set Pz := P {ω | Z ω = z} with hPzdef
  set Pa := P {ω | T ω = a ∧ Z ω = z} with hPaDef
  have hM1top : M1 ≠ ⊤ := by rw [hM1def]; exact measure_ne_top P _
  have hM2top : M2 ≠ ⊤ := by rw [hM2def]; exact measure_ne_top P _
  have hPztop : Pz ≠ ⊤ := by rw [hPzdef]; exact measure_ne_top P _
  have hPz0 : Pz ≠ 0 := by rw [hPzdef]; exact ne_of_gt (hZpos z)
  have hPzpos : 0 < Pz.toReal := ENNReal.toReal_pos hPz0 hPztop
  have hkey : M1 * Pz = M2 * Pa := by
    have h := hIgnorable a B hB a z
    rw [← hM1def, ← hM2def, ← hPzdef, ← hPaDef] at h
    exact h
  have hreal : M1.toReal * Pz.toReal = M2.toReal * Pa.toReal := by
    have h := congrArg ENNReal.toReal hkey
    rwa [ENNReal.toReal_mul, ENNReal.toReal_mul] at h
  have hdiv1 : M1.toReal = M2.toReal * Pa.toReal / Pz.toReal := by
    rw [eq_div_iff (ne_of_gt hPzpos), hreal]
  have hdiv : M1.toReal = M2.toReal * (Pa.toReal / Pz.toReal) := by
    rw [hdiv1, mul_div_assoc]
  have hof1 : ENNReal.ofReal M1.toReal = M1 := ENNReal.ofReal_toReal hM1top
  have hof2 : ENNReal.ofReal M2.toReal = M2 := ENNReal.ofReal_toReal hM2top
  have hmul : ENNReal.ofReal (M2.toReal * (Pa.toReal / Pz.toReal)) =
      ENNReal.ofReal M2.toReal * ENNReal.ofReal (Pa.toReal / Pz.toReal) :=
    ENNReal.ofReal_mul ENNReal.toReal_nonneg
  show M1 = ENNReal.ofReal (Pa.toReal / Pz.toReal) * M2
  rw [← hof1, hdiv, hmul, hof2, mul_comm]
  /- @proof-region region.target-node.session.6c56e083a9adaf07 end -/
