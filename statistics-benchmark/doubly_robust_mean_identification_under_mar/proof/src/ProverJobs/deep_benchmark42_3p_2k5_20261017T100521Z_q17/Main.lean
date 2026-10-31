import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q17.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q17.ProvedNodes
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q17.Base

open MeasureTheory

theorem doubly_robust_mean_identification_under_mar
    {Ω 𝒵 : Type*}
    [MeasurableSpace Ω]
    [Fintype 𝒵]
    [MeasurableSpace 𝒵]
    [MeasurableSingletonClass 𝒵]
    (P : Measure Ω)
    [IsProbabilityMeasure P]
    (R : Ω → Bool)
    (Z : Ω → 𝒵)
    (Y : Ω → ℝ)
    (hRmeas : Measurable R)
    (hZmeas : Measurable Z)
    (hYmeas : Measurable Y)
    (hYint : Integrable Y P)
    (hZpos : ∀ z, 0 < P {ω | Z ω = z})
    (hMAR :
      ∀ (B : Set ℝ), MeasurableSet B → ∀ r z,
        P {ω | Y ω ∈ B ∧ R ω = r ∧ Z ω = z} * P {ω | Z ω = z} =
          P {ω | Y ω ∈ B ∧ Z ω = z} * P {ω | R ω = r ∧ Z ω = z})
    (m : 𝒵 → ℝ)
    (π : 𝒵 → ℝ)
    (hπpos : ∀ z, 0 < π z)
    (hπle : ∀ z, π z ≤ 1) :
    let m0 : 𝒵 → ℝ := fun z ↦
      (∫ ω in {ω | Z ω = z}, Y ω ∂P) / (P {ω | Z ω = z}).toReal
    let π0 : 𝒵 → ℝ := fun z ↦
      (P {ω | R ω = true ∧ Z ω = z}).toReal / (P {ω | Z ω = z}).toReal
    (∀ z, 0 < π0 z) →
      (m = m0 ∨ π = π0) →
      ∫ ω,
          m (Z ω) +
            (if R ω then (1 : ℝ) else 0) / π (Z ω) * (Y ω - m (Z ω))
        ∂P =
        ∫ ω, Y ω ∂P
:= by
  /- @proof-region region.root.c361f15ac99d begin -/
  intro m0 π0 hπ0pos hcase
  have hpne : ∀ z, π z ≠ 0 := fun z => ne_of_gt (hπpos z)
  have hmaster :=
    (statopia_math_node_2053934716_e66d820a P R Z Y hRmeas hZmeas hYmeas hYint hZpos hMAR m π hpne).2
  have hmean :=
    statopia_math_node_329917857_412e8c7d P Z Y hZmeas hYmeas hYint hZpos
  have hcollapse : ∀ z : 𝒵,
      (P {ω | Z ω = z}).toReal *
        (m z +
          ((P {ω | R ω = true ∧ Z ω = z}).toReal / (P {ω | Z ω = z}).toReal) / π z *
            ((∫ ω in {ω | Z ω = z}, Y ω ∂P) / (P {ω | Z ω = z}).toReal - m z)) =
      (P {ω | Z ω = z}).toReal *
        ((∫ ω in {ω | Z ω = z}, Y ω ∂P) / (P {ω | Z ω = z}).toReal) := by
    intro z
    rcases hcase with hm | hp
    · have hmz : m z = (∫ ω in {ω | Z ω = z}, Y ω ∂P) / (P {ω | Z ω = z}).toReal :=
        congrFun hm z
      rw [hmz, sub_self, mul_zero, add_zero]
    · have hpz : π z = (P {ω | R ω = true ∧ Z ω = z}).toReal / (P {ω | Z ω = z}).toReal :=
        congrFun hp z
      have hne : (P {ω | R ω = true ∧ Z ω = z}).toReal / (P {ω | Z ω = z}).toReal ≠ 0 :=
        ne_of_gt (hπ0pos z)
      rw [hpz, div_self hne, one_mul]
      ring
  rw [hmaster, hmean]
  exact Finset.sum_congr rfl (fun z _ => hcollapse z)
  /- @proof-region region.root.c361f15ac99d end -/
