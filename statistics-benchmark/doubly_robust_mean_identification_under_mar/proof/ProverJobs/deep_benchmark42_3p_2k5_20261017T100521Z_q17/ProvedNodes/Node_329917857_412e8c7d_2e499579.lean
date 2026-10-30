import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q17.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q17.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q17.ProvedNodes.Node_482029874_f417c92e_c8c152fa

open MeasureTheory

open MeasureTheory

set_option autoImplicit false in
theorem statopia_math_node_329917857_412e8c7d : ∀ {Ω 𝒵 : Type*}
    [MeasurableSpace Ω]
    [Fintype 𝒵]
    [MeasurableSpace 𝒵]
    [MeasurableSingletonClass 𝒵]
    (P : Measure Ω)
    [IsProbabilityMeasure P]
    (Z : Ω → 𝒵)
    (Y : Ω → ℝ)
    (hZmeas : Measurable Z)
    (hYmeas : Measurable Y)
    (hYint : Integrable Y P)
    (hZpos : ∀ z, 0 < P {ω | Z ω = z}),
    ∫ ω, Y ω ∂P =
      ∑ z : 𝒵, (P {ω | Z ω = z}).toReal *
        ((∫ ω in {ω | Z ω = z}, Y ω ∂P) / (P {ω | Z ω = z}).toReal) := by
  /- @proof-region region.target-node.session.4c1327dae10d2896 begin -/
  intro Ω 𝒵 _ _ _ _ P _ Z Y hZmeas hYmeas hYint hZpos
  classical
  have hTmeas : ∀ z : 𝒵, MeasurableSet ({ω : Ω | Z ω = z}) := by
    intro z
    have h := hZmeas (measurableSet_singleton z)
    have h' : ({ω : Ω | Z ω = z} : Set Ω) = Z ⁻¹' ({z} : Set 𝒵) := by
      ext ω
      simp
    rw [h']
    exact h
  have hfun_point : ∀ ω : Ω, (∑ z : 𝒵, ({ω : Ω | Z ω = z} : Set Ω).indicator Y ω) = Y ω := by
    intro ω
    have hsingle : (∑ z : 𝒵, ({ω : Ω | Z ω = z} : Set Ω).indicator Y ω)
        = ({ω : Ω | Z ω = Z ω} : Set Ω).indicator Y ω := by
      refine Finset.sum_eq_single (Z ω) ?_ ?_
      · intro z _ hz
        have hmem : ω ∉ ({ω : Ω | Z ω = z} : Set Ω) := by
          simp only [Set.mem_setOf_eq]
          exact fun h => hz h.symm
        simp [hmem]
      · intro h
        exact absurd (Finset.mem_univ (Z ω)) h
    rw [hsingle]
    simp
  have hsplit :=
    (statopia_math_node_482029874_f417c92e P (fun z : 𝒵 => {ω : Ω | Z ω = z}) hTmeas
      (fun _ => Y) (fun _ => hYint)).2
  have hmain : ∫ ω, Y ω ∂P = ∑ z : 𝒵, ∫ ω in {ω : Ω | Z ω = z}, Y ω ∂P := by
    simpa only [hfun_point] using hsplit
  rw [hmain]
  apply Finset.sum_congr rfl
  intro z _
  have hfin : P {ω : Ω | Z ω = z} ≠ ⊤ := measure_ne_top P _
  have hne : (P {ω : Ω | Z ω = z}).toReal ≠ 0 := by
    intro h0
    have hz0 : P {ω : Ω | Z ω = z} = 0 := by
      rw [← ENNReal.ofReal_toReal hfin, h0, ENNReal.ofReal_zero]
    exact absurd hz0 (ne_of_gt (hZpos z))
  have h1 : (P {ω : Ω | Z ω = z}).toReal *
      ((∫ ω in {ω : Ω | Z ω = z}, Y ω ∂P) * (P {ω : Ω | Z ω = z}).toReal⁻¹) =
      (∫ ω in {ω : Ω | Z ω = z}, Y ω ∂P) *
        ((P {ω : Ω | Z ω = z}).toReal * (P {ω : Ω | Z ω = z}).toReal⁻¹) := by
    ring
  rw [div_eq_mul_inv, h1, mul_inv_cancel₀ hne, mul_one]

  /- @proof-region region.target-node.session.4c1327dae10d2896 end -/
