import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q18.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q18.Base

open MeasureTheory ProbabilityTheory Filter

open MeasureTheory ProbabilityTheory Filter

set_option autoImplicit false in
theorem statopia_math_node_1542068916_7a306912 : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (k : ℕ) (U : Fin k → Ω → ℝ)
    (hU_meas : ∀ i, Measurable (U i))
    (hU_uniform : ∀ i, MeasureTheory.pdf.IsUniform (U i) (Set.Ioo (0 : ℝ) 1) P),
    (∀ i : Fin k, Measure.map (U i) P =
        (volume (Set.Ioo (0 : ℝ) 1))⁻¹ • volume.restrict (Set.Ioo (0 : ℝ) 1)) ∧
      (∀ i : Fin k, P {ω | U i ω ∈ Set.Ioo (0 : ℝ) 1} = 1) := by
  /- @proof-region region.target-node.session.2826663f4818543b begin -/
  intro Ω _ P _ k U hU_meas hU_uniform
  refine ⟨fun i => hU_uniform i, fun i => ?_⟩
  have hvol : volume (Set.Ioo (0 : ℝ) 1) = 1 := by
    rw [Real.volume_Ioo, sub_zero, ENNReal.ofReal_one]
  have hpre : P {ω | U i ω ∈ Set.Ioo (0 : ℝ) 1} =
      volume (Set.Ioo (0 : ℝ) 1 ∩ Set.Ioo (0 : ℝ) 1) / volume (Set.Ioo (0 : ℝ) 1) :=
    @MeasureTheory.pdf.IsUniform.measure_preimage ℝ _ volume Ω _
      P (U i) (Set.Ioo (0 : ℝ) 1) (by rw [hvol]; simp) (by rw [hvol]; simp)
      (hU_uniform i) (Set.Ioo (0 : ℝ) 1) measurableSet_Ioo
  rw [hpre, Set.inter_self, hvol]
  simp
  /- @proof-region region.target-node.session.2826663f4818543b end -/
