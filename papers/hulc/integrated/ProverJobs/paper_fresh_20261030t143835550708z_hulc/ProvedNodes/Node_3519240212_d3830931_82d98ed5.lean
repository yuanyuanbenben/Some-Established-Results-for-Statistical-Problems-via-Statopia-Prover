import ProverJobs.paper_fresh_20261030t143835550708z_hulc.Vocabulary
import ProverJobs.paper_fresh_20261030t143835550708z_hulc.Base

namespace PaperProofTasks.paper_fresh_20261030t143835550708z_hulc

open _root_.PaperProofTasks.paper_fresh_20261030t143835550708z_hulc.Statlib.Imported
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Statlib.Imported
open _root_.Statlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_3519240212_d3830931 : ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Ω → ℝ) (hU_meas : Measurable U)
    (hU_uniform : Measure.map U P = (volume : Measure ℝ).restrict (Set.Icc 0 1))
    (c : ℝ) (hc_nonneg : 0 ≤ c) (hc_le_one : c ≤ 1),
    P {ω | U ω ≤ c} = ENNReal.ofReal c ∧
      P {ω | c < U ω} = ENNReal.ofReal (1 - c) := by
  /- @proof-region region.target-node.session.83c93b69598194a5 begin -/
  intro Ω _ P _ U hU_meas hU_uniform c hc_nonneg hc_le_one
  have hmap : ∀ s : Set ℝ, MeasurableSet s →
      P (U ⁻¹' s) = (volume : Measure ℝ).restrict (Set.Icc 0 1) s := by
    intro s hs
    rw [← Measure.map_apply hU_meas hs, hU_uniform]
  constructor
  · change P (U ⁻¹' Set.Iic c) = ENNReal.ofReal c
    rw [hmap (Set.Iic c) measurableSet_Iic,
      Measure.restrict_apply measurableSet_Iic]
    have hEq : Set.Iic c ∩ Set.Icc 0 1 = Set.Icc 0 c := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
      constructor
      · rintro ⟨h1, h2, _⟩
        exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h2, h1, le_trans h2 hc_le_one⟩
    rw [hEq, Real.volume_Icc, sub_zero]
  · change P (U ⁻¹' Set.Ioi c) = ENNReal.ofReal (1 - c)
    rw [hmap (Set.Ioi c) measurableSet_Ioi,
      Measure.restrict_apply measurableSet_Ioi]
    have hEq : Set.Ioi c ∩ Set.Icc 0 1 = Set.Ioc c 1 := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
      constructor
      · rintro ⟨h1, _, h2⟩
        exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, le_trans hc_nonneg h1.le, h2⟩
    rw [hEq, Real.volume_Ioc]

  /- @proof-region region.target-node.session.83c93b69598194a5 end -/

end

end Statlib.Imported

