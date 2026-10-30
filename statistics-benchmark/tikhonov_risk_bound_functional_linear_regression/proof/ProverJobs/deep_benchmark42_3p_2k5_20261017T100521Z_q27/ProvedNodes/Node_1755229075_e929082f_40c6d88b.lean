import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q27.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q27.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q27.ProvedNodes.Node_2203294958_aa644ea9_93f6db00

open MeasureTheory

open MeasureTheory

set_option autoImplicit false in
theorem statopia_math_node_1755229075_e929082f : ∀ {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [SecondCountableTopology H]
    (P : Measure Ω)
    (X : Ω → H) (Y : Ω → ℝ)
    (hXmeas : StronglyMeasurable X)
    (hYmeas : StronglyMeasurable Y)
    (hXsq : Integrable (fun ω ↦ ‖X ω‖ ^ 2) P)
    (hYsq : Integrable (fun ω ↦ (Y ω) ^ 2) P)
    (C : H →L[ℝ] H)
    (hC : ∀ h, C h = ∫ ω, (inner ℝ (X ω) h) • X ω ∂P),
    let g : H := ∫ ω, (Y ω) • X ω ∂P
    (∀ v : H, inner ℝ g v = ∫ ω, Y ω * inner ℝ (X ω) v ∂P) ∧
      (∀ u v : H,
        inner ℝ (C u) v = ∫ ω, inner ℝ (X ω) u * inner ℝ (X ω) v ∂P) := by
  /- @proof-region region.target-node.session.b4bffcad5741db91 begin -/
  intro Ω H iΩ iH1 iH2 iH3 iH4 P X Y hXmeas hYmeas hXsq hYsq C hC

  dsimp only
  constructor
  · intro v
    have hint : Integrable (fun ω => (Y ω) • X ω) P :=
      (statopia_math_node_2203294958_aa644ea9 P X Y hXmeas hYmeas hXsq hYsq v v).1
    have hcomm := ContinuousLinearMap.integral_comp_comm (innerSL ℝ v) hint
    calc inner ℝ (∫ ω, (Y ω) • X ω ∂P) v
        = (innerSL ℝ v) (∫ ω, (Y ω) • X ω ∂P) := by
          rw [innerSL_apply]
          exact real_inner_comm v (∫ ω, (Y ω) • X ω ∂P)
      _ = ∫ ω, (innerSL ℝ v) ((Y ω) • X ω) ∂P := hcomm.symm
      _ = ∫ ω, Y ω * inner ℝ (X ω) v ∂P := by
          have hp : ∀ ω, (innerSL ℝ v) ((Y ω) • X ω) = Y ω * inner ℝ (X ω) v := by
            intro ω
            rw [innerSL_apply, (real_inner_comm v ((Y ω) • X ω)).symm, real_inner_smul_left]
          simp only [hp]
  · intro u v
    have hint : Integrable (fun ω => (inner ℝ (X ω) u) • X ω) P :=
      (statopia_math_node_2203294958_aa644ea9 P X Y hXmeas hYmeas hXsq hYsq u u).2.1
    have hcomm := ContinuousLinearMap.integral_comp_comm (innerSL ℝ v) hint
    calc inner ℝ (C u) v
        = (innerSL ℝ v) (C u) := by
          rw [innerSL_apply]
          exact real_inner_comm v (C u)
      _ = (innerSL ℝ v) (∫ ω, (inner ℝ (X ω) u) • X ω ∂P) := by rw [hC u]
      _ = ∫ ω, (innerSL ℝ v) ((inner ℝ (X ω) u) • X ω) ∂P := hcomm.symm
      _ = ∫ ω, inner ℝ (X ω) u * inner ℝ (X ω) v ∂P := by
          have hp : ∀ ω, (innerSL ℝ v) ((inner ℝ (X ω) u) • X ω)
              = inner ℝ (X ω) u * inner ℝ (X ω) v := by
            intro ω
            rw [innerSL_apply,
              (real_inner_comm v ((inner ℝ (X ω) u) • X ω)).symm, real_inner_smul_left]
          simp only [hp]
  /- @proof-region region.target-node.session.b4bffcad5741db91 end -/
