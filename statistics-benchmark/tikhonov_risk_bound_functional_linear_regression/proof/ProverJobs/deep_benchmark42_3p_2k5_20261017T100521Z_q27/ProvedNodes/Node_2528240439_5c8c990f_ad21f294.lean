import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q27.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q27.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q27.ProvedNodes.Node_1755229075_e929082f_40c6d88b
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q27.ProvedNodes.Node_2203294958_aa644ea9_93f6db00


open MeasureTheory

open MeasureTheory

set_option autoImplicit false in
theorem statopia_math_node_2528240439_5c8c990f : ∀ {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [SecondCountableTopology H]
    (P : Measure Ω)
    (X : Ω → H) (Y : Ω → ℝ)
    (hXmeas : StronglyMeasurable X)
    (hYmeas : StronglyMeasurable Y)
    (hXsq : Integrable (fun ω ↦ ‖X ω‖ ^ 2) P)
    (hYsq : Integrable (fun ω ↦ (Y ω) ^ 2) P)
    (C : H →L[ℝ] H)
    (hC : ∀ h, C h = ∫ ω, (inner ℝ (X ω) h) • X ω ∂P)
    (alpha : ℝ)
    (Ainv : H →L[ℝ] H)
    (hright : (C + alpha • ContinuousLinearMap.id ℝ H).comp Ainv =
      ContinuousLinearMap.id ℝ H),
    let g : H := ∫ ω, (Y ω) • X ω ∂P
    let bAlpha : H := Ainv g
    ∀ d : H,
      (∫ ω, (Y ω - inner ℝ (X ω) bAlpha) * inner ℝ (X ω) d ∂P)
        = alpha * inner ℝ bAlpha d := by
  /- @proof-region region.target-node.session.c08a62702b641a6c begin -/
  intro Ω H _ _ _ _ _ P X Y hXmeas hYmeas hXsq hYsq C hC alpha Ainv hright
  dsimp only
  intro d
  obtain ⟨_, _, h3, h4, _⟩ :=
    statopia_math_node_2203294958_aa644ea9 P X Y hXmeas hYmeas hXsq hYsq
      (Ainv (∫ ω, (Y ω) • X ω ∂P)) d
  obtain ⟨hId1, hId2⟩ :=
    statopia_math_node_1755229075_e929082f P X Y hXmeas hYmeas hXsq hYsq C hC
  have hfun :
      (fun ω => (Y ω - inner ℝ (X ω) (Ainv (∫ ω, (Y ω) • X ω ∂P))) * inner ℝ (X ω) d)
        = (fun ω => Y ω * inner ℝ (X ω) d
            - inner ℝ (X ω) (Ainv (∫ ω, (Y ω) • X ω ∂P)) * inner ℝ (X ω) d) := by
    funext ω
    ring
  have hsplit :
      (∫ ω, (Y ω * inner ℝ (X ω) d
          - inner ℝ (X ω) (Ainv (∫ ω, (Y ω) • X ω ∂P)) * inner ℝ (X ω) d) ∂P)
        = (∫ ω, Y ω * inner ℝ (X ω) d ∂P)
          - (∫ ω, inner ℝ (X ω) (Ainv (∫ ω, (Y ω) • X ω ∂P)) * inner ℝ (X ω) d ∂P) :=
    integral_sub h3 h4
  have hnorm :
      C (Ainv (∫ ω, (Y ω) • X ω ∂P)) + alpha • Ainv (∫ ω, (Y ω) • X ω ∂P)
        = ∫ ω, (Y ω) • X ω ∂P := by
    have h := congrArg (fun L : H →L[ℝ] H => L (∫ ω, (Y ω) • X ω ∂P)) hright
    simpa using h
  have hGC :
      (∫ ω, (Y ω) • X ω ∂P) - C (Ainv (∫ ω, (Y ω) • X ω ∂P))
        = alpha • Ainv (∫ ω, (Y ω) • X ω ∂P) := by
    rw [sub_eq_iff_eq_add, add_comm]
    exact hnorm.symm
  rw [hfun, hsplit, ← hId1 d, ← hId2 (Ainv (∫ ω, (Y ω) • X ω ∂P)) d, ← inner_sub_left, hGC,
    real_inner_smul_left]
  /- @proof-region region.target-node.session.c08a62702b641a6c end -/
