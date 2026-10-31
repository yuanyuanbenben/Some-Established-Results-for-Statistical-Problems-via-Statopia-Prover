import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q27.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q27.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q27.ProvedNodes.Node_2203294958_aa644ea9_93f6db00
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q27.ProvedNodes.Node_2528240439_5c8c990f_ad21f294


open MeasureTheory

open MeasureTheory

set_option autoImplicit false in
theorem statopia_math_node_2066443448_6390c552 : ∀ {Ω H : Type*} [MeasurableSpace Ω]
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
    let Q : H → ℝ := fun b ↦
      (∫ ω, (Y ω - inner ℝ (X ω) b) ^ 2 ∂P) + alpha * ‖b‖ ^ 2
    let bAlpha : H := Ainv g
    ∀ d : H,
      Q (bAlpha + d) = Q bAlpha + (∫ ω, (inner ℝ (X ω) d) ^ 2 ∂P) + alpha * ‖d‖ ^ 2 := by
  /- @proof-region region.target-node.session.16dd16fb3495fa17 begin -/
  intro Ω H _instΩ _instNG _instIP _instCS _instSCT P X Y hXmeas hYmeas hXsq hYsq C hC alpha Ainv hright
  dsimp only
  intro d
  set bAlpha : H := Ainv (∫ ω, (Y ω) • X ω ∂P) with hbAlpha
  obtain ⟨-, -, hIntYd, hIntBd, hIntRes⟩ :=
    statopia_math_node_2203294958_aa644ea9 P X Y hXmeas hYmeas hXsq hYsq bAlpha d
  obtain ⟨-, -, -, hIntDD, -⟩ :=
    statopia_math_node_2203294958_aa644ea9 P X Y hXmeas hYmeas hXsq hYsq d d
  have hIntD : Integrable (fun ω => (inner ℝ (X ω) d) ^ 2) P := by
    refine hIntDD.congr (Filter.Eventually.of_forall fun ω => ?_)
    show inner ℝ (X ω) d * inner ℝ (X ω) d = (inner ℝ (X ω) d) ^ 2
    ring
  have hIntB : Integrable (fun ω => (Y ω - inner ℝ (X ω) bAlpha) * inner ℝ (X ω) d) P := by
    refine (hIntYd.sub hIntBd).congr (Filter.Eventually.of_forall fun ω => ?_)
    show Y ω * inner ℝ (X ω) d - inner ℝ (X ω) bAlpha * inner ℝ (X ω) d
      = (Y ω - inner ℝ (X ω) bAlpha) * inner ℝ (X ω) d
    ring
  have hInt2B : Integrable (fun ω => 2 * ((Y ω - inner ℝ (X ω) bAlpha) * inner ℝ (X ω) d)) P :=
    hIntB.const_mul 2
  have hfun : (fun ω => (Y ω - inner ℝ (X ω) (bAlpha + d)) ^ 2)
      = fun ω => ((Y ω - inner ℝ (X ω) bAlpha) ^ 2
          - 2 * ((Y ω - inner ℝ (X ω) bAlpha) * inner ℝ (X ω) d)
          + (inner ℝ (X ω) d) ^ 2) := by
    funext ω
    rw [inner_add_right]
    show (Y ω - (inner ℝ (X ω) bAlpha + inner ℝ (X ω) d)) ^ 2
        = (Y ω - inner ℝ (X ω) bAlpha) ^ 2
          - 2 * ((Y ω - inner ℝ (X ω) bAlpha) * inner ℝ (X ω) d)
          + (inner ℝ (X ω) d) ^ 2
    ring
  have step1 : ∫ ω, (Y ω - inner ℝ (X ω) (bAlpha + d)) ^ 2 ∂P
      = ∫ ω, ((Y ω - inner ℝ (X ω) bAlpha) ^ 2
          - 2 * ((Y ω - inner ℝ (X ω) bAlpha) * inner ℝ (X ω) d)
          + (inner ℝ (X ω) d) ^ 2) ∂P := by
    rw [hfun]
  have step2a : ∫ ω, ((Y ω - inner ℝ (X ω) bAlpha) ^ 2
          - 2 * ((Y ω - inner ℝ (X ω) bAlpha) * inner ℝ (X ω) d)
          + (inner ℝ (X ω) d) ^ 2) ∂P
      = ∫ ω, ((Y ω - inner ℝ (X ω) bAlpha) ^ 2
          - 2 * ((Y ω - inner ℝ (X ω) bAlpha) * inner ℝ (X ω) d)) ∂P
        + ∫ ω, (inner ℝ (X ω) d) ^ 2 ∂P :=
    integral_add (hIntRes.sub hInt2B) hIntD
  have step2b : ∫ ω, ((Y ω - inner ℝ (X ω) bAlpha) ^ 2
          - 2 * ((Y ω - inner ℝ (X ω) bAlpha) * inner ℝ (X ω) d)) ∂P
      = ∫ ω, (Y ω - inner ℝ (X ω) bAlpha) ^ 2 ∂P
        - ∫ ω, 2 * ((Y ω - inner ℝ (X ω) bAlpha) * inner ℝ (X ω) d) ∂P :=
    integral_sub hIntRes hInt2B
  have step2c : ∫ ω, 2 * ((Y ω - inner ℝ (X ω) bAlpha) * inner ℝ (X ω) d) ∂P
      = 2 * ∫ ω, (Y ω - inner ℝ (X ω) bAlpha) * inner ℝ (X ω) d ∂P :=
    integral_const_mul (2 : ℝ) (fun ω => (Y ω - inner ℝ (X ω) bAlpha) * inner ℝ (X ω) d)
  have hmain : ∫ ω, (Y ω - inner ℝ (X ω) (bAlpha + d)) ^ 2 ∂P
      = ∫ ω, (Y ω - inner ℝ (X ω) bAlpha) ^ 2 ∂P
        - 2 * ∫ ω, (Y ω - inner ℝ (X ω) bAlpha) * inner ℝ (X ω) d ∂P
        + ∫ ω, (inner ℝ (X ω) d) ^ 2 ∂P := by
    rw [step1, step2a, step2b, step2c]
  have hmix : ∫ ω, (Y ω - inner ℝ (X ω) bAlpha) * inner ℝ (X ω) d ∂P
      = alpha * inner ℝ bAlpha d :=
    statopia_math_node_2528240439_5c8c990f P X Y hXmeas hYmeas hXsq hYsq C hC alpha Ainv hright d
  have hnorm : ‖bAlpha + d‖ ^ 2 = ‖bAlpha‖ ^ 2 + 2 * inner ℝ bAlpha d + ‖d‖ ^ 2 :=
    norm_add_sq_real bAlpha d
  rw [hmain, hmix, hnorm]
  ring
  /- @proof-region region.target-node.session.16dd16fb3495fa17 end -/
