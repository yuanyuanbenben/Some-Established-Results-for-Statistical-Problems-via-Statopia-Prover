import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q27.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q27.ProvedNodes
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q27.Base

open MeasureTheory

theorem tikhonov_risk_bound_functional_linear_regression
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [SecondCountableTopology H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → H) (Y : Ω → ℝ)
    (hXmeas : StronglyMeasurable X)
    (hYmeas : StronglyMeasurable Y)
    (hXsq : Integrable (fun ω ↦ ‖X ω‖ ^ 2) P)
    (hYsq : Integrable (fun ω ↦ (Y ω) ^ 2) P)
    (C : H →L[ℝ] H)
    (hC : ∀ h, C h = ∫ ω, (inner ℝ (X ω) h) • X ω ∂P)
    (alpha : ℝ) (halpha : 0 < alpha)
    (Ainv : H →L[ℝ] H)
    (hleft : Ainv.comp
        (C + alpha • ContinuousLinearMap.id ℝ H) =
      ContinuousLinearMap.id ℝ H)
    (hright : (C + alpha • ContinuousLinearMap.id ℝ H).comp Ainv =
      ContinuousLinearMap.id ℝ H) :
    let g : H := ∫ ω, (Y ω) • X ω ∂P
    let Q : H → ℝ := fun b ↦
      (∫ ω, (Y ω - inner ℝ (X ω) b) ^ 2 ∂P) +
        alpha * ‖b‖ ^ 2
    let bAlpha := Ainv g
    ∀ b, Q b ≥ Q bAlpha + alpha * ‖b - bAlpha‖ ^ 2
:= by
  /- @proof-region region.root.9d7aa57255fe begin -/
  dsimp only
  intro b
  have h := statopia_math_node_2066443448_6390c552 P X Y hXmeas hYmeas hXsq hYsq
    C hC alpha Ainv hright
  dsimp only at h
  have hb := h (b - Ainv (∫ ω, (Y ω) • X ω ∂P))
  have hd : Ainv (∫ ω, (Y ω) • X ω ∂P) + (b - Ainv (∫ ω, (Y ω) • X ω ∂P)) = b := by
    abel
  rw [hd] at hb
  have hI : 0 ≤ ∫ ω, (inner ℝ (X ω) (b - Ainv (∫ ω, (Y ω) • X ω ∂P))) ^ 2 ∂P :=
    integral_nonneg
      (fun ω => sq_nonneg (inner ℝ (X ω) (b - Ainv (∫ ω, (Y ω) • X ω ∂P))))
  linarith
  /- @proof-region region.root.9d7aa57255fe end -/
