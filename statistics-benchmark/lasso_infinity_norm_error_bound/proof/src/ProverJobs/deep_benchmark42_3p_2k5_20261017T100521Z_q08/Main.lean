import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q08.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q08.ProvedNodes
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q08.Base

open MeasureTheory Matrix ProbabilityTheory

theorem lasso_infinity_norm_error_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n d : ℕ) (hn : 1 ≤ n) (hd : 2 ≤ d)
    (sigma : ℝ) (hsigma : 0 < sigma)
    (X : Matrix (Fin n) (Fin d) ℝ)
    (hcols : ∀ j,
      dotProduct (fun i ↦ X i j) (fun i ↦ X i j) / (n : ℝ) ≤ 1)
    (S : Finset (Fin d))
    (gamma : ℝ) (hgamma : 0 < gamma)
    (hRE : ∀ Delta : Fin d → ℝ,
      (∑ j, if j ∈ S then (0 : ℝ) else |Delta j|) ≤
          3 * (∑ j, if j ∈ S then |Delta j| else (0 : ℝ)) →
      (⨆ j, |(((n : ℝ)⁻¹ • (X.transpose * X)) *ᵥ Delta) j|) ≥
        gamma * ⨆ j, |Delta j|)
    (thetaStar : Fin d → ℝ)
    (hsupport : ∀ j, j ∉ S → thetaStar j = 0)
    (w : Ω → Fin n → ℝ)
    (hw : ∀ a : Fin n → ℝ,
      HasLaw (fun ω ↦ dotProduct a (w ω))
        (gaussianReal 0
          (Real.toNNReal (sigma ^ 2 * dotProduct a a))) P) :
    let lambda := 4 * sigma *
      Real.sqrt (Real.log (d : ℝ) / (n : ℝ))
    let y : Ω → Fin n → ℝ := fun ω ↦ X *ᵥ thetaStar + w ω
    let objective : Ω → (Fin d → ℝ) → ℝ := fun ω theta ↦
      dotProduct (y ω - X *ᵥ theta) (y ω - X *ᵥ theta) /
          (2 * (n : ℝ)) +
        lambda * ∑ j, |theta j|
    let minimizers : Ω → Set (Fin d → ℝ) := fun ω ↦
      {theta | ∀ eta, objective ω theta ≤ objective ω eta}
    let good : Set Ω := {ω | ∀ thetaHat ∈ minimizers ω,
      (⨆ j, |(thetaHat - thetaStar) j|) ≤
        6 * sigma / gamma *
          Real.sqrt (Real.log (d : ℝ) / (n : ℝ))}
    NullMeasurableSet good P ∧
      P good ≥ ENNReal.ofReal (1 - 2 / (d : ℝ))
:= by
  /- @proof-region region.root.7ed55bcc36f1 begin -/
  dsimp only
  have hdot : ∀ v : Fin n → ℝ, v ⬝ᵥ v = ∑ i, v i ^ 2 := by
    intro v
    simp only [dotProduct, pow_two]
  constructor
  · have hZ :=
      statopia_math_node_11731219_b8d62fc9 n d hn hd sigma hsigma gamma hgamma X thetaStar
    have hAEm : AEMeasurable w P :=
      statopia_math_node_35352085_cac9d037 P n hn sigma hsigma w hw
    have hpre := hAEm.nullMeasurableSet_preimage hZ
    convert hpre using 1
    ext ω
    simp only [Set.mem_preimage, Set.mem_setOf_eq, hdot]
  · refine le_trans
      (statopia_math_node_3084854362_14c87009 P n d hn hd sigma hsigma X hcols w hw)
      (measure_mono ?_)
    intro ω hω thetaHat hmin
    exact
      statopia_math_node_4186121393_be2d5497 n d hn hd sigma hsigma X S gamma hgamma hRE
        thetaStar hsupport (w ω) thetaHat hmin hω
  /- @proof-region region.root.7ed55bcc36f1 end -/
