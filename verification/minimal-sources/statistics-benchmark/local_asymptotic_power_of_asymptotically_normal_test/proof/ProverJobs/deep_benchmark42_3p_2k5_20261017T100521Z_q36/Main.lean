import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q36.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q36.ProvedNodes
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q36.Base

open MeasureTheory ProbabilityTheory Filter Topology

theorem local_asymptotic_power_of_asymptotically_normal_test
    {Ω : Type*} [MeasurableSpace Ω]
    (P : ℕ → ProbabilityMeasure Ω)
    (thetaHat : ℕ → Ω → ℝ)
    (theta₀ h c sigma : ℝ)
    (hsigma : 0 < sigma)
    (hthetaHat : ∀ n, Measurable (thetaHat n))
    (hasymptotic_normality :
      Tendsto
        (fun n ↦
          ProbabilityMeasure.map (P (n + 1))
            (show
              AEMeasurable
                (fun ω ↦
                  Real.sqrt (n + 1 : ℝ) *
                      (thetaHat (n + 1) ω -
                        (theta₀ + h / Real.sqrt (n + 1 : ℝ))) /
                    sigma)
                (P (n + 1)) by
              fun_prop))
        atTop
        (𝓝 (⟨gaussianReal 0 1, inferInstance⟩ :
          ProbabilityMeasure ℝ))) :
    Tendsto
      (fun n ↦
        ENNReal.toReal
          ((P (n + 1) : Measure Ω)
            {ω |
              Real.sqrt (n + 1 : ℝ) *
                  (thetaHat (n + 1) ω - theta₀) /
                sigma >
              c}))
      atTop
      (𝓝
        (1 -
          cdf (gaussianReal 0 1) (c - h / sigma)))
:= by
  /- @proof-region region.root.7f308485c09c begin -/
  set a : ℝ := c - h / sigma with ha
  set gamma : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1, inferInstance⟩ with hgamma
  have hφ : ∀ n : ℕ, AEMeasurable
      (fun ω => Real.sqrt (n + 1 : ℝ) *
        (thetaHat (n + 1) ω - (theta₀ + h / Real.sqrt (n + 1 : ℝ))) / sigma)
      (P (n + 1)) := by
    intro n
    fun_prop
  have hweak : Tendsto (fun n : ℕ => ProbabilityMeasure.map (P (n + 1)) (hφ n)) atTop
      (𝓝 gamma) := by
    rw [hgamma]
    exact hasymptotic_normality
  have hgammaNoAtoms : NoAtoms (gamma : Measure ℝ) := by
    rw [hgamma]
    exact noAtoms_gaussianReal (by norm_num : (1 : NNReal) ≠ 0)
  have haffine : ∀ (n : ℕ) (ω : Ω),
      Real.sqrt (n + 1 : ℝ) *
          (thetaHat (n + 1) ω - (theta₀ + h / Real.sqrt (n + 1 : ℝ))) / sigma +
        h / sigma =
      Real.sqrt (n + 1 : ℝ) * (thetaHat (n + 1) ω - theta₀) / sigma := by
    intro n ω
    have hs : Real.sqrt (n + 1 : ℝ) ≠ 0 := by positivity
    have hσ : sigma ≠ 0 := ne_of_gt hsigma
    field_simp
    ring
  have hset : ∀ n : ℕ,
      (fun ω => Real.sqrt (n + 1 : ℝ) *
        (thetaHat (n + 1) ω - (theta₀ + h / Real.sqrt (n + 1 : ℝ))) / sigma) ⁻¹' Set.Ioi a
        = {ω | Real.sqrt (n + 1 : ℝ) * (thetaHat (n + 1) ω - theta₀) / sigma > c} := by
    intro n
    ext ω
    simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_setOf_eq, ha]
    constructor
    · intro hω
      linarith [haffine n ω]
    · intro hω
      linarith [haffine n ω]
  have hmass : ∀ n : ℕ, ENNReal.toReal ((P (n + 1) : Measure Ω)
        {ω | Real.sqrt (n + 1 : ℝ) * (thetaHat (n + 1) ω - theta₀) / sigma > c})
      = ENNReal.toReal
        ((ProbabilityMeasure.map (P (n + 1)) (hφ n) : Measure ℝ) (Set.Ioi a)) := by
    intro n
    have h1 : (ProbabilityMeasure.map (P (n + 1)) (hφ n) : Measure ℝ) (Set.Ioi a)
        = (P (n + 1) : Measure Ω)
            {ω | Real.sqrt (n + 1 : ℝ) * (thetaHat (n + 1) ω - theta₀) / sigma > c} := by
      rw [ProbabilityMeasure.map_apply' (P (n + 1)) (hφ n) measurableSet_Ioi, hset n]
    rw [h1]
  have hmain := statopia_math_node_1208565295_ba30b8ee
    (fun n : ℕ => ProbabilityMeasure.map (P (n + 1)) (hφ n)) gamma hgammaNoAtoms hweak a
  have hcoe : (gamma : Measure ℝ) = gaussianReal 0 1 := rfl
  simpa only [hmass, hcoe] using hmain
  /- @proof-region region.root.7f308485c09c end -/
