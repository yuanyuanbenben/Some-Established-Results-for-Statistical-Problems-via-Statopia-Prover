import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q15.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q15.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q15.ProvedNodes.Node_3660083059_ee3ca287_a16ffa73

open Filter MeasureTheory ProbabilityTheory

open Filter MeasureTheory ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_3925726211_24458778 : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (X : ℕ → Ω → Bool)
    (hxi_meas : ∀ i, Measurable (fun ω => if X i ω then (1 : ℝ) else 0))
    (hxi_law : ∀ i, Measure.map (fun ω => if X i ω then (1 : ℝ) else 0) P
        = Measure.map (fun b : Bool => if b then (1 : ℝ) else 0)
            (PMF.bernoulli ⟨θ, hθ0.le⟩ (by exact_mod_cast hθ1.le)).toMeasure)
    (hY_int : ∀ i, Integrable (fun ω => (if X i ω then (1 : ℝ) else 0) - θ) P),
    (∀ i, ∫ ω, ((if X i ω then (1 : ℝ) else 0) - θ) ∂P = 0)
    ∧ (∀ i, ∫ ω, (((if X i ω then (1 : ℝ) else 0) - θ) ^ 2) ∂P = θ * (1 - θ))
    ∧ (∀ i, ∫ ω, |((if X i ω then (1 : ℝ) else 0) - θ)| ^ 3 ∂P
        = θ * (1 - θ) * (θ ^ 2 + (1 - θ) ^ 2))
    ∧ (∀ i, MemLp (fun ω => (if X i ω then (1 : ℝ) else 0) - θ) 3 P)

    ∧ (∀ (i : ℕ) (ω : Ω), |((if X i ω then (1 : ℝ) else 0) - θ)| ≤ 1)
    ∧ (Real.sqrt (θ * (1 - θ)) ^ 2 = θ * (1 - θ))
    ∧ (0 ≤ θ * (1 - θ) * (θ ^ 2 + (1 - θ) ^ 2))
    ∧ (∀ i, ∫ ω, |((if X i ω then (1 : ℝ) else 0) - θ)| ^ 3 ∂P
        = θ * (1 - θ) * (θ ^ 2 + (1 - θ) ^ 2)) := by
  /- @proof-region region.target-node.session.f54c65f4d5ef3170 begin -/
  intro Ω instΩ P instP θ hθ0 hθ1 X hxi_meas hxi_law hY_int
  have hmean : ∀ i, ∫ ω, (if X i ω then (1 : ℝ) else 0) ∂P = θ := by
    intro i
    have hbool : ∫ b : Bool, (if b then (1 : ℝ) else 0)
        ∂(PMF.bernoulli ⟨θ, hθ0.le⟩ (by exact_mod_cast hθ1.le)).toMeasure = θ := by
      rw [show (fun b : Bool => (if b then (1 : ℝ) else 0))
            = (fun b : Bool => (bif b then (1 : ℝ) else 0)) from by
          funext b; cases b <;> rfl]
      have e := PMF.bernoulli_expectation (p := ⟨θ, hθ0.le⟩) (by exact_mod_cast hθ1.le)
      simpa using e
    calc ∫ ω, (if X i ω then (1 : ℝ) else 0) ∂P
        = ∫ y, (fun y : ℝ => y) y
            ∂Measure.map (fun ω => if X i ω then (1 : ℝ) else 0) P :=
          (integral_map (hxi_meas i).aemeasurable aestronglyMeasurable_id).symm
      _ = ∫ y, (fun y : ℝ => y) y
            ∂Measure.map (fun b : Bool => if b then (1 : ℝ) else 0)
              (PMF.bernoulli ⟨θ, hθ0.le⟩ (by exact_mod_cast hθ1.le)).toMeasure := by
          rw [hxi_law i]
      _ = ∫ b, (fun y : ℝ => y) ((if b then (1 : ℝ) else 0))
            ∂(PMF.bernoulli ⟨θ, hθ0.le⟩ (by exact_mod_cast hθ1.le)).toMeasure :=
          integral_map (f := fun y : ℝ => y)
            (measurable_of_finite (fun b : Bool => if b then (1 : ℝ) else 0)).aemeasurable
            aestronglyMeasurable_id
      _ = θ := hbool
  have hξ_int : ∀ i, Integrable (fun ω => (if X i ω then (1 : ℝ) else 0)) P := by
    intro i
    have h1 := (hY_int i).add (integrable_const θ)
    have h2 : ((fun ω => (if X i ω then (1 : ℝ) else 0) - θ) + (fun _ : Ω => θ))
        = (fun ω => (if X i ω then (1 : ℝ) else 0)) := by
      funext ω
      change (if X i ω = true then (1 : ℝ) else 0) - θ + θ = (if X i ω = true then (1 : ℝ) else 0)
      ring
    rw [h2] at h1
    exact h1
  have hone : ∫ ω, (1 : ℝ) ∂P = 1 := by
    rw [integral_const]
    simp [Measure.real]
  have hξc_int : ∀ i, Integrable (fun ω => (1 : ℝ) - (if X i ω then (1 : ℝ) else 0)) P := by
    intro i
    exact (integrable_const (1 : ℝ)).sub (hξ_int i)
  have hone_sub : ∀ i, ∫ ω, ((1 : ℝ) - (if X i ω then (1 : ℝ) else 0)) ∂P = 1 - θ := by
    intro i
    rw [integral_sub (integrable_const (1 : ℝ)) (hξ_int i), hone, hmean i]
  have hmom1 : ∀ i, ∫ ω, ((if X i ω then (1 : ℝ) else 0) - θ) ∂P = 0 := by
    intro i
    rw [integral_sub (hξ_int i) (integrable_const θ), hmean i, integral_const]
    simp [Measure.real]
  have hmom2 : ∀ i, ∫ ω, (((if X i ω then (1 : ℝ) else 0) - θ) ^ 2) ∂P = θ * (1 - θ) := by
    intro i
    rw [show (fun ω => (((if X i ω then (1 : ℝ) else 0) - θ) ^ 2))
          = (fun ω => ((1 - 2 * θ) * (if X i ω then (1 : ℝ) else 0) + θ ^ 2)) from by
        funext ω
        by_cases h : X i ω = true
        · have hξ : (if X i ω then (1 : ℝ) else 0) = 1 := by simp [h]
          rw [hξ]; ring
        · have hξ : (if X i ω then (1 : ℝ) else 0) = 0 := by simp [h]
          rw [hξ]; ring]
    rw [integral_add ((hξ_int i).const_mul (1 - 2 * θ)) (integrable_const (θ ^ 2))]
    rw [integral_const_mul, hmean i, integral_const]
    simp [Measure.real]
    ring
  have hmom3 : ∀ i, ∫ ω, |((if X i ω then (1 : ℝ) else 0) - θ)| ^ 3 ∂P
      = θ * (1 - θ) * (θ ^ 2 + (1 - θ) ^ 2) := by
    intro i
    rw [show (fun ω => |((if X i ω then (1 : ℝ) else 0) - θ)| ^ 3)
          = (fun ω => ((if X i ω then (1 : ℝ) else 0) * (1 - θ) ^ 3
              + (1 - (if X i ω then (1 : ℝ) else 0)) * θ ^ 3)) from by
        funext ω
        by_cases h : X i ω = true
        · have hξ : (if X i ω then (1 : ℝ) else 0) = 1 := by simp [h]
          rw [hξ, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - θ)]
          ring
        · have hξ : (if X i ω then (1 : ℝ) else 0) = 0 := by simp [h]
          rw [hξ, zero_sub, abs_neg, abs_of_pos hθ0]
          ring]
    rw [integral_add ((hξ_int i).mul_const ((1 - θ) ^ 3)) ((hξc_int i).mul_const (θ ^ 3))]
    rw [integral_mul_const, integral_mul_const, hmean i, hone_sub i]
    ring
  have hbd : ∀ (i : ℕ) (ω : Ω), |((if X i ω then (1 : ℝ) else 0) - θ)| ≤ 1 := by
    intro i ω
    by_cases h : X i ω = true
    · have hξ : (if X i ω then (1 : ℝ) else 0) = 1 := by simp [h]
      rw [hξ, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - θ)]
      linarith
    · have hξ : (if X i ω then (1 : ℝ) else 0) = 0 := by simp [h]
      rw [hξ, zero_sub, abs_neg, abs_of_pos hθ0]
      linarith
  have hmemLp : ∀ i, MemLp (fun ω => (if X i ω then (1 : ℝ) else 0) - θ) 3 P := by
    intro i
    apply MemLp.of_bound ((hxi_meas i).sub measurable_const).aestronglyMeasurable 1
    filter_upwards with ω
    rw [Real.norm_eq_abs]
    exact hbd i ω
  refine ⟨hmom1, hmom2, hmom3, hmemLp, hbd, ?_, ?_, hmom3⟩
  · rw [Real.sq_sqrt (le_of_lt (mul_pos hθ0 (by linarith)))]
  · exact mul_nonneg (le_of_lt (mul_pos hθ0 (by linarith)))
      (add_nonneg (sq_nonneg θ) (sq_nonneg (1 - θ)))
  /- @proof-region region.target-node.session.f54c65f4d5ef3170 end -/
