import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q16.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q16.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q16.ProvedNodes.Node_1353280134_668c18e6_a5a2ddf7
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q16.ProvedNodes.Node_359342246_18c0b9ff_8e3dacd9


open MeasureTheory Matrix ProbabilityTheory

open MeasureTheory Matrix ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_2860752011_ddd01222 : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n p : ℕ)
    (X : Matrix (Fin n) (Fin p) ℝ)
    (sigma : ℝ) (hsigma : 0 < sigma)
    (epsilon : Ω → Fin n → ℝ)
    (heps : AEMeasurable epsilon P)
    (hsymm :
      ((1 : Matrix (Fin n) (Fin n) ℝ) - X * (X.transpose * X)⁻¹ * X.transpose).transpose
        = (1 : Matrix (Fin n) (Fin n) ℝ) - X * (X.transpose * X)⁻¹ * X.transpose)
    (hgaussian : ∀ a : Fin n → ℝ,
      HasLaw (fun ω => dotProduct a (epsilon ω))
        (gaussianReal 0 (Real.toNNReal (sigma ^ 2 * dotProduct a a))) P),
    let U : Matrix (Fin n) (Fin n) ℝ :=
      (1 : Matrix (Fin n) (Fin n) ℝ) - X * (X.transpose * X)⁻¹ * X.transpose
    let A : Ω → Fin p → ℝ := fun ω => X.transpose *ᵥ epsilon ω
    let B : Ω → Fin n → ℝ := fun ω => U *ᵥ epsilon ω
    ∀ s : Fin p → ℝ, ∀ u : Fin n → ℝ,
      ∫ ω, Complex.exp
            (Complex.I * ((dotProduct s (A ω) + dotProduct u (B ω) : ℝ) : ℂ)) ∂P
        = Complex.exp
            ((-(sigma ^ 2 * dotProduct (X *ᵥ s + U *ᵥ u) (X *ᵥ s + U *ᵥ u)) / 2 : ℝ) : ℂ) := by
  /- @proof-region region.target-node.session.4af34d19797d0d25 begin -/
  intro Ω _ P _ n p X sigma hsigma epsilon heps hsymm hgaussian
  dsimp only
  intro s u
  set U : Matrix (Fin n) (Fin n) ℝ :=
    (1 : Matrix (Fin n) (Fin n) ℝ) - X * (X.transpose * X)⁻¹ * X.transpose with hU
  set a : Fin n → ℝ := X *ᵥ s + U *ᵥ u with ha
  have hUsymm : U.transpose = U := by simpa only [← hU] using hsymm
  have h1 : Matrix.vecMul s X.transpose = X *ᵥ s := by
    rw [← Matrix.mulVec_transpose (A := X.transpose) (x := s)]
    simp
  have h2 : Matrix.vecMul u U = U *ᵥ u := by
    rw [← Matrix.mulVec_transpose (A := U) (x := u), hUsymm]
  have hpt : ∀ ω : Ω, dotProduct s (X.transpose *ᵥ epsilon ω) + dotProduct u (U *ᵥ epsilon ω)
      = dotProduct a (epsilon ω) := by
    intro ω
    rw [ha, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec, h1, h2]
    simp only [dotProduct, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  simp only [hpt]
  have hmap : Measure.map (fun ω => dotProduct a (epsilon ω)) P
      = gaussianReal 0 (Real.toNNReal (sigma ^ 2 * dotProduct a a)) := (hgaussian a).map_eq
  have hφ_meas : AEMeasurable (fun ω => dotProduct a (epsilon ω)) P := by
    by_contra h
    rw [MeasureTheory.Measure.map_of_not_aemeasurable h] at hmap
    have hne : gaussianReal 0 (Real.toNNReal (sigma ^ 2 * dotProduct a a)) ≠ 0 := by
      intro h0
      have hone : gaussianReal 0 (Real.toNNReal (sigma ^ 2 * dotProduct a a)) Set.univ = 1 :=
        measure_univ
      rw [h0] at hone
      simpa using hone
    exact hne hmap.symm
  have hf_aesm : AEStronglyMeasurable (fun x : ℝ => Complex.exp (Complex.I * (x : ℂ)))
      (Measure.map (fun ω => dotProduct a (epsilon ω)) P) :=
    (by continuity : Continuous (fun x : ℝ => Complex.exp (Complex.I * (x : ℂ)))).aestronglyMeasurable
  have hint : ∫ ω, Complex.exp (Complex.I * ((dotProduct a (epsilon ω) : ℝ) : ℂ)) ∂P
      = ∫ x : ℝ, Complex.exp (Complex.I * (x : ℂ))
          ∂(gaussianReal 0 (Real.toNNReal (sigma ^ 2 * dotProduct a a))) := by
    rw [← hmap]
    exact (MeasureTheory.integral_map
      (φ := fun ω => dotProduct a (epsilon ω))
      (f := fun x : ℝ => Complex.exp (Complex.I * (x : ℂ))) hφ_meas hf_aesm).symm
  have hchar1 : ∫ x : ℝ, Complex.exp (Complex.I * (x : ℂ))
      ∂(gaussianReal 0 (Real.toNNReal (sigma ^ 2 * dotProduct a a)))
      = MeasureTheory.charFun
          (gaussianReal 0 (Real.toNNReal (sigma ^ 2 * dotProduct a a))) (1 : ℝ) := by
    rw [MeasureTheory.charFun_eq_integral_innerProbChar]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [BoundedContinuousFunction.innerProbChar_apply]
    simp [mul_comm]
  have hchar2 : MeasureTheory.charFun
        (gaussianReal 0 (Real.toNNReal (sigma ^ 2 * dotProduct a a))) (1 : ℝ)
      = Complex.exp
          ((-(Real.toNNReal (sigma ^ 2 * dotProduct a a) : ℝ) / 2 : ℝ) : ℂ) := by
    rw [ProbabilityTheory.charFun_gaussianReal]
    congr 1
    push_cast
    ring
  rw [hint, hchar1, hchar2]
  have hnonneg : 0 ≤ sigma ^ 2 * dotProduct a a := by
    have hd : (0 : ℝ) ≤ dotProduct a a := by
      simpa using dotProduct_star_self_nonneg (v := a)
    exact mul_nonneg (sq_nonneg sigma) hd
  rw [Real.coe_toNNReal _ hnonneg]
  /- @proof-region region.target-node.session.4af34d19797d0d25 end -/
