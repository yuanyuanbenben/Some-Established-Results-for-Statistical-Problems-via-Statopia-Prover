import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q03.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q03.ProvedNodes
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q03.Base

open MeasureTheory Matrix ProbabilityTheory

theorem exact_student_t_distribution_ols_contrast
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n p : ℕ) (hnp : p < n) (hp : 1 ≤ p)
    (X : Matrix (Fin n) (Fin p) ℝ)
    (hX : Function.Injective X.mulVec)
    (betaStar : Fin p → ℝ)
    (sigma : ℝ) (hsigma : 0 < sigma)
    (epsilon : Ω → Fin n → ℝ)
    (hgaussian : ∀ b : Fin n → ℝ,
      HasLaw (fun ω ↦ dotProduct b (epsilon ω))
        (gaussianReal 0
          (Real.toNNReal (sigma ^ 2 * dotProduct b b))) P)
    (a : Fin p → ℝ) (ha : a ≠ 0)
    (c : ℝ) (hnull : dotProduct a betaStar = c) :
    let y : Ω → Fin n → ℝ := fun ω ↦ X *ᵥ betaStar + epsilon ω
    let betaHat : Ω → Fin p → ℝ := fun ω ↦
      (X.transpose * X)⁻¹ *ᵥ (X.transpose *ᵥ y ω)
    let sigmaHatSq : Ω → ℝ := fun ω ↦
      dotProduct (y ω - X *ᵥ betaHat ω)
          (y ω - X *ᵥ betaHat ω) / ((n - p : ℕ) : ℝ)
    let statistic : Ω → ℝ := fun ω ↦
      (dotProduct a (betaHat ω) - c) /
        (Real.sqrt (sigmaHatSq ω) *
          Real.sqrt (dotProduct a ((X.transpose * X)⁻¹ *ᵥ a)))
    let nu : ℝ := ((n - p : ℕ) : ℝ)
    let density : ℝ → ℝ := fun z ↦
      Real.Gamma ((nu + 1) / 2) /
          (Real.sqrt (nu * Real.pi) * Real.Gamma (nu / 2)) *
        Real.rpow (1 + z ^ 2 / nu) (-(nu + 1) / 2)
    let studentT : Measure ℝ :=
      volume.withDensity (fun z ↦ ENNReal.ofReal (density z))
    HasLaw statistic studentT P
:= by
  /- @proof-region region.root.f98874e44894 begin -/
  classical
  have hνpos : (0 : ℝ) < ((n - p : ℕ) : ℝ) := by
    have h : 0 < n - p := by omega
    exact_mod_cast h
  have hdep := statopia_math_node_2828381066_e53af6ac n p X hX a ha
  dsimp only at hdep
  obtain ⟨⟨hMX, hXM⟩, hMsymm, hMpos, hP, hR, huEx, hRu, huu, hqpos⟩ := hdep
  obtain ⟨hPP, hPsymm, hPcol, hPorth, hPfix⟩ := hP
  obtain ⟨hRR, hRsymm, hRorth, hRrange⟩ := hR
  have hdep2 :=
    statopia_math_node_4184677617_2d1d411b n p hnp X hX ((X.transpose * X)⁻¹) rfl
      (1 - X * (X.transpose * X)⁻¹ * X.transpose) rfl hRR hRsymm hRorth hRrange
  obtain ⟨⟨hfinrank, hspaneq⟩, v, hv1, hv2, hvspan, hvRv, hRv⟩ := hdep2
  have hvu : ∀ k : Fin (n - p),
      dotProduct (X *ᵥ ((X.transpose * X)⁻¹ *ᵥ a)) (v k) = 0 := by
    have hsq :
        (∑ k : Fin (n - p),
          (dotProduct (v k) (X *ᵥ ((X.transpose * X)⁻¹ *ᵥ a))) ^ 2) = 0 := by
      rw [← (hRv (X *ᵥ ((X.transpose * X)⁻¹ *ᵥ a))).2, hRu]
      simp [dotProduct]
    intro k
    have hk : (dotProduct (v k) (X *ᵥ ((X.transpose * X)⁻¹ *ᵥ a))) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).1 hsq k (Finset.mem_univ k)
    have hk2 : dotProduct (v k) (X *ᵥ ((X.transpose * X)⁻¹ *ᵥ a)) *
        dotProduct (v k) (X *ᵥ ((X.transpose * X)⁻¹ *ᵥ a)) = 0 := by
      simpa [pow_two] using hk
    have hk0 : dotProduct (v k) (X *ᵥ ((X.transpose * X)⁻¹ *ᵥ a)) = 0 :=
      mul_self_eq_zero.mp hk2
    have hcomm : dotProduct (X *ᵥ ((X.transpose * X)⁻¹ *ᵥ a)) (v k) =
        dotProduct (v k) (X *ᵥ ((X.transpose * X)⁻¹ *ᵥ a)) := by
      simp only [dotProduct]
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    rw [hcomm, hk0]
  
  have hZV :
      HasLaw
        (fun ω =>
          (dotProduct (X *ᵥ ((X.transpose * X)⁻¹ *ᵥ a)) (epsilon ω) /
              (sigma * Real.sqrt (dotProduct a ((X.transpose * X)⁻¹ *ᵥ a))),
            ∑ k : Fin (n - p), (dotProduct (v k) (epsilon ω) / sigma) ^ 2))
        ((gaussianReal 0 1).prod
          (volume.withDensity
            (fun s => ENNReal.ofReal (gammaConvDensity (((n - p : ℕ) : ℝ) / 2) s)))) P := by
    exact statopia_math_node_455327756_5baa9f36 P n p hnp X hX a ha sigma hsigma epsilon
      hgaussian v hv1 hv2 hvu huu hqpos
  
  have hT :=
    statopia_math_node_2309641057_5900fd9f P (((n - p : ℕ) : ℝ)) hνpos
      (fun ω =>
        dotProduct (X *ᵥ ((X.transpose * X)⁻¹ *ᵥ a)) (epsilon ω) /
          (sigma * Real.sqrt (dotProduct a ((X.transpose * X)⁻¹ *ᵥ a))))
      (fun ω => ∑ k : Fin (n - p), (dotProduct (v k) (epsilon ω) / sigma) ^ 2) hZV
  dsimp only at hT
  let yv : Ω → Fin n → ℝ := fun ω => X *ᵥ betaStar + epsilon ω
  let bh : Ω → Fin p → ℝ := fun ω => (X.transpose * X)⁻¹ *ᵥ (X.transpose *ᵥ yv ω)
  let qq : ℝ := a ⬝ᵥ ((X.transpose * X)⁻¹ *ᵥ a)
  have hpoint : ∀ ω : Ω,
      (a ⬝ᵥ bh ω - c) /
          (Real.sqrt (dotProduct (yv ω - X *ᵥ bh ω) (yv ω - X *ᵥ bh ω) /
                ((n - p : ℕ) : ℝ)) *
            Real.sqrt qq) =
        (X *ᵥ ((X.transpose * X)⁻¹ *ᵥ a)) ⬝ᵥ epsilon ω / (sigma * Real.sqrt qq) /
          Real.sqrt ((∑ k : Fin (n - p), (v k ⬝ᵥ epsilon ω / sigma) ^ 2) /
            ((n - p : ℕ) : ℝ)) := by
    intro ω
    have hres : yv ω - X *ᵥ bh ω
        = (1 - X * (X.transpose * X)⁻¹ * X.transpose) *ᵥ epsilon ω := by
      rw [show yv ω = X *ᵥ betaStar + epsilon ω from rfl]
      rw [show bh ω = (X.transpose * X)⁻¹ *ᵥ
          (X.transpose *ᵥ (X *ᵥ betaStar + epsilon ω)) from rfl]
      rw [Matrix.mulVec_add X.transpose (X *ᵥ betaStar) (epsilon ω)]
      rw [Matrix.mulVec_mulVec betaStar X.transpose X]
      rw [Matrix.mulVec_add ((X.transpose * X)⁻¹)
        ((X.transpose * X) *ᵥ betaStar) (X.transpose *ᵥ epsilon ω)]
      rw [Matrix.mulVec_mulVec betaStar ((X.transpose * X)⁻¹) (X.transpose * X)]
      rw [hMX, Matrix.one_mulVec]
      rw [Matrix.mulVec_add X betaStar
        ((X.transpose * X)⁻¹ *ᵥ (X.transpose *ᵥ epsilon ω))]
      rw [Matrix.mulVec_mulVec (X.transpose *ᵥ epsilon ω) X ((X.transpose * X)⁻¹)]
      rw [Matrix.mulVec_mulVec (epsilon ω) (X * (X.transpose * X)⁻¹) X.transpose]
      rw [Matrix.sub_mulVec (1 : Matrix (Fin n) (Fin n) ℝ)
          (X * (X.transpose * X)⁻¹ * X.transpose) (epsilon ω), Matrix.one_mulVec]
      abel
    have hsig2 : sigma ^ 2 ≠ 0 := pow_ne_zero 2 hsigma.ne'
    have hW :
        (∑ k : Fin (n - p), (v k ⬝ᵥ epsilon ω / sigma) ^ 2)
          = (∑ k : Fin (n - p), (v k ⬝ᵥ epsilon ω) ^ 2) / sigma ^ 2 := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl (fun k _ => by rw [div_pow])
    have hS :
        (∑ k : Fin (n - p), (v k ⬝ᵥ epsilon ω) ^ 2)
          = sigma ^ 2 * (∑ k : Fin (n - p), (v k ⬝ᵥ epsilon ω / sigma) ^ 2) := by
      rw [hW]
      field_simp
    have hsqrt :
        Real.sqrt (dotProduct (yv ω - X *ᵥ bh ω) (yv ω - X *ᵥ bh ω) /
            ((n - p : ℕ) : ℝ))
          = sigma * Real.sqrt
              ((∑ k : Fin (n - p), (v k ⬝ᵥ epsilon ω / sigma) ^ 2) /
                ((n - p : ℕ) : ℝ)) := by
      rw [hres, (hRv (epsilon ω)).2, hS]
      rw [show sigma ^ 2 *
            (∑ k : Fin (n - p), (v k ⬝ᵥ epsilon ω / sigma) ^ 2) / ((n - p : ℕ) : ℝ)
          = sigma ^ 2 * ((∑ k : Fin (n - p), (v k ⬝ᵥ epsilon ω / sigma) ^ 2) /
              ((n - p : ℕ) : ℝ)) from by ring]
      rw [Real.sqrt_mul (sq_nonneg sigma), Real.sqrt_sq hsigma.le]
    have hbeta : bh ω = betaStar + (X.transpose * X)⁻¹ *ᵥ (X.transpose *ᵥ epsilon ω) := by
      rw [show bh ω = (X.transpose * X)⁻¹ *ᵥ
          (X.transpose *ᵥ (X *ᵥ betaStar + epsilon ω)) from rfl]
      rw [Matrix.mulVec_add X.transpose (X *ᵥ betaStar) (epsilon ω)]
      rw [Matrix.mulVec_mulVec betaStar X.transpose X]
      rw [Matrix.mulVec_add ((X.transpose * X)⁻¹)
        ((X.transpose * X) *ᵥ betaStar) (X.transpose *ᵥ epsilon ω)]
      rw [Matrix.mulVec_mulVec betaStar ((X.transpose * X)⁻¹) (X.transpose * X)]
      rw [hMX, Matrix.one_mulVec]
    have hTT : X.transpose.transpose = X := rfl
    have hnum :
        a ⬝ᵥ bh ω - c = (X *ᵥ ((X.transpose * X)⁻¹ *ᵥ a)) ⬝ᵥ epsilon ω := by
      rw [hbeta, dotProduct_add, hnull]
      have hcut : c + a ⬝ᵥ ((X.transpose * X)⁻¹ *ᵥ (X.transpose *ᵥ epsilon ω)) - c
          = a ⬝ᵥ ((X.transpose * X)⁻¹ *ᵥ (X.transpose *ᵥ epsilon ω)) := by abel
      rw [hcut]
      rw [Matrix.dotProduct_mulVec a ((X.transpose * X)⁻¹) (X.transpose *ᵥ epsilon ω)]
      rw [← Matrix.mulVec_transpose ((X.transpose * X)⁻¹) a, hMsymm]
      rw [Matrix.dotProduct_mulVec ((X.transpose * X)⁻¹ *ᵥ a) X.transpose (epsilon ω)]
      rw [← Matrix.mulVec_transpose X.transpose ((X.transpose * X)⁻¹ *ᵥ a), hTT]
    rw [hnum, hsqrt]
    simp only [div_eq_mul_inv, _root_.mul_inv_rev]
    ring
  
  
  
  
  refine hT.congr ?_
  filter_upwards with ω
  exact hpoint ω
  /- @proof-region region.root.f98874e44894 end -/
