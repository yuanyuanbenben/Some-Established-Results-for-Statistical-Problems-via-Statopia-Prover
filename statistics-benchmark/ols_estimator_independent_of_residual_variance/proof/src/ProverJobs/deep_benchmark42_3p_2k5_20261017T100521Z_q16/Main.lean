import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q16.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q16.ProvedNodes
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q16.Base

open MeasureTheory Matrix ProbabilityTheory

theorem ols_estimator_independent_of_residual_variance
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n p : ℕ) (hnp : p < n) (hp : 1 ≤ p)
    (X : Matrix (Fin n) (Fin p) ℝ)
    (hX : Function.Injective X.mulVec)
    (betaStar : Fin p → ℝ)
    (sigma : ℝ) (hsigma : 0 < sigma)
    (epsilon : Ω → Fin n → ℝ)
    (hgaussian : ∀ a : Fin n → ℝ,
      HasLaw (fun ω ↦ dotProduct a (epsilon ω))
        (gaussianReal 0
          (Real.toNNReal (sigma ^ 2 * dotProduct a a))) P) :
    let y : Ω → Fin n → ℝ := fun ω ↦ X *ᵥ betaStar + epsilon ω
    let betaHat : Ω → Fin p → ℝ := fun ω ↦
      (X.transpose * X)⁻¹ *ᵥ (X.transpose *ᵥ y ω)
    let sigmaHatSq : Ω → ℝ := fun ω ↦
      dotProduct (y ω - X *ᵥ betaHat ω)
          (y ω - X *ᵥ betaHat ω) / ((n - p : ℕ) : ℝ)
    IndepFun betaHat sigmaHatSq P
:= by
  /- @proof-region region.root.5552f9e7edae begin -/
  have hMdet : IsUnit (X.transpose * X).det := by
    have hdet : (X.transpose * X).det ≠ 0 := by
      intro h0
      obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
      have hvec : Matrix.vecMul (X *ᵥ v) X = X.transpose *ᵥ (X *ᵥ v) := by
        simpa using Matrix.vecMul_transpose (A := X.transpose) (x := X *ᵥ v)
      have hdot : (X *ᵥ v) ⬝ᵥ (X *ᵥ v) = v ⬝ᵥ ((X.transpose * X).mulVec v) := by
        rw [Matrix.dotProduct_mulVec (X *ᵥ v) X v, hvec,
          Matrix.mulVec_mulVec v X.transpose X, dotProduct_comm]
      have hzero : v ⬝ᵥ ((X.transpose * X).mulVec v) = 0 := by
        rw [hv]
        simp
      have hXv : X *ᵥ v = 0 := by
        apply dotProduct_self_eq_zero.mp
        rw [hdot]
        exact hzero
      exact hv0 (hX (by simpa using hXv))
    exact isUnit_iff_ne_zero.mpr hdet
  have hmul : (X.transpose * X) * (X.transpose * X)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hMdet
  have hnsing : (X.transpose * X)⁻¹ * (X.transpose * X) = 1 := Matrix.nonsing_inv_mul _ hMdet
  have hMM : (X.transpose * X).transpose = X.transpose * X := by
    simp [Matrix.transpose_mul]
  have hMinvT : ((X.transpose * X)⁻¹).transpose = (X.transpose * X)⁻¹ := by
    have h1 : ((X.transpose * X)⁻¹).transpose * (X.transpose * X) = 1 := by
      have h2 : ((X.transpose * X)⁻¹).transpose * (X.transpose * X).transpose = 1 := by
        rw [← Matrix.transpose_mul, hmul, Matrix.transpose_one]
      rwa [hMM] at h2
    calc ((X.transpose * X)⁻¹).transpose
        = ((X.transpose * X)⁻¹).transpose * 1 := by rw [Matrix.mul_one]
      _ = ((X.transpose * X)⁻¹).transpose * ((X.transpose * X) * (X.transpose * X)⁻¹) := by
            rw [hmul]
      _ = (((X.transpose * X)⁻¹).transpose * (X.transpose * X)) * (X.transpose * X)⁻¹ := by
            rw [← Matrix.mul_assoc]
      _ = 1 * (X.transpose * X)⁻¹ := by rw [h1]
      _ = (X.transpose * X)⁻¹ := by rw [Matrix.one_mul]
  have hsymm : ((1 : Matrix (Fin n) (Fin n) ℝ) - X * (X.transpose * X)⁻¹ * X.transpose).transpose
      = (1 : Matrix (Fin n) (Fin n) ℝ) - X * (X.transpose * X)⁻¹ * X.transpose := by
    simp [Matrix.transpose_mul, hMinvT, Matrix.mul_assoc]
  
  have horth :
      X.transpose * ((1 : Matrix (Fin n) (Fin n) ℝ) - X * (X.transpose * X)⁻¹ * X.transpose) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one]
    have hH : X.transpose * (X * (X.transpose * X)⁻¹ * X.transpose) = X.transpose := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hmul, Matrix.one_mul]
    rw [hH, sub_self]
  have hcoord : ∀ i : Fin n, HasLaw (fun ω => epsilon ω i)
      (gaussianReal 0
        (Real.toNNReal (sigma ^ 2 * (Pi.single i (1 : ℝ)) ⬝ᵥ Pi.single i (1 : ℝ)))) P := by
    intro i
    simpa using hgaussian (Pi.single i (1 : ℝ))
  have heps : AEMeasurable epsilon P := by
    rw [aemeasurable_pi_iff]
    intro i
    obtain ⟨hae⟩ := hcoord i
    exact hae
  have hAB :=
    statopia_math_node_34046222_46bb4793 P n p X sigma hsigma epsilon heps hsymm horth hgaussian
  dsimp only at hAB
  have hf : Measurable (fun a : Fin p → ℝ => betaStar + (X.transpose * X)⁻¹ *ᵥ a) := by
    rw [measurable_pi_iff]
    intro i
    have h : (fun a : Fin p → ℝ => (betaStar + (X.transpose * X)⁻¹ *ᵥ a) i)
        = fun a => betaStar i + ∑ j, (X.transpose * X)⁻¹ i j * a j := by
      funext a
      simp [Matrix.mulVec, dotProduct]
    rw [h]
    measurability
  have hg : Measurable (fun b : Fin n → ℝ => b ⬝ᵥ b / ((n - p : ℕ) : ℝ)) := by
    have h : (fun b : Fin n → ℝ => b ⬝ᵥ b / ((n - p : ℕ) : ℝ))
        = fun b => (∑ i, b i * b i) / ((n - p : ℕ) : ℝ) := by
      funext b
      simp [dotProduct]
    rw [h]
    measurability
  have hcomp := hAB.comp hf hg
  have hC : (X.transpose * X)⁻¹ *ᵥ ((X.transpose * X) *ᵥ betaStar) = betaStar := by
    rw [Matrix.mulVec_mulVec, hnsing, Matrix.one_mulVec]
  have hbeta_pt : ∀ ω : Ω,
      (X.transpose * X)⁻¹ *ᵥ (X.transpose *ᵥ (X *ᵥ betaStar + epsilon ω))
        = betaStar + (X.transpose * X)⁻¹ *ᵥ (X.transpose *ᵥ epsilon ω) := by
    intro ω
    have e1 : X.transpose *ᵥ (X *ᵥ betaStar + epsilon ω)
        = (X.transpose * X) *ᵥ betaStar + X.transpose *ᵥ epsilon ω := by
      rw [Matrix.mulVec_add, Matrix.mulVec_mulVec]
    calc (X.transpose * X)⁻¹ *ᵥ (X.transpose *ᵥ (X *ᵥ betaStar + epsilon ω))
        = (X.transpose * X)⁻¹ *ᵥ
            ((X.transpose * X) *ᵥ betaStar + X.transpose *ᵥ epsilon ω) := by
          rw [e1]
      _ = (X.transpose * X)⁻¹ *ᵥ ((X.transpose * X) *ᵥ betaStar)
            + (X.transpose * X)⁻¹ *ᵥ (X.transpose *ᵥ epsilon ω) := by
          rw [Matrix.mulVec_add]
      _ = betaStar + (X.transpose * X)⁻¹ *ᵥ (X.transpose *ᵥ epsilon ω) := by
          rw [hC]
  have hXb_pt : ∀ ω : Ω,
      X *ᵥ ((X.transpose * X)⁻¹ *ᵥ (X.transpose *ᵥ (X *ᵥ betaStar + epsilon ω)))
        = X *ᵥ betaStar + (X * (X.transpose * X)⁻¹ * X.transpose) *ᵥ epsilon ω := by
    intro ω
    have hW : X *ᵥ ((X.transpose * X)⁻¹ *ᵥ (X.transpose *ᵥ epsilon ω))
        = (X * (X.transpose * X)⁻¹ * X.transpose) *ᵥ epsilon ω :=
      (Matrix.mulVec_mulVec (X.transpose *ᵥ epsilon ω) X ((X.transpose * X)⁻¹)).trans
        (Matrix.mulVec_mulVec (epsilon ω) (X * (X.transpose * X)⁻¹) X.transpose)
    rw [hbeta_pt ω, Matrix.mulVec_add, hW]
  have hdiff_pt : ∀ ω : Ω,
      X *ᵥ betaStar + epsilon ω
          - X *ᵥ ((X.transpose * X)⁻¹ *ᵥ (X.transpose *ᵥ (X *ᵥ betaStar + epsilon ω)))
        = ((1 : Matrix (Fin n) (Fin n) ℝ) - X * (X.transpose * X)⁻¹ * X.transpose)
            *ᵥ epsilon ω := by
    intro ω
    rw [hXb_pt ω, Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  have hbeta_fun :
      (fun ω : Ω => (X.transpose * X)⁻¹ *ᵥ (X.transpose *ᵥ (X *ᵥ betaStar + epsilon ω)))
        = fun ω => betaStar + (X.transpose * X)⁻¹ *ᵥ (X.transpose *ᵥ epsilon ω) :=
    funext hbeta_pt
  have hsig_fun :
      (fun ω : Ω => dotProduct
          (X *ᵥ betaStar + epsilon ω
            - X *ᵥ ((X.transpose * X)⁻¹ *ᵥ (X.transpose *ᵥ (X *ᵥ betaStar + epsilon ω))))
          (X *ᵥ betaStar + epsilon ω
            - X *ᵥ ((X.transpose * X)⁻¹ *ᵥ (X.transpose *ᵥ (X *ᵥ betaStar + epsilon ω))))
          / ((n - p : ℕ) : ℝ))
        = fun ω => dotProduct
          (((1 : Matrix (Fin n) (Fin n) ℝ) - X * (X.transpose * X)⁻¹ * X.transpose) *ᵥ epsilon ω)
          (((1 : Matrix (Fin n) (Fin n) ℝ) - X * (X.transpose * X)⁻¹ * X.transpose) *ᵥ epsilon ω)
          / ((n - p : ℕ) : ℝ) := by
    funext ω
    simp only [hdiff_pt ω]
  dsimp only
  rw [hbeta_fun, hsig_fun]
  exact hcomp
  /- @proof-region region.root.5552f9e7edae end -/
