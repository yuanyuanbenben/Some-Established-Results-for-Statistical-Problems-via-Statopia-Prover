import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q26.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q26.ProvedNodes
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q26.Base

open MeasureTheory Matrix

theorem ridge_regression_mean_squared_error
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (X : Matrix (Fin n) (Fin d) ℝ)
    (betaStar : Fin d → ℝ)
    (epsilon : Ω → Fin n → ℝ)
    (hε_L2 : MemLp epsilon 2 P)
    (sigmaSq : ℝ) (hsigma : 0 ≤ sigmaSq)
    (hmean : ∫ ω, epsilon ω ∂P = 0)
    (hcov : ∀ i j, ∫ ω, epsilon ω i * epsilon ω j ∂P =
      if i = j then sigmaSq else 0)
    (lambda : ℝ) (hlambda : 0 < lambda) :
    let A : Matrix (Fin d) (Fin d) ℝ :=
      X.transpose * X + lambda • 1
    let y : Ω → Fin n → ℝ := fun ω ↦ X *ᵥ betaStar + epsilon ω
    let betaHat : Ω → Fin d → ℝ := fun ω ↦
      A⁻¹ *ᵥ (X.transpose *ᵥ y ω)
    ∫ ω, dotProduct (betaHat ω - betaStar)
        (betaHat ω - betaStar) ∂P =
      lambda ^ 2 *
          dotProduct (A⁻¹ *ᵥ betaStar) (A⁻¹ *ᵥ betaStar) +
        sigmaSq * (A⁻¹ * X.transpose * X * A⁻¹).trace
:= by
  /- @proof-region region.root.7ff8ab84a874 begin -/
  classical
  dsimp only
  let A : Matrix (Fin d) (Fin d) ℝ := X.transpose * X + lambda • 1
  let L : Matrix (Fin d) (Fin n) ℝ := A⁻¹ * X.transpose
  let c : Fin d → ℝ := A⁻¹ *ᵥ betaStar
  let y : Ω → Fin n → ℝ := fun ω => X *ᵥ betaStar + epsilon ω
  let betaHat : Ω → Fin d → ℝ := fun ω => A⁻¹ *ᵥ (X.transpose *ᵥ y ω)
  change ∫ ω, dotProduct (betaHat ω - betaStar) (betaHat ω - betaStar) ∂P =
    lambda ^ 2 * dotProduct c c + sigmaSq * (A⁻¹ * X.transpose * X * A⁻¹).trace
  have hPsd : (X.transpose * X).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self X
  have hPD : (lambda • (1 : Matrix (Fin d) (Fin d) ℝ)).PosDef :=
    Matrix.PosDef.smul Matrix.PosDef.one hlambda
  have hApos : A.PosDef := by
    have h := hPD.add_posSemidef hPsd
    rw [add_comm] at h
    simpa [A] using h
  have hdet : IsUnit A.det := isUnit_iff_ne_zero.mpr (ne_of_gt hApos.det_pos)
  haveI : Invertible A := Matrix.invertibleOfIsUnitDet A hdet
  have hinv_left : A⁻¹ * A = 1 := Matrix.inv_mul_of_invertible A
  have hinv_right : A * A⁻¹ = 1 := Matrix.mul_inv_of_invertible A
  have hAsymm : A.transpose = A := by
    simp [A]
  have hAinv_symm : (A⁻¹).transpose = A⁻¹ := by
    have h1 : (A⁻¹).transpose * A = 1 := by
      have h2 := congrArg Matrix.transpose hinv_right
      rw [Matrix.transpose_mul, Matrix.transpose_one, hAsymm] at h2
      exact h2
    calc (A⁻¹).transpose = (A⁻¹).transpose * 1 := (Matrix.mul_one _).symm
      _ = (A⁻¹).transpose * (A * A⁻¹) := by rw [hinv_right]
      _ = ((A⁻¹).transpose * A) * A⁻¹ := by rw [Matrix.mul_assoc]
      _ = 1 * A⁻¹ := by rw [h1]
      _ = A⁻¹ := Matrix.one_mul _
  have haffine := statopia_math_node_1402057802_aa0b1c9d n d X betaStar epsilon lambda hinv_left hinv_right
  obtain ⟨hvec, hcoord⟩ := haffine
  have heps_int : Integrable epsilon P :=
    MeasureTheory.MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2) hε_L2
  have hcoord_int : ∀ i : Fin n, Integrable (fun ω => epsilon ω i) P := fun i =>
    MeasureTheory.MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2)
      (MeasureTheory.memLp_pi_iff.mp hε_L2 i)
  have hint : ∀ i j : Fin n, Integrable (fun ω => epsilon ω i * epsilon ω j) P := by
    intro i j
    have hi := MeasureTheory.memLp_pi_iff.mp hε_L2 i
    have hj := MeasureTheory.memLp_pi_iff.mp hε_L2 j
    simpa [Pi.mul_apply] using hi.integrable_mul hj
  let w : Ω → Fin d → ℝ := fun ω => L *ᵥ epsilon ω
  have hdot : ∀ (u v : Fin d → ℝ) (t : ℝ),
      dotProduct (u - t • v) (u - t • v)
        = dotProduct u u - 2 * t * dotProduct u v + t ^ 2 * dotProduct v v := by
    intro u v t
    simp only [dotProduct, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have h1 : 2 * t * ∑ x : Fin d, u x * v x = ∑ x : Fin d, 2 * t * (u x * v x) := by
      rw [Finset.mul_sum]
    have h2 : t ^ 2 * ∑ x : Fin d, v x * v x = ∑ x : Fin d, t ^ 2 * (v x * v x) := by
      rw [Finset.mul_sum]
    rw [h1, h2, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hpoint : ∀ ω : Ω, dotProduct (betaHat ω - betaStar) (betaHat ω - betaStar)
      = dotProduct (w ω) (w ω) - 2 * lambda * dotProduct (w ω) c
        + lambda ^ 2 * dotProduct c c := by
    intro ω
    rw [hvec ω]
    exact hdot (w ω) c lambda
  have hw_int : ∀ k : Fin d, Integrable (fun ω => ∑ i : Fin n, L k i * epsilon ω i) P := by
    intro k
    exact MeasureTheory.integrable_finset_sum Finset.univ
      (fun i _ => (hcoord_int i).const_mul (L k i))
  have hw_sq_int : ∀ k : Fin d,
      Integrable (fun ω => (∑ i : Fin n, L k i * epsilon ω i) ^ 2) P := by
    intro k
    have hexp : (fun ω => (∑ i : Fin n, L k i * epsilon ω i) ^ 2)
        = fun ω => ∑ i : Fin n, ∑ j : Fin n,
            (L k i * L k j) * (epsilon ω i * epsilon ω j) := by
      funext ω
      rw [pow_two, Finset.sum_mul_sum Finset.univ Finset.univ]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hexp]
    exact MeasureTheory.integrable_finset_sum Finset.univ
      (fun i _ => MeasureTheory.integrable_finset_sum Finset.univ
        (fun j _ => (hint i j).const_mul (L k i * L k j)))
  have hWint : Integrable (fun ω => dotProduct (w ω) (w ω)) P := by
    have hfun : (fun ω => dotProduct (w ω) (w ω))
        = fun ω => ∑ k : Fin d, (∑ i : Fin n, L k i * epsilon ω i) ^ 2 := by
      funext ω
      simp only [dotProduct, pow_two]
      apply Finset.sum_congr rfl
      intro k _
      rfl
    rw [hfun]
    exact MeasureTheory.integrable_finset_sum Finset.univ (fun k _ => hw_sq_int k)
  have hcross_int : Integrable (fun ω => dotProduct (w ω) c) P := by
    have hfun : (fun ω => dotProduct (w ω) c)
        = fun ω => ∑ k : Fin d, c k * (∑ i : Fin n, L k i * epsilon ω i) := by
      funext ω
      simp only [dotProduct]
      apply Finset.sum_congr rfl
      intro k _
      change (∑ i : Fin n, L k i * epsilon ω i) * c k
        = c k * ∑ i : Fin n, L k i * epsilon ω i
      ring
    rw [hfun]
    exact MeasureTheory.integrable_finset_sum Finset.univ
      (fun k _ => (hw_int k).const_mul (c k))
  have hWval : ∫ ω, dotProduct (w ω) (w ω) ∂P
      = sigmaSq * ∑ k : Fin d, ∑ i : Fin n, (L k i) ^ 2 := by
    have hfun : (fun ω => dotProduct (w ω) (w ω))
        = fun ω => ∑ k : Fin d, (∑ i : Fin n, L k i * epsilon ω i) ^ 2 := by
      funext ω
      simp only [dotProduct, pow_two]
      apply Finset.sum_congr rfl
      intro k _
      rfl
    rw [hfun]
    rw [MeasureTheory.integral_finset_sum Finset.univ (fun k _ => hw_sq_int k)]
    have hk : ∀ k : Fin d, ∫ ω, (∑ i : Fin n, L k i * epsilon ω i) ^ 2 ∂P
        = sigmaSq * ∑ i : Fin n, (L k i) ^ 2 := fun k =>
      statopia_math_node_2978562146_47ebeab7 P n d epsilon hε_L2 L sigmaSq hcov hint k
    rw [show (∑ k : Fin d, ∫ ω, (∑ i : Fin n, L k i * epsilon ω i) ^ 2 ∂P)
          = ∑ k : Fin d, sigmaSq * ∑ i : Fin n, (L k i) ^ 2 from
        Finset.sum_congr rfl (fun k _ => hk k)]
    rw [Finset.mul_sum]
  have hcross_val : ∫ ω, dotProduct (w ω) c ∂P = 0 := by
    have hfun : (fun ω => dotProduct (w ω) c)
        = fun ω => ∑ k : Fin d, c k * (∑ i : Fin n, L k i * epsilon ω i) := by
      funext ω
      simp only [dotProduct]
      apply Finset.sum_congr rfl
      intro k _
      change (∑ i : Fin n, L k i * epsilon ω i) * c k
        = c k * ∑ i : Fin n, L k i * epsilon ω i
      ring
    rw [hfun]
    exact statopia_math_node_4216094757_85bc2c28 P n d X betaStar epsilon lambda
      heps_int hcoord_int hmean
  have hconst_val : ∫ ω, dotProduct c c ∂P = dotProduct c c := by
    rw [MeasureTheory.integral_const]
    simp
  have hB_int : Integrable (fun ω => 2 * lambda * dotProduct (w ω) c) P :=
    hcross_int.const_mul (2 * lambda)
  have hconst_int : Integrable (fun _ : Ω => lambda ^ 2 * dotProduct c c) P :=
    MeasureTheory.integrable_const _
  have htrace : (A⁻¹ * X.transpose * X * A⁻¹).trace
      = ∑ k : Fin d, ∑ i : Fin n, (L k i) ^ 2 := by
    have h := statopia_math_node_1521777629_f3d38e95 n d X A hAsymm hAinv_symm
    simpa [L] using h
  calc
    ∫ ω, dotProduct (betaHat ω - betaStar) (betaHat ω - betaStar) ∂P
        = ∫ ω, (dotProduct (w ω) (w ω) - 2 * lambda * dotProduct (w ω) c
            + lambda ^ 2 * dotProduct c c) ∂P := by
          rw [show (fun ω => dotProduct (betaHat ω - betaStar) (betaHat ω - betaStar))
              = (fun ω => dotProduct (w ω) (w ω) - 2 * lambda * dotProduct (w ω) c
                  + lambda ^ 2 * dotProduct c c) from funext hpoint]
    _ = ∫ ω, dotProduct (w ω) (w ω) ∂P
          - ∫ ω, 2 * lambda * dotProduct (w ω) c ∂P
          + ∫ ω, lambda ^ 2 * dotProduct c c ∂P := by
          have hadd : ∫ ω, ((dotProduct (w ω) (w ω) - 2 * lambda * dotProduct (w ω) c)
                + lambda ^ 2 * dotProduct c c) ∂P
              = ∫ ω, (dotProduct (w ω) (w ω) - 2 * lambda * dotProduct (w ω) c) ∂P
                + ∫ ω, lambda ^ 2 * dotProduct c c ∂P :=
            MeasureTheory.integral_add (hWint.sub hB_int) hconst_int
          have hsub : ∫ ω, (dotProduct (w ω) (w ω) - 2 * lambda * dotProduct (w ω) c) ∂P
              = ∫ ω, dotProduct (w ω) (w ω) ∂P
                - ∫ ω, 2 * lambda * dotProduct (w ω) c ∂P :=
            MeasureTheory.integral_sub hWint hB_int
          rw [hadd, hsub]
    _ = ∫ ω, dotProduct (w ω) (w ω) ∂P
          - 2 * lambda * ∫ ω, dotProduct (w ω) c ∂P
          + lambda ^ 2 * ∫ ω, dotProduct c c ∂P := by
          rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    _ = sigmaSq * ∑ k : Fin d, ∑ i : Fin n, (L k i) ^ 2
          - 2 * lambda * 0 + lambda ^ 2 * dotProduct c c := by
          rw [hWval, hcross_val, hconst_val]
    _ = lambda ^ 2 * dotProduct c c
          + sigmaSq * (A⁻¹ * X.transpose * X * A⁻¹).trace := by
          rw [← htrace]
          ring
  /- @proof-region region.root.7ff8ab84a874 end -/
