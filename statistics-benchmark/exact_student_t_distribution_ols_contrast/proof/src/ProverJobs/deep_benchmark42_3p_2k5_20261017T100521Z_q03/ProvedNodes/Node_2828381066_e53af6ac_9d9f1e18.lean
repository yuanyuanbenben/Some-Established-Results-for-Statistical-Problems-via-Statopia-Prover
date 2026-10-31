import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q03.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q03.Base

open MeasureTheory Matrix ProbabilityTheory

open MeasureTheory Matrix ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_2828381066_e53af6ac : ∀ (n p : ℕ) (X : Matrix (Fin n) (Fin p) ℝ)
    (hX : Function.Injective X.mulVec)
    (a : Fin p → ℝ) (ha : a ≠ 0),
    let M : Matrix (Fin p) (Fin p) ℝ := (X.transpose * X)⁻¹
    let P : Matrix (Fin n) (Fin n) ℝ := X * M * X.transpose
    let R : Matrix (Fin n) (Fin n) ℝ := 1 - P
    let u : Fin n → ℝ := X *ᵥ (M *ᵥ a)
    let q : ℝ := dotProduct a (M *ᵥ a)
    (M * (X.transpose * X) = 1 ∧ (X.transpose * X) * M = 1) ∧
    M.transpose = M ∧
    (∀ v : Fin p → ℝ, v ≠ 0 → 0 < dotProduct v (M *ᵥ v)) ∧
    (P * P = P ∧ P.transpose = P ∧
      (∀ x : Fin n → ℝ, ∃ z : Fin p → ℝ, X *ᵥ z = P *ᵥ x) ∧
      (∀ x : Fin n → ℝ, ∀ z : Fin p → ℝ,
        dotProduct (x - P *ᵥ x) (X *ᵥ z) = 0) ∧
      (∀ x : Fin n → ℝ, (∃ z : Fin p → ℝ, X *ᵥ z = x) → P *ᵥ x = x)) ∧
    (R * R = R ∧ R.transpose = R ∧
      (∀ x : Fin n → ℝ, ∀ z : Fin p → ℝ,
        dotProduct (R *ᵥ x) (X *ᵥ z) = 0) ∧
      (∀ x : Fin n → ℝ, ∃ z : Fin p → ℝ, X *ᵥ z = x - R *ᵥ x)) ∧
    (∃ z : Fin p → ℝ, X *ᵥ z = u) ∧
    R *ᵥ u = 0 ∧
    dotProduct u u = q ∧
    0 < q := by
  /- @proof-region region.target-node.session.54a8a14e4aede69a begin -/
  intro n p X hX a ha
  dsimp only
  set M : Matrix (Fin p) (Fin p) ℝ := (X.transpose * X)⁻¹ with hM
  set P : Matrix (Fin n) (Fin n) ℝ := X * M * X.transpose with hP
  set R : Matrix (Fin n) (Fin n) ℝ := 1 - P with hR
  set u : Fin n → ℝ := X *ᵥ (M *ᵥ a) with hu
  set q : ℝ := dotProduct a (M *ᵥ a) with hq
  have h_comm : ∀ (k : ℕ) (v w : Fin k → ℝ), dotProduct v w = dotProduct w v := by
    intro k v w
    simp only [dotProduct]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have h_adj : ∀ (m k : ℕ) (A : Matrix (Fin m) (Fin k) ℝ) (v : Fin k → ℝ) (w : Fin m → ℝ),
      dotProduct (A *ᵥ v) w = dotProduct v (A.transpose *ᵥ w) := by
    intro m k A v w
    calc dotProduct (A *ᵥ v) w
        = dotProduct w (A *ᵥ v) := h_comm m (A *ᵥ v) w
      _ = dotProduct (Matrix.vecMul w A) v := Matrix.dotProduct_mulVec w A v
      _ = dotProduct v (Matrix.vecMul w A) := h_comm k (Matrix.vecMul w A) v
      _ = dotProduct v (A.transpose *ᵥ w) := by
            congr 1
            exact Matrix.vecMul_transpose A.transpose w
  have h_self_pos : ∀ (k : ℕ) (w : Fin k → ℝ), w ≠ 0 → 0 < dotProduct w w := by
    intro k w hw
    obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
      by_contra h
      apply hw
      funext j
      by_contra hj
      exact h ⟨j, hj⟩
    simp only [dotProduct]
    have hnn : ∀ j, 0 ≤ w j * w j := fun j => mul_self_nonneg (w j)
    have hpos : 0 < w i * w i := mul_self_pos.mpr hi
    have hle : w i * w i ≤ ∑ j, w j * w j :=
      Finset.single_le_sum (f := fun j => w j * w j) (fun j _ => hnn j) (Finset.mem_univ i)
    linarith
  have hGunit : IsUnit (X.transpose * X).det := by
    have hpd : (X.transpose * X).PosDef := by
      rw [Matrix.posDef_iff_dotProduct_mulVec]
      refine ⟨?_, ?_⟩
      · show Matrix.conjTranspose (X.transpose * X) = X.transpose * X
        ext i j
        simp [Matrix.conjTranspose_apply, Matrix.mul_apply, Matrix.transpose_apply, mul_comm]
      · intro x hx
        rw [star_trivial]
        rw [show (X.transpose * X) *ᵥ x = X.transpose *ᵥ (X *ᵥ x) from
          (Matrix.mulVec_mulVec x X.transpose X).symm]
        rw [← h_adj n p X x (X *ᵥ x)]
        have hxne : X *ᵥ x ≠ 0 := by
          intro h
          exact hx (hX (by rw [h]; simp))
        exact h_self_pos n (X *ᵥ x) hxne
    exact isUnit_iff_ne_zero.mpr (ne_of_gt (Matrix.PosDef.det_pos hpd))
  have h_inv : M * (X.transpose * X) = 1 ∧ (X.transpose * X) * M = 1 := by
    constructor
    · rw [hM]; exact Matrix.nonsing_inv_mul (X.transpose * X) hGunit
    · rw [hM]; exact Matrix.mul_nonsing_inv (X.transpose * X) hGunit
  have h_symm : M.transpose = M := by
    rw [hM, Matrix.transpose_nonsing_inv]
    congr 1
    simp [Matrix.transpose_mul]
  have h_pd : ∀ v : Fin p → ℝ, v ≠ 0 → 0 < dotProduct v (M *ᵥ v) := by
    intro v hv
    have hvEq : v = (X.transpose * X) *ᵥ (M *ᵥ v) := by
      rw [Matrix.mulVec_mulVec, h_inv.2]; simp
    have hwne : M *ᵥ v ≠ 0 := by
      intro h; apply hv; rw [hvEq, h]; simp
    have key : dotProduct v (M *ᵥ v) = dotProduct (X *ᵥ (M *ᵥ v)) (X *ᵥ (M *ᵥ v)) := by
      nth_rewrite 1 [hvEq]
      rw [show (X.transpose * X) *ᵥ (M *ᵥ v) = X.transpose *ᵥ (X *ᵥ (M *ᵥ v)) from
        (Matrix.mulVec_mulVec (M *ᵥ v) X.transpose X).symm]
      rw [h_adj p n X.transpose (X *ᵥ (M *ᵥ v)) (M *ᵥ v)]
      simp
    rw [key]
    exact h_self_pos n (X *ᵥ (M *ᵥ v)) (fun h => hwne (hX (by simpa using h)))
  have h_sub : ∀ (k : ℕ) (a b c : Fin k → ℝ),
      dotProduct (a - b) c = dotProduct a c - dotProduct b c := by
    intro k a b c
    simp [dotProduct, Finset.sum_sub_distrib, sub_mul]
  have hPX : P * X = X := by
    rw [hP]
    rw [show (X * M * X.transpose) * X = X * (M * (X.transpose * X)) from by
      simp only [Matrix.mul_assoc]]
    rw [h_inv.1]
    simp
  have hPfix : ∀ x : Fin n → ℝ, (∃ z : Fin p → ℝ, X *ᵥ z = x) → P *ᵥ x = x := by
    intro x hx
    obtain ⟨z, hz⟩ := hx
    rw [← hz, Matrix.mulVec_mulVec, hPX]
  have hPcol : ∀ x : Fin n → ℝ, ∃ z : Fin p → ℝ, X *ᵥ z = P *ᵥ x := by
    intro x
    exact ⟨M *ᵥ (X.transpose *ᵥ x),
      by rw [hP, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]⟩
  have hPt : P.transpose = P := by
    rw [hP]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, h_symm]
    simp only [Matrix.mul_assoc]
  have hPP : P * P = P := by
    rw [hP]
    rw [show (X * M * X.transpose) * (X * M * X.transpose)
        = X * (M * (X.transpose * X)) * M * X.transpose from by
      simp only [Matrix.mul_assoc]]
    rw [h_inv.1]
    simp
  have hPorth : ∀ x : Fin n → ℝ, ∀ z : Fin p → ℝ,
      dotProduct (x - P *ᵥ x) (X *ᵥ z) = 0 := by
    intro x z
    have step : dotProduct (P *ᵥ x) (X *ᵥ z) = dotProduct x (X *ᵥ z) := by
      rw [h_adj n n P x (X *ᵥ z), hPt, hPfix (X *ᵥ z) ⟨z, rfl⟩]
    rw [h_sub n x (P *ᵥ x) (X *ᵥ z), step, sub_self]
  have h_P : P * P = P ∧ P.transpose = P ∧
      (∀ x : Fin n → ℝ, ∃ z : Fin p → ℝ, X *ᵥ z = P *ᵥ x) ∧
      (∀ x : Fin n → ℝ, ∀ z : Fin p → ℝ, dotProduct (x - P *ᵥ x) (X *ᵥ z) = 0) ∧
      (∀ x : Fin n → ℝ, (∃ z : Fin p → ℝ, X *ᵥ z = x) → P *ᵥ x = x) :=
    ⟨hPP, hPt, hPcol, hPorth, hPfix⟩
  have hRR : R * R = R := by
    rw [hR]
    rw [show (1 - P) * (1 - P) = 1 - P - P + P * P from by noncomm_ring]
    rw [hPP]
    noncomm_ring
  have hRt : R.transpose = R := by
    rw [hR, Matrix.transpose_sub, Matrix.transpose_one, hPt]
  have hRx : ∀ x : Fin n → ℝ, R *ᵥ x = x - P *ᵥ x := by
    intro x
    rw [hR, Matrix.sub_mulVec, Matrix.one_mulVec]
  have hRorth : ∀ x : Fin n → ℝ, ∀ z : Fin p → ℝ,
      dotProduct (R *ᵥ x) (X *ᵥ z) = 0 := by
    intro x z
    rw [hRx x]
    exact hPorth x z
  have hRcol : ∀ x : Fin n → ℝ, ∃ z : Fin p → ℝ, X *ᵥ z = x - R *ᵥ x := by
    intro x
    obtain ⟨z, hz⟩ := hPcol x
    refine ⟨z, ?_⟩
    rw [hRx x, hz]
    abel
  have h_R : R * R = R ∧ R.transpose = R ∧
      (∀ x : Fin n → ℝ, ∀ z : Fin p → ℝ, dotProduct (R *ᵥ x) (X *ᵥ z) = 0) ∧
      (∀ x : Fin n → ℝ, ∃ z : Fin p → ℝ, X *ᵥ z = x - R *ᵥ x) :=
    ⟨hRR, hRt, hRorth, hRcol⟩
  have h_u : ∃ z : Fin p → ℝ, X *ᵥ z = u := ⟨M *ᵥ a, hu.symm⟩
  have h_Ru : R *ᵥ u = 0 := by
    obtain ⟨z, hz⟩ := h_u
    rw [hRx u, hPfix u ⟨z, hz⟩, sub_self]
  have h_uu : dotProduct u u = q := by
    rw [hu, hq]
    have e1 : X.transpose *ᵥ (X *ᵥ (M *ᵥ a)) = (X.transpose * X) *ᵥ (M *ᵥ a) :=
      Matrix.mulVec_mulVec (M *ᵥ a) X.transpose X
    have e2 : (X.transpose * X) *ᵥ (M *ᵥ a) = a := by
      rw [Matrix.mulVec_mulVec, h_inv.2]; simp
    calc dotProduct (X *ᵥ (M *ᵥ a)) (X *ᵥ (M *ᵥ a))
        = dotProduct (M *ᵥ a) (X.transpose *ᵥ (X *ᵥ (M *ᵥ a))) := h_adj n p X (M *ᵥ a) (X *ᵥ (M *ᵥ a))
      _ = dotProduct (M *ᵥ a) ((X.transpose * X) *ᵥ (M *ᵥ a)) := by rw [e1]
      _ = dotProduct (M *ᵥ a) a := by rw [e2]
      _ = dotProduct a (M *ᵥ a) := h_comm p (M *ᵥ a) a
  have h_q : 0 < q := by rw [hq]; exact h_pd a ha
  exact ⟨h_inv, h_symm, h_pd, h_P, h_R, h_u, h_Ru, h_uu, h_q⟩
  /- @proof-region region.target-node.session.54a8a14e4aede69a end -/
