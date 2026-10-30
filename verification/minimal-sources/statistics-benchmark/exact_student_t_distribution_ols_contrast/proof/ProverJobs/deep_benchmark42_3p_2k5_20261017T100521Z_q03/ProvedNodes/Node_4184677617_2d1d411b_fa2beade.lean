import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q03.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q03.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q03.ProvedNodes.Node_2828381066_e53af6ac_9d9f1e18
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q03.ProvedNodes.Node_870075716_61295c54_6d06aba6

open MeasureTheory Matrix ProbabilityTheory

open MeasureTheory Matrix ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_4184677617_2d1d411b : ∀ (n p : ℕ) (hnp : p < n)
    (X : Matrix (Fin n) (Fin p) ℝ) (hX : Function.Injective X.mulVec)
    (M : Matrix (Fin p) (Fin p) ℝ) (hM : M = (X.transpose * X)⁻¹)
    (R : Matrix (Fin n) (Fin n) ℝ) (hR : R = 1 - X * M * X.transpose)
    (hRidem : R * R = R) (hRsymm : R.transpose = R)
    (hRorth : ∀ x : Fin n → ℝ, ∀ z : Fin p → ℝ,
      dotProduct (R *ᵥ x) (X *ᵥ z) = 0)
    (hRrange : ∀ x : Fin n → ℝ, ∃ z : Fin p → ℝ, X *ᵥ z = x - R *ᵥ x),
    (Module.finrank ℝ (Submodule.span ℝ
        {x : Fin n → ℝ | ∀ z : Fin p → ℝ, dotProduct x (X *ᵥ z) = 0}) = n - p ∧
      Submodule.span ℝ
          {x : Fin n → ℝ | ∀ z : Fin p → ℝ, dotProduct x (X *ᵥ z) = 0} =
        LinearMap.range R.mulVecLin) ∧
    (∃ v : Fin (n - p) → (Fin n → ℝ),
      (∀ k, dotProduct (v k) (v k) = 1) ∧
      (∀ k l, k ≠ l → dotProduct (v k) (v l) = 0) ∧
      Submodule.span ℝ (Set.range v) =
        Submodule.span ℝ
          {x : Fin n → ℝ | ∀ z : Fin p → ℝ, dotProduct x (X *ᵥ z) = 0} ∧
      (∀ k, R *ᵥ v k = v k) ∧
      (∀ x : Fin n → ℝ,
        R *ᵥ x = ∑ k : Fin (n - p), (dotProduct (v k) x) • v k ∧
        dotProduct (R *ᵥ x) (R *ᵥ x) =
          ∑ k : Fin (n - p), (dotProduct (v k) x) ^ 2)) := by
  /- @proof-region region.target-node.session.5d2aa7c05e2a23bc begin -/
  intro n p hnp X hX M hM R hR hRidem hRsymm hRorth hRrange
  have hfp : Module.finrank ℝ (Fin p → ℝ) = p := by simp
  have hfn : Module.finrank ℝ (Fin n → ℝ) = n := by simp
  have hmulVecLin_apply : ∀ (A : Matrix (Fin p) (Fin p) ℝ) (v : Fin p → ℝ),
      A.mulVecLin v = A *ᵥ v := by
    intro A v
    simp [Matrix.mulVecLin]
  have hTapply : ∀ x : Fin n → ℝ, X.transpose.mulVecLin x = Matrix.vecMul x X := by
    intro x
    simp
  have hRapply : ∀ x : Fin n → ℝ, R.mulVecLin x = R *ᵥ x := by
    intro x
    simp [Matrix.mulVecLin]
  have hvec : ∀ x : Fin n → ℝ, Matrix.vecMul x X = X.transpose *ᵥ x := by
    intro x
    have h := Matrix.vecMul_transpose X.transpose x
    simpa only [Matrix.transpose_transpose] using h
  have hdotsub : ∀ a b c : Fin n → ℝ,
      dotProduct (a - b) c = dotProduct a c - dotProduct b c := by
    intro a b c
    simp only [dotProduct, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  have hker_iff : ∀ x : Fin n → ℝ,
      (x ∈ LinearMap.ker (X.transpose.mulVecLin)) ↔ Matrix.vecMul x X = 0 := by
    intro x
    rw [LinearMap.mem_ker, hTapply x]
  have hmem : ∀ x : Fin n → ℝ,
      (x ∈ LinearMap.ker (X.transpose.mulVecLin)) ↔
        ∀ z : Fin p → ℝ, dotProduct x (X *ᵥ z) = 0 := by
    intro x
    rw [hker_iff x]
    constructor
    · intro hx z
      rw [Matrix.dotProduct_mulVec, hx]
      simp [dotProduct]
    · intro hx
      have h1 : Matrix.vecMul x X ⬝ᵥ Matrix.vecMul x X = 0 := by
        have h0 := hx (Matrix.vecMul x X)
        rwa [Matrix.dotProduct_mulVec] at h0
      exact dotProduct_self_eq_zero.mp h1
  have hSker : ({x : Fin n → ℝ | ∀ z : Fin p → ℝ, dotProduct x (X *ᵥ z) = 0} : Set (Fin n → ℝ))
      = (LinearMap.ker (X.transpose.mulVecLin) : Set (Fin n → ℝ)) := by
    ext x
    exact (hmem x).symm
  have hspan : Submodule.span ℝ {x : Fin n → ℝ | ∀ z : Fin p → ℝ, dotProduct x (X *ᵥ z) = 0}
      = LinearMap.ker (X.transpose.mulVecLin) := by
    rw [hSker]
    exact Submodule.span_eq _
  have hGram : ∀ z : Fin p → ℝ, (X.transpose * X) *ᵥ z = 0 → z = 0 := by
    intro z hz
    have h1 : dotProduct z ((X.transpose * X) *ᵥ z) = 0 := by rw [hz]; simp [dotProduct]
    have h2 : dotProduct z ((X.transpose * X) *ᵥ z) = dotProduct (X *ᵥ z) (X *ᵥ z) := by
      rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    have h3 : dotProduct (X *ᵥ z) (X *ᵥ z) = 0 := by rw [← h2]; exact h1
    have h4 : X *ᵥ z = 0 := dotProduct_self_eq_zero.mp h3
    have h5 : X.mulVec z = X.mulVec 0 := by simpa using h4
    exact hX h5
  have hGker : LinearMap.ker ((X.transpose * X).mulVecLin) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro z hz
    rw [LinearMap.mem_ker, hmulVecLin_apply] at hz
    exact hGram z hz
  have hGdim : Module.finrank ℝ (LinearMap.range ((X.transpose * X).mulVecLin)) = p := by
    have h := LinearMap.finrank_range_add_finrank_ker ((X.transpose * X).mulVecLin)
    rw [hGker, finrank_bot, add_zero, hfp] at h
    exact h
  have hrange_le : LinearMap.range ((X.transpose * X).mulVecLin) ≤ LinearMap.range (X.transpose.mulVecLin) := by
    rintro _ ⟨z, rfl⟩
    refine ⟨X *ᵥ z, ?_⟩
    rw [hTapply, hvec, Matrix.mulVec_mulVec, ← hmulVecLin_apply]
  have hTdim : Module.finrank ℝ (LinearMap.range (X.transpose.mulVecLin)) = p := by
    have hle : Module.finrank ℝ (LinearMap.range ((X.transpose * X).mulVecLin))
        ≤ Module.finrank ℝ (LinearMap.range (X.transpose.mulVecLin)) :=
      Submodule.finrank_mono hrange_le
    have hle2 : Module.finrank ℝ (LinearMap.range (X.transpose.mulVecLin)) ≤ p := by
      have h2 := Submodule.finrank_le (LinearMap.range (X.transpose.mulVecLin))
      simpa [hfp] using h2
    rw [hGdim] at hle
    omega
  have hdimker : Module.finrank ℝ (LinearMap.ker (X.transpose.mulVecLin)) = n - p := by
    have h := LinearMap.finrank_range_add_finrank_ker (X.transpose.mulVecLin)
    rw [hTdim, hfn] at h
    omega
  have hdim : Module.finrank ℝ (Submodule.span ℝ {x : Fin n → ℝ | ∀ z : Fin p → ℝ, dotProduct x (X *ᵥ z) = 0}) = n - p := by
    rw [hspan, hdimker]
  have hker_range : LinearMap.ker (X.transpose.mulVecLin) = LinearMap.range R.mulVecLin := by
    refine le_antisymm ?_ ?_
    · intro y hy
      have hy' : ∀ z : Fin p → ℝ, dotProduct y (X *ᵥ z) = 0 := (hmem y).mp hy
      obtain ⟨z, hz⟩ := hRrange y
      have f2 : dotProduct y (y - R *ᵥ y) = 0 := by rw [← hz]; exact hy' z
      have f3 : dotProduct (R *ᵥ y) (y - R *ᵥ y) = 0 := by rw [← hz]; exact hRorth y z
      have h3 : dotProduct (y - R *ᵥ y) (y - R *ᵥ y) = 0 := by
        rw [hdotsub, f2, f3, sub_zero]
      have h4 : y - R *ᵥ y = 0 := dotProduct_self_eq_zero.mp h3
      refine ⟨y, ?_⟩
      rw [hRapply]
      exact (sub_eq_zero.mp h4).symm
    · intro y hy
      rw [hmem y]
      obtain ⟨w, hw⟩ := hy
      intro z
      have hw' : R *ᵥ w = y := by simpa [hRapply] using hw
      rw [← hw']
      exact hRorth w z
  have hspan_range : Submodule.span ℝ {x : Fin n → ℝ | ∀ z : Fin p → ℝ, dotProduct x (X *ᵥ z) = 0} = LinearMap.range R.mulVecLin := by
    rw [hspan, hker_range]
  refine ⟨⟨hdim, hspan_range⟩, ?_⟩
  have hdimR : Module.finrank ℝ (LinearMap.range R.mulVecLin) = n - p := by
    rw [← hspan_range, hdim]
  exact statopia_math_node_870075716_61295c54 n p hnp X R hRidem hRsymm hRorth hRrange
    hspan_range hdimR
  /- @proof-region region.target-node.session.5d2aa7c05e2a23bc end -/
