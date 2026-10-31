import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q03.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q03.Base

open MeasureTheory Matrix ProbabilityTheory

open MeasureTheory Matrix ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_870075716_61295c54 : ∀ (n p : ℕ) (hnp : p < n)
    (X : Matrix (Fin n) (Fin p) ℝ) (R : Matrix (Fin n) (Fin n) ℝ)
    (hRidem : R * R = R) (hRsymm : R.transpose = R)
    (hRorth : ∀ x : Fin n → ℝ, ∀ z : Fin p → ℝ, dotProduct (R *ᵥ x) (X *ᵥ z) = 0)
    (hRrange : ∀ x : Fin n → ℝ, ∃ z : Fin p → ℝ, X *ᵥ z = x - R *ᵥ x)
    (hspan : Submodule.span ℝ {x : Fin n → ℝ | ∀ z : Fin p → ℝ, dotProduct x (X *ᵥ z) = 0}
      = LinearMap.range R.mulVecLin)
    (hdim : Module.finrank ℝ (LinearMap.range R.mulVecLin) = n - p),
    ∃ v : Fin (n - p) → (Fin n → ℝ),
      (∀ k : Fin (n - p), dotProduct (v k) (v k) = 1) ∧
      (∀ k l : Fin (n - p), k ≠ l → dotProduct (v k) (v l) = 0) ∧
      (Submodule.span ℝ (Set.range v)
        = Submodule.span ℝ {x : Fin n → ℝ | ∀ z : Fin p → ℝ, dotProduct x (X *ᵥ z) = 0}) ∧
      (∀ k : Fin (n - p), R *ᵥ v k = v k) ∧
      (∀ x : Fin n → ℝ,
        R *ᵥ x = ∑ k : Fin (n - p), (dotProduct (v k) x) • v k ∧
        dotProduct (R *ᵥ x) (R *ᵥ x)
          = ∑ k : Fin (n - p), (dotProduct (v k) x) ^ 2) := by
  /- @proof-region region.target-node.session.956cf35d16e409fb begin -/
  intro n p hnp X R hRidem hRsymm hRorth hRrange hspan hdim
  classical
  set Wf : Submodule ℝ (Fin n → ℝ) :=
    Submodule.span ℝ {x : Fin n → ℝ | ∀ z : Fin p → ℝ, dotProduct x (X *ᵥ z) = 0} with hWfdef
  have hWf : Wf = LinearMap.range R.mulVecLin := hspan
  let Φ : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] (Fin n → ℝ) := WithLp.linearEquiv 2 ℝ (Fin n → ℝ)
  let W : Submodule ℝ (EuclideanSpace ℝ (Fin n)) := Wf.comap Φ.toLinearMap
  have hΦ : ∀ u : EuclideanSpace ℝ (Fin n), Φ u = u.ofLp := fun u => rfl
  have eW : ↥W ≃ₗ[ℝ] ↥Wf :=
    { toFun := fun u => ⟨Φ u.1, u.2⟩
      invFun := fun y => ⟨Φ.symm y.1, by
        show Φ (Φ.symm y.1) ∈ Wf
        rw [LinearEquiv.apply_symm_apply]
        exact y.2⟩
      left_inv := by intro u; ext; simp
      right_inv := by intro y; ext; simp
      map_add' := by intro u u'; ext; simp
      map_smul' := by intro c u; ext; simp }
  have hdimW : Module.finrank ℝ W = n - p := by
    rw [LinearEquiv.finrank_eq eW, hWf, hdim]
  let b : OrthonormalBasis (Fin (Module.finrank ℝ W)) ℝ ↥W := stdOrthonormalBasis ℝ ↥W
  let b' : OrthonormalBasis (Fin (n - p)) ℝ ↥W := b.reindex (finCongr hdimW)
  let v : Fin (n - p) → (Fin n → ℝ) := fun k => Φ ((b' k : ↥W) : EuclideanSpace ℝ (Fin n))
  have hv_def : ∀ k : Fin (n - p), v k = Φ ((b' k : ↥W) : EuclideanSpace ℝ (Fin n)) := fun k => rfl
  have inner_bridge : ∀ u u' : EuclideanSpace ℝ (Fin n),
      inner ℝ u u' = dotProduct (Φ u) (Φ u') := by
    intro u u'
    simp [PiLp.inner_apply, dotProduct, hΦ, mul_comm]
  have hb_orth : ∀ i j : Fin (n - p),
      inner ℝ ((b' i : ↥W) : EuclideanSpace ℝ (Fin n)) ((b' j : ↥W) : EuclideanSpace ℝ (Fin n))
        = if i = j then 1 else 0 := by
    intro i j
    have h := (orthonormal_iff_ite.mp b'.orthonormal) i j
    simpa using h
  have hv_mem : ∀ k : Fin (n - p), v k ∈ Wf := by
    intro k
    exact (b' k).2
  have hWf_res : ∀ x ∈ Wf, ∀ z : Fin p → ℝ, dotProduct x (X *ᵥ z) = 0 := by
    intro x hx z
    rw [hWf] at hx
    obtain ⟨w, hw⟩ := LinearMap.mem_range.1 hx
    have hw' : R *ᵥ w = x := hw
    rw [← hw']
    exact hRorth w z
  have hkey : ∀ (k : Fin (n - p)) (y : Fin n → ℝ),
      dotProduct (v k) (R *ᵥ y) = dotProduct (v k) y := by
    intro k y
    obtain ⟨z, hz⟩ := hRrange y
    have hz0 : dotProduct (v k) (X *ᵥ z) = 0 := hWf_res (v k) (hv_mem k) z
    have hy : R *ᵥ y + X *ᵥ z = y := by rw [hz]; abel
    have hadd : dotProduct (v k) (R *ᵥ y + X *ᵥ z)
        = dotProduct (v k) (R *ᵥ y) + dotProduct (v k) (X *ᵥ z) := by
      simp [dotProduct, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    calc dotProduct (v k) (R *ᵥ y)
        = dotProduct (v k) (R *ᵥ y) + dotProduct (v k) (X *ᵥ z) := by rw [hz0, add_zero]
      _ = dotProduct (v k) (R *ᵥ y + X *ᵥ z) := hadd.symm
      _ = dotProduct (v k) y := by rw [hy]
  have hboth : ∀ x : Fin n → ℝ,
      R *ᵥ x = ∑ k : Fin (n - p), (dotProduct (v k) x) • v k ∧
      dotProduct (R *ᵥ x) (R *ᵥ x) = ∑ k : Fin (n - p), (dotProduct (v k) x) ^ 2 := by
    intro x
    set y := R *ᵥ x with hydef
    have hyWf : y ∈ Wf := by
      rw [hWf]
      exact LinearMap.mem_range.2 ⟨x, rfl⟩
    let u : ↥W := ⟨Φ.symm y, by
      show Φ (Φ.symm y) ∈ Wf
      rw [LinearEquiv.apply_symm_apply]
      exact hyWf⟩
    have hΦu : Φ (u : EuclideanSpace ℝ (Fin n)) = y := by
      show Φ (Φ.symm y) = y
      rw [LinearEquiv.apply_symm_apply]
    have hcoef : ∀ k : Fin (n - p), inner ℝ (b' k) u = dotProduct (v k) x := by
      intro k
      have ha : inner ℝ ((b' k : ↥W) : EuclideanSpace ℝ (Fin n)) (u : EuclideanSpace ℝ (Fin n))
          = dotProduct (v k) x := by
        rw [hv_def k, inner_bridge, hΦu, hydef]
        exact hkey k x
      simpa using ha
    constructor
    · have hveq : ∀ k : Fin (n - p), (Φ.toLinearMap.comp W.subtype) (b' k) = v k := fun k => rfl
      have hLu : (Φ.toLinearMap.comp W.subtype) u = R *ᵥ x := by
        change Φ (u : EuclideanSpace ℝ (Fin n)) = R *ᵥ x
        rw [hΦu, hydef]
      have hmap := congrArg (Φ.toLinearMap.comp W.subtype) (b'.sum_repr' u)
      simp only [map_sum, map_smul, hveq, hcoef, hLu] at hmap
      exact hmap.symm
    · have hsq := Orthonormal.inner_sum b'.orthonormal
        (fun k : Fin (n - p) => inner ℝ (b' k) u) (fun k : Fin (n - p) => inner ℝ (b' k) u)
        Finset.univ
      have hsqrt : inner ℝ u u = dotProduct y y := by
        have ha : inner ℝ ((u : ↥W) : EuclideanSpace ℝ (Fin n)) ((u : ↥W) : EuclideanSpace ℝ (Fin n))
            = dotProduct y y := by
          rw [inner_bridge, hΦu]
        simpa using ha
      simp only [b'.sum_repr' u, hsqrt] at hsq
      rw [hsq]
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [hcoef k]
      simp [sq]
  refine ⟨v, ?_, ?_, ?_, ?_, ?_⟩
  · show ∀ k : Fin (n - p), dotProduct (v k) (v k) = 1
    intro k
    rw [hv_def k, ← inner_bridge]
    have h := hb_orth k k
    rw [if_pos rfl] at h
    exact h
  · show ∀ k l : Fin (n - p), k ≠ l → dotProduct (v k) (v l) = 0
    intro k l hkl
    rw [hv_def k, hv_def l, ← inner_bridge]
    have h := hb_orth k l
    rw [if_neg hkl] at h
    exact h
  · show Submodule.span ℝ (Set.range v) = Wf
    refine le_antisymm ?_ ?_
    · rw [Submodule.span_le]
      rintro w ⟨k, rfl⟩
      exact hv_mem k
    · intro w hw
      rw [hWf] at hw
      obtain ⟨x, hx⟩ := LinearMap.mem_range.1 hw
      have hxy : w = R *ᵥ x := hx.symm
      rw [hxy, (hboth x).1]
      exact Submodule.sum_mem (Submodule.span ℝ (Set.range v))
        (fun k _ => Submodule.smul_mem (Submodule.span ℝ (Set.range v)) (dotProduct (v k) x)
          (Submodule.subset_span ⟨k, rfl⟩))
  · show ∀ k : Fin (n - p), R *ᵥ v k = v k
    intro k
    have hmem : v k ∈ LinearMap.range R.mulVecLin := by
      rw [← hWf]
      exact hv_mem k
    obtain ⟨w, hw⟩ := LinearMap.mem_range.1 hmem
    have hw' : R *ᵥ w = v k := hw
    rw [← hw', Matrix.mulVec_mulVec, hRidem]
  · exact hboth
  /- @proof-region region.target-node.session.956cf35d16e409fb end -/
