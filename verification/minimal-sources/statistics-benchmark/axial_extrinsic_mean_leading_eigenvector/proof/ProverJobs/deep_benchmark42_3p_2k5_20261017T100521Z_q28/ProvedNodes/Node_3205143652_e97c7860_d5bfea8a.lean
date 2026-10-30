import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q28.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q28.Base

open Matrix

open Matrix

set_option autoImplicit false in
theorem statopia_math_node_3205143652_e97c7860 : ∀ (d : ℕ) (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ j k : Fin d, A j k = A k j)
    (lambda : ℝ)
    (hineq : ∀ y : Fin d → ℝ,
      dotProduct y (A *ᵥ y) ≤ lambda * dotProduct y y)
    (u : Fin d → ℝ)
    (hu : dotProduct u u = 1)
    (huq : dotProduct u (A *ᵥ u) = lambda),
    A *ᵥ u = lambda • u := by
  /- @proof-region region.target-node.session.1c35e96878cd15d4 begin -/
  intro d A hA lambda hineq u hu huq
  set r : Fin d → ℝ := A *ᵥ u - lambda • u with hr
  have hAu : A *ᵥ u = r + lambda • u := by
    rw [hr]
    exact (sub_add_cancel _ _).symm
  have hsym : ∀ x y : Fin d → ℝ, dotProduct x (A *ᵥ y) = dotProduct y (A *ᵥ x) := by
    intro x y
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hA j i]
    ring
  have hcross : dotProduct u (A *ᵥ r) = dotProduct r r + lambda * dotProduct u r := by
    rw [hsym u r, hAu, dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_comm r u]
  have hexp1 : ∀ t : ℝ, dotProduct (u + t • r) (u + t • r)
      = 1 + 2 * t * dotProduct u r + t^2 * dotProduct r r := by
    intro t
    have hru : dotProduct r u = dotProduct u r := dotProduct_comm r u
    rw [dotProduct_add (u + t • r) u (t • r), dotProduct_smul t (u + t • r) r, smul_eq_mul,
      dotProduct_comm (u + t • r) u, dotProduct_comm (u + t • r) r]
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
    rw [hru, hu]
    ring
  have hexp2 : ∀ t : ℝ, dotProduct (u + t • r) (A *ᵥ (u + t • r))
      = lambda + 2 * t * dotProduct r r + 2 * lambda * t * dotProduct u r
        + t^2 * dotProduct r (A *ᵥ r) := by
    intro t
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul]
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
    simp only [hsym (u + t • r) u, hsym (u + t • r) r]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul]
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
    simp only [hsym r u, hcross, huq]
    ring
  have hkey : ∀ t : ℝ, 2 * t * dotProduct r r
      ≤ t^2 * (lambda * dotProduct r r - dotProduct r (A *ᵥ r)) := by
    intro t
    have h := hineq (u + t • r)
    rw [hexp1 t, hexp2 t] at h
    nlinarith [h]
  have hzero : r = 0 := by
    by_contra hne
    have hnn : 0 ≤ dotProduct r r := by
      have hrepr : dotProduct r r = ∑ i, r i * r i := rfl
      rw [hrepr]
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg (r i)
    have hnz : dotProduct r r ≠ 0 := by
      intro h0
      exact hne (dotProduct_self_eq_zero.mp h0)
    have hpos : 0 < dotProduct r r := lt_of_le_of_ne hnn (Ne.symm hnz)
    by_cases hC : lambda * dotProduct r r - dotProduct r (A *ᵥ r) ≤ 0
    · have h1 := hkey 1
      nlinarith [hpos, h1, hC]
    · have hCpos : 0 < lambda * dotProduct r r - dotProduct r (A *ᵥ r) := not_le.mp hC
      have hCne : lambda * dotProduct r r - dotProduct r (A *ᵥ r) ≠ 0 := ne_of_gt hCpos
      have htC : (dotProduct r r / (lambda * dotProduct r r - dotProduct r (A *ᵥ r)))
            * (lambda * dotProduct r r - dotProduct r (A *ᵥ r)) = dotProduct r r := by
        rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hCne, mul_one]
      have hn2 : (dotProduct r r / (lambda * dotProduct r r - dotProduct r (A *ᵥ r)))^2
            * (lambda * dotProduct r r - dotProduct r (A *ᵥ r))
          = (dotProduct r r / (lambda * dotProduct r r - dotProduct r (A *ᵥ r)))
            * dotProduct r r := by
        rw [pow_two, mul_assoc, htC]
      have htpos : 0 < dotProduct r r / (lambda * dotProduct r r - dotProduct r (A *ᵥ r)) :=
        div_pos hpos hCpos
      have hmul : 0 < (dotProduct r r / (lambda * dotProduct r r - dotProduct r (A *ᵥ r)))
          * dotProduct r r := mul_pos htpos hpos
      have h1 := hkey (dotProduct r r / (lambda * dotProduct r r - dotProduct r (A *ᵥ r)))
      nlinarith [h1, hn2, hmul]
  have hfinal : A *ᵥ u - lambda • u = 0 := by
    rw [← hr]
    exact hzero
  exact sub_eq_zero.mp hfinal
  /- @proof-region region.target-node.session.1c35e96878cd15d4 end -/
