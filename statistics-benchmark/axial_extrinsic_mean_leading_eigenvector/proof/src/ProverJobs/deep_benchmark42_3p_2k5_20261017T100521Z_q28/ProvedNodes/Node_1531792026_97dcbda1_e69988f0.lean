import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q28.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q28.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q28.ProvedNodes.Node_1405453512_c5985cf9_b8bbeddd

open Matrix

open Matrix

set_option autoImplicit false in
theorem statopia_math_node_1531792026_97dcbda1 : ∀ (d n : ℕ) (hn : 1 ≤ n)
    (x : Fin n → Fin d → ℝ)
    (hx : ∀ i, dotProduct (x i) (x i) = 1)
    (v : Fin d → ℝ) (hv : dotProduct v v = 1)
    (lambda : ℝ),
    let A : Matrix (Fin d) (Fin d) ℝ :=
      (n : ℝ)⁻¹ • ∑ i, vecMulVec (x i) (x i)
    let q : (Fin d → ℝ) → ℝ := fun u => dotProduct u (A *ᵥ u)
    let objective : (Fin d → ℝ) → ℝ := fun u ↦
      (n : ℝ)⁻¹ *
        ∑ i, ∑ j, ∑ k,
          (u j * u k - x i j * x i k) ^ 2
    A *ᵥ v = lambda • v →
    (∀ w, dotProduct w w = 1 → q w ≤ lambda) →
      q v = lambda ∧
      (∀ w, dotProduct w w = 1 → 2 * (1 - lambda) ≤ objective w) ∧
      dotProduct (-v) (-v) = 1 ∧
      objective v = 2 * (1 - lambda) ∧
      objective (-v) = 2 * (1 - lambda) ∧
      (∀ w, dotProduct w w = 1 → objective v ≤ objective w) ∧
      (∀ w, dotProduct w w = 1 → objective (-v) ≤ objective w) := by
  /- @proof-region region.target-node.session.67e2ac89a9661abd begin -/
  intro d n hn x hx v hv lambda
  dsimp only
  intro hAv hRay
  have hq : dotProduct v (((n : ℝ)⁻¹ • ∑ i, vecMulVec (x i) (x i)) *ᵥ v) = lambda := by
    rw [hAv, dotProduct_smul, hv, smul_eq_mul, mul_one]
  have hneg : dotProduct (-v) (-v) = 1 := by
    have h1 : (-v : Fin d → ℝ) = (-1 : ℝ) • v := by
      funext i
      simp [smul_eq_mul]
    rw [h1]
    rw [dotProduct_smul]
    rw [dotProduct_comm ((-1 : ℝ) • v) v]
    rw [dotProduct_smul]
    rw [hv]
    rw [smul_eq_mul, smul_eq_mul]
    norm_num
  have hObj : ∀ u : Fin d → ℝ, dotProduct u u = 1 →
      (n : ℝ)⁻¹ * ∑ i, ∑ j, ∑ k, (u j * u k - x i j * x i k) ^ 2
        = 2 * (1 - dotProduct u (((n : ℝ)⁻¹ • ∑ i, vecMulVec (x i) (x i)) *ᵥ u)) := by
    intro u hu
    exact statopia_math_node_1405453512_c5985cf9 d n hn x hx u hu
  have hobj_v : (n : ℝ)⁻¹ * ∑ i, ∑ j, ∑ k, (v j * v k - x i j * x i k) ^ 2
      = 2 * (1 - lambda) := by
    rw [hObj v hv, hq]
  have hobj_neg : (n : ℝ)⁻¹ * ∑ i, ∑ j, ∑ k, ((-v) j * (-v) k - x i j * x i k) ^ 2
      = 2 * (1 - lambda) := by
    have heq : (∑ i, ∑ j, ∑ k, ((-v) j * (-v) k - x i j * x i k) ^ 2)
        = ∑ i, ∑ j, ∑ k, (v j * v k - x i j * x i k) ^ 2 := by
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      refine Finset.sum_congr rfl ?_
      intro k _
      simp
    rw [heq, hobj_v]
  have hbound : ∀ w : Fin d → ℝ, dotProduct w w = 1 →
      2 * (1 - lambda) ≤ (n : ℝ)⁻¹ * ∑ i, ∑ j, ∑ k, (w j * w k - x i j * x i k) ^ 2 := by
    intro w hw
    rw [hObj w hw]
    have hw' := hRay w hw
    linarith
  have hmin_v : ∀ w : Fin d → ℝ, dotProduct w w = 1 →
      (n : ℝ)⁻¹ * ∑ i, ∑ j, ∑ k, (v j * v k - x i j * x i k) ^ 2
        ≤ (n : ℝ)⁻¹ * ∑ i, ∑ j, ∑ k, (w j * w k - x i j * x i k) ^ 2 := by
    intro w hw
    rw [hobj_v]
    exact hbound w hw
  have hmin_neg : ∀ w : Fin d → ℝ, dotProduct w w = 1 →
      (n : ℝ)⁻¹ * ∑ i, ∑ j, ∑ k, ((-v) j * (-v) k - x i j * x i k) ^ 2
        ≤ (n : ℝ)⁻¹ * ∑ i, ∑ j, ∑ k, (w j * w k - x i j * x i k) ^ 2 := by
    intro w hw
    rw [hobj_neg]
    exact hbound w hw
  exact ⟨hq, hbound, hneg, hobj_v, hobj_neg, hmin_v, hmin_neg⟩
  /- @proof-region region.target-node.session.67e2ac89a9661abd end -/
