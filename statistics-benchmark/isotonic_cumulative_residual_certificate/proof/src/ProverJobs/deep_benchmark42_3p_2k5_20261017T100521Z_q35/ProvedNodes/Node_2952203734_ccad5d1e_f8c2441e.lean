import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q35.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q35.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q35.ProvedNodes.Node_3210606411_004fbd06_18ec203e


set_option autoImplicit false in
theorem statopia_math_node_2952203734_ccad5d1e : ∀ (n : ℕ) (y thetaHat theta : Fin n → ℝ),
    let rho : ℕ → ℝ := fun j => if h : j < n then y ⟨j, h⟩ - thetaHat ⟨j, h⟩ else 0
    let alpha : ℕ → ℝ := fun j => if h : j < n then theta ⟨j, h⟩ - thetaHat ⟨j, h⟩ else 0
    let R : ℕ → ℝ := fun k => ∑ j : Fin n, if (j : ℕ) < k then y j - thetaHat j else 0
    let P : ℕ → ℝ := fun k => ∑ j ∈ Finset.range k, rho j
    (∀ k : ℕ, R k = P k) → R n = 0 →
      (∑ i ∈ Finset.range n, alpha i * rho i)
        = ∑ i ∈ Finset.range (n - 1), (alpha i - alpha (i + 1)) * R (i + 1) := by
  /- @proof-region region.target-node.session.05167b5242267806 begin -/
  intro n y thetaHat theta
  dsimp only
  intro hRP hRn
  have hb := Finset.sum_range_by_parts
    (fun j : ℕ => if h : j < n then theta ⟨j, h⟩ - thetaHat ⟨j, h⟩ else 0)
    (fun j : ℕ => if h : j < n then y ⟨j, h⟩ - thetaHat ⟨j, h⟩ else 0) n
  simp only [smul_eq_mul] at hb
  have hPn : (∑ i ∈ Finset.range n, (if h : i < n then y ⟨i, h⟩ - thetaHat ⟨i, h⟩ else 0)) = 0 := by
    rw [← hRP n]
    exact hRn
  rw [hb, hPn, mul_zero, zero_sub, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← hRP (i + 1)]
  ring
  /- @proof-region region.target-node.session.05167b5242267806 end -/
