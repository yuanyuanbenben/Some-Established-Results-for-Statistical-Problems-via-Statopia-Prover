import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q28.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q28.Base

open Matrix

open Matrix

set_option autoImplicit false in
theorem statopia_math_node_2436574301_d58fdb18 : ∀ (d n : ℕ) (hn : 1 ≤ n)
    (x : Fin n → Fin d → ℝ),
    let A : Matrix (Fin d) (Fin d) ℝ := (n : ℝ)⁻¹ • ∑ i, vecMulVec (x i) (x i)
    Aᵀ = A ∧
      ∀ u : Fin d → ℝ,
        dotProduct u (A *ᵥ u) = (n : ℝ)⁻¹ * ∑ i, (dotProduct u (x i)) ^ 2 := by
  /- @proof-region region.target-node.session.4870b78df61b9729 begin -/
  intro d n hn x
  dsimp only
  constructor
  · ext j k
    simp only [Matrix.transpose_apply, Matrix.smul_apply, Matrix.sum_apply, Matrix.vecMulVec,
      Matrix.of_apply]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  · intro u
    have hA : ∀ j k : Fin d, ((n : ℝ)⁻¹ • ∑ i, vecMulVec (x i) (x i)) j k
        = (n : ℝ)⁻¹ * ∑ i, x i j * x i k := by
      intro j k
      simp [Matrix.smul_apply, Matrix.sum_apply, Matrix.vecMulVec, Matrix.of_apply, smul_eq_mul]
    have hAu : ∀ j : Fin d, (((n : ℝ)⁻¹ • ∑ i, vecMulVec (x i) (x i)) *ᵥ u) j
        = ∑ k, ((n : ℝ)⁻¹ * ∑ i, x i j * x i k) * u k := by
      intro j
      simp only [Matrix.mulVec, dotProduct]
      exact Finset.sum_congr rfl fun k _ => by rw [hA]
    have hSjk : ∀ j k : Fin d, (u j * (∑ i, x i j * x i k)) * u k
        = ∑ i, (u j * x i j) * (x i k * u k) := by
      intro j k
      rw [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    have e1 : (∑ j, u j * ∑ k, ((n : ℝ)⁻¹ * ∑ i, x i j * x i k) * u k)
        = ∑ j, ∑ k, u j * (((n : ℝ)⁻¹ * ∑ i, x i j * x i k) * u k) := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.mul_sum Finset.univ
        (fun k => ((n : ℝ)⁻¹ * ∑ i, x i j * x i k) * u k) (u j)
    have e2 : (∑ j, ∑ k, u j * (((n : ℝ)⁻¹ * ∑ i, x i j * x i k) * u k))
        = ∑ j, ∑ k, (n : ℝ)⁻¹ * ((u j * (∑ i, x i j * x i k)) * u k) := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring
    have e3 : (∑ j, ∑ k, (n : ℝ)⁻¹ * ((u j * (∑ i, x i j * x i k)) * u k))
        = ∑ j, ∑ k, (n : ℝ)⁻¹ * ∑ i, (u j * x i j) * (x i k * u k) := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      rw [hSjk j k]
    have e4 : (∑ j, ∑ k, (n : ℝ)⁻¹ * ∑ i, (u j * x i j) * (x i k * u k))
        = (n : ℝ)⁻¹ * ∑ j, ∑ k, ∑ i, (u j * x i j) * (x i k * u k) := by
      have inner : ∀ j : Fin d, (∑ k, (n : ℝ)⁻¹ * ∑ i, (u j * x i j) * (x i k * u k))
          = (n : ℝ)⁻¹ * ∑ k, ∑ i, (u j * x i j) * (x i k * u k) := by
        intro j
        exact (Finset.mul_sum Finset.univ
          (fun k => ∑ i, (u j * x i j) * (x i k * u k)) (n : ℝ)⁻¹).symm
      simp only [inner]
      exact (Finset.mul_sum Finset.univ
        (fun j => ∑ k, ∑ i, (u j * x i j) * (x i k * u k)) (n : ℝ)⁻¹).symm
    have eswap : (∑ j, ∑ k, ∑ i, (u j * x i j) * (x i k * u k))
        = ∑ i, ∑ j, ∑ k, (u j * x i j) * (x i k * u k) := by
      calc (∑ j, ∑ k, ∑ i, (u j * x i j) * (x i k * u k))
          = ∑ j, ∑ i, ∑ k, (u j * x i j) * (x i k * u k) := by
            apply Finset.sum_congr rfl
            intro j _
            exact Finset.sum_comm
        _ = ∑ i, ∑ j, ∑ k, (u j * x i j) * (x i k * u k) := Finset.sum_comm
    have efac : (∑ i, ∑ j, ∑ k, (u j * x i j) * (x i k * u k))
        = ∑ i, (∑ j, u j * x i j) * (∑ k, x i k * u k) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (Finset.sum_mul_sum Finset.univ Finset.univ
        (fun j => u j * x i j) (fun k => x i k * u k)).symm
    calc u ⬝ᵥ (((n : ℝ)⁻¹ • ∑ i, vecMulVec (x i) (x i)) *ᵥ u)
        = ∑ j, u j * ∑ k, ((n : ℝ)⁻¹ * ∑ i, x i j * x i k) * u k := by
          simp only [dotProduct]
          exact Finset.sum_congr rfl fun j _ => by rw [hAu]
      _ = ∑ j, ∑ k, u j * (((n : ℝ)⁻¹ * ∑ i, x i j * x i k) * u k) := e1
      _ = ∑ j, ∑ k, (n : ℝ)⁻¹ * ((u j * (∑ i, x i j * x i k)) * u k) := e2
      _ = ∑ j, ∑ k, (n : ℝ)⁻¹ * ∑ i, (u j * x i j) * (x i k * u k) := e3
      _ = (n : ℝ)⁻¹ * ∑ j, ∑ k, ∑ i, (u j * x i j) * (x i k * u k) := e4
      _ = (n : ℝ)⁻¹ * ∑ i, ∑ j, ∑ k, (u j * x i j) * (x i k * u k) := by rw [eswap]
      _ = (n : ℝ)⁻¹ * ∑ i, (∑ j, u j * x i j) * (∑ k, x i k * u k) := by rw [efac]
      _ = (n : ℝ)⁻¹ * ∑ i, (u ⬝ᵥ x i) ^ 2 := by
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          have hsum : (∑ k, x i k * u k) = ∑ j, u j * x i j :=
            Finset.sum_congr rfl fun k _ => by ring
          rw [hsum]
          simp only [dotProduct, pow_two]
  /- @proof-region region.target-node.session.4870b78df61b9729 end -/
