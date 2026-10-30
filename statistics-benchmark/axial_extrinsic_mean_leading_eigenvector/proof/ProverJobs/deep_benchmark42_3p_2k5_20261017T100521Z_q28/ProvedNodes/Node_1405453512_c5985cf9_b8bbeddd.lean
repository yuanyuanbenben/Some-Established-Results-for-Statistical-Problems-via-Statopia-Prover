import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q28.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q28.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q28.ProvedNodes.Node_2436574301_d58fdb18_c1a4b65f

open Matrix

open Matrix

set_option autoImplicit false in
theorem statopia_math_node_1405453512_c5985cf9 : ∀ (d n : ℕ) (hn : 1 ≤ n)
    (x : Fin n → Fin d → ℝ)
    (hx : ∀ i, dotProduct (x i) (x i) = 1),
    ∀ u : Fin d → ℝ, dotProduct u u = 1 →
      (n : ℝ)⁻¹ * ∑ i, ∑ j, ∑ k, (u j * u k - x i j * x i k) ^ 2 =
        2 * (1 - dotProduct u (((n : ℝ)⁻¹ • ∑ i, vecMulVec (x i) (x i)) *ᵥ u)) := by
  /- @proof-region region.target-node.session.fa7143b731a602f3 begin -/
  intro d n hn x hx u hu
  obtain ⟨_, hAq⟩ := statopia_math_node_2436574301_d58fdb18 d n hn x
  have hinner : ∀ i : Fin n, ∑ j : Fin d, ∑ k : Fin d,
      (u j * u k - x i j * x i k) ^ 2 = 2 * (1 - (dotProduct u (x i)) ^ 2) := by
    intro i
    have huu : dotProduct u u = ∑ j : Fin d, u j ^ 2 := by
      simp [dotProduct, pow_two]
    have hxx : dotProduct (x i) (x i) = ∑ j : Fin d, (x i j) ^ 2 := by
      simp [dotProduct, pow_two]
    have hux : dotProduct u (x i) = ∑ j : Fin d, u j * x i j := by
      simp [dotProduct]
    have h1 : (∑ j : Fin d, ∑ k : Fin d, (u j * u k) ^ 2) = (dotProduct u u) ^ 2 := by
      rw [huu]
      calc
        ∑ j : Fin d, ∑ k : Fin d, (u j * u k) ^ 2
            = ∑ j : Fin d, ∑ k : Fin d, u j ^ 2 * u k ^ 2 := by
              apply Finset.sum_congr rfl
              intro j hj
              apply Finset.sum_congr rfl
              intro k hk
              ring
        _ = (∑ j : Fin d, u j ^ 2) * (∑ k : Fin d, u k ^ 2) := by
              rw [← Fintype.sum_mul_sum]
        _ = (∑ j : Fin d, u j ^ 2) ^ 2 := by ring
    have h2 : (∑ j : Fin d, ∑ k : Fin d, (x i j * x i k) ^ 2) =
        (dotProduct (x i) (x i)) ^ 2 := by
      rw [hxx]
      calc
        ∑ j : Fin d, ∑ k : Fin d, (x i j * x i k) ^ 2
            = ∑ j : Fin d, ∑ k : Fin d, (x i j) ^ 2 * (x i k) ^ 2 := by
              apply Finset.sum_congr rfl
              intro j hj
              apply Finset.sum_congr rfl
              intro k hk
              ring
        _ = (∑ j : Fin d, (x i j) ^ 2) * (∑ k : Fin d, (x i k) ^ 2) := by
              rw [← Fintype.sum_mul_sum]
        _ = (∑ j : Fin d, (x i j) ^ 2) ^ 2 := by ring
    have h3 : (∑ j : Fin d, ∑ k : Fin d, u j * u k * x i j * x i k) =
        (dotProduct u (x i)) ^ 2 := by
      rw [hux]
      calc
        ∑ j : Fin d, ∑ k : Fin d, u j * u k * x i j * x i k
            = ∑ j : Fin d, ∑ k : Fin d, (u j * x i j) * (u k * x i k) := by
              apply Finset.sum_congr rfl
              intro j hj
              apply Finset.sum_congr rfl
              intro k hk
              ring
        _ = (∑ j : Fin d, u j * x i j) * (∑ k : Fin d, u k * x i k) := by
              rw [← Fintype.sum_mul_sum]
        _ = (∑ j : Fin d, u j * x i j) ^ 2 := by ring
    calc
      ∑ j : Fin d, ∑ k : Fin d, (u j * u k - x i j * x i k) ^ 2
          = ∑ j : Fin d, ∑ k : Fin d,
              ((u j * u k) ^ 2 + (x i j * x i k) ^ 2 - 2 * (u j * u k * x i j * x i k)) := by
            apply Finset.sum_congr rfl
            intro j hj
            apply Finset.sum_congr rfl
            intro k hk
            ring
      _ = ∑ j : Fin d, ((∑ k : Fin d, (u j * u k) ^ 2)
            + (∑ k : Fin d, (x i j * x i k) ^ 2)
            - 2 * (∑ k : Fin d, u j * u k * x i j * x i k)) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = (∑ j : Fin d, ∑ k : Fin d, (u j * u k) ^ 2)
            + (∑ j : Fin d, ∑ k : Fin d, (x i j * x i k) ^ 2)
            - 2 * (∑ j : Fin d, ∑ k : Fin d, u j * u k * x i j * x i k) := by
            rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = 2 * (1 - (dotProduct u (x i)) ^ 2) := by
            rw [h1, h2, h3, hx i, hu]
            ring
  have hsum : (∑ i : Fin n, ∑ j : Fin d, ∑ k : Fin d,
      (u j * u k - x i j * x i k) ^ 2)
      = 2 * ((n : ℝ) - ∑ i : Fin n, (dotProduct u (x i)) ^ 2) := by
    calc
      ∑ i : Fin n, ∑ j : Fin d, ∑ k : Fin d, (u j * u k - x i j * x i k) ^ 2
          = ∑ i : Fin n, 2 * (1 - (dotProduct u (x i)) ^ 2) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hinner i
      _ = 2 * ((n : ℝ) - ∑ i : Fin n, (dotProduct u (x i)) ^ 2) := by
            rw [← Finset.mul_sum]
            congr 1
            rw [Finset.sum_sub_distrib]
            simp
  calc
    (n : ℝ)⁻¹ * ∑ i : Fin n, ∑ j : Fin d, ∑ k : Fin d,
        (u j * u k - x i j * x i k) ^ 2
        = (n : ℝ)⁻¹ * (2 * ((n : ℝ) - ∑ i : Fin n, (dotProduct u (x i)) ^ 2)) := by
          rw [hsum]
    _ = 2 * (1 - (n : ℝ)⁻¹ * ∑ i : Fin n, (dotProduct u (x i)) ^ 2) := by
          calc
            (n : ℝ)⁻¹ * (2 * ((n : ℝ) - ∑ i : Fin n, (dotProduct u (x i)) ^ 2))
                = 2 * ((n : ℝ)⁻¹ * ((n : ℝ) - ∑ i : Fin n, (dotProduct u (x i)) ^ 2)) := by ring
            _ = 2 * ((n : ℝ)⁻¹ * (n : ℝ) -
                  (n : ℝ)⁻¹ * ∑ i : Fin n, (dotProduct u (x i)) ^ 2) := by rw [mul_sub]
            _ = 2 * (1 - (n : ℝ)⁻¹ * ∑ i : Fin n, (dotProduct u (x i)) ^ 2) := by
                  have hn0 : (n : ℝ) ≠ 0 := by
                    have hnpos : (0 : ℝ) < (n : ℝ) := by
                      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
                    exact ne_of_gt hnpos
                  rw [inv_mul_cancel₀ hn0]
    _ = 2 * (1 - dotProduct u (((n : ℝ)⁻¹ • ∑ i : Fin n, vecMulVec (x i) (x i)) *ᵥ u)) := by
          rw [hAq u]
  /- @proof-region region.target-node.session.fa7143b731a602f3 end -/
