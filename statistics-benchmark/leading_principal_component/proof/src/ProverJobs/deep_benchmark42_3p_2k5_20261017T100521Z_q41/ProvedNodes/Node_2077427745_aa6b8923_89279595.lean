import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q41.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q41.Base

open Matrix

open Matrix

set_option autoImplicit false in
theorem statopia_math_node_2077427745_aa6b8923 : ∀ (n d : ℕ) (hn : 1 ≤ n)
    (x : Fin n → Fin d → ℝ)
    (S : Matrix (Fin d) (Fin d) ℝ)
    (hS : S = (n : ℝ)⁻¹ • ∑ i, vecMulVec (x i) (x i))
    (u : Fin d → ℝ),
    (n : ℝ)⁻¹ * ∑ i, (dotProduct u (x i)) ^ 2 = dotProduct u (S *ᵥ u) := by
  /- @proof-region region.target-node.session.c4a7e79ed766f69a begin -/
  intro n d hn x S hs u
  have hvec : ∀ (i : Fin n) (k j : Fin d), vecMulVec (x i) (x i) k j = x i k * x i j :=
    fun i k j => rfl
  have hadd : ∀ (A B : Matrix (Fin d) (Fin d) ℝ) (k j : Fin d), (A + B) k j = A k j + B k j :=
    fun A B k j => rfl
  have hgen : ∀ (s : Finset (Fin n)) (k j : Fin d),
      (∑ i ∈ s, vecMulVec (x i) (x i)) k j
        = ∑ i ∈ s, vecMulVec (x i) (x i) k j := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro k j
        rw [Finset.sum_empty, Finset.sum_empty]
        rfl
    | insert a s ha ih =>
        intro k j
        rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, ih]
  have hsum_ev : ∀ (k j : Fin d),
      (∑ i : Fin n, vecMulVec (x i) (x i)) k j = ∑ i : Fin n, vecMulVec (x i) (x i) k j :=
    hgen Finset.univ
  have hSapp : ∀ (k j : Fin d), S k j = (n : ℝ)⁻¹ * ∑ i : Fin n, x i k * x i j := by
    intro k j
    rw [hs, Matrix.smul_apply, hsum_ev, smul_eq_mul]
    simp only [hvec]
  have hR : dotProduct u (S *ᵥ u) = ∑ k : Fin d, ∑ j : Fin d, u k * (S k j * u j) := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  have hR2 : (∑ k : Fin d, ∑ j : Fin d, u k * (S k j * u j))
      = ∑ k : Fin d, ∑ j : Fin d,
          u k * (((n : ℝ)⁻¹ * ∑ i : Fin n, x i k * x i j) * u j) := by
    simp only [hSapp]
  have hR3 : (∑ k : Fin d, ∑ j : Fin d,
        u k * (((n : ℝ)⁻¹ * ∑ i : Fin n, x i k * x i j) * u j))
      = ∑ k : Fin d, ∑ j : Fin d, ∑ i : Fin n,
          u k * (((n : ℝ)⁻¹ * (x i k * x i j)) * u j) := by
    simp only [Finset.mul_sum, Finset.sum_mul]
  have hR4 : (∑ k : Fin d, ∑ j : Fin d, ∑ i : Fin n,
        u k * (((n : ℝ)⁻¹ * (x i k * x i j)) * u j))
      = ∑ i : Fin n, ∑ k : Fin d, ∑ j : Fin d,
          u k * (((n : ℝ)⁻¹ * (x i k * x i j)) * u j) := by
    calc
      (∑ k : Fin d, ∑ j : Fin d, ∑ i : Fin n,
          u k * (((n : ℝ)⁻¹ * (x i k * x i j)) * u j))
          = ∑ j : Fin d, ∑ k : Fin d, ∑ i : Fin n,
              u k * (((n : ℝ)⁻¹ * (x i k * x i j)) * u j) := Finset.sum_comm
      _ = ∑ j : Fin d, ∑ i : Fin n, ∑ k : Fin d,
              u k * (((n : ℝ)⁻¹ * (x i k * x i j)) * u j) :=
            Finset.sum_congr rfl (fun j _ => Finset.sum_comm)
      _ = ∑ i : Fin n, ∑ j : Fin d, ∑ k : Fin d,
              u k * (((n : ℝ)⁻¹ * (x i k * x i j)) * u j) := Finset.sum_comm
      _ = ∑ i : Fin n, ∑ k : Fin d, ∑ j : Fin d,
              u k * (((n : ℝ)⁻¹ * (x i k * x i j)) * u j) :=
            Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
  have hR5 : (∑ i : Fin n, ∑ k : Fin d, ∑ j : Fin d,
        u k * (((n : ℝ)⁻¹ * (x i k * x i j)) * u j))
      = ∑ i : Fin n, ∑ k : Fin d, ∑ j : Fin d,
          (n : ℝ)⁻¹ * ((u k * x i k) * (u j * x i j)) := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ =>
      Finset.sum_congr rfl (fun j _ => ?_)))
    ring
  have hA1 : (∑ i : Fin n, (dotProduct u (x i)) ^ 2)
      = ∑ i : Fin n, ∑ k : Fin d, ∑ j : Fin d,
          (u k * x i k) * (u j * x i j) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [pow_two]
    simp only [dotProduct]
    rw [Finset.sum_mul_sum]
  have hA2 : (n : ℝ)⁻¹ * ∑ i : Fin n, ∑ k : Fin d, ∑ j : Fin d,
        (u k * x i k) * (u j * x i j)
      = ∑ i : Fin n, ∑ k : Fin d, ∑ j : Fin d,
          (n : ℝ)⁻¹ * ((u k * x i k) * (u j * x i j)) := by
    simp only [Finset.mul_sum]
  rw [hA1, hA2, hR, hR2, hR3, hR4, hR5]
  /- @proof-region region.target-node.session.c4a7e79ed766f69a end -/
