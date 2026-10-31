import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q37.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q37.ProvedNodes
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q37.Base

open Matrix

theorem local_polynomial_reproduction
    (n : ℕ) (hn : 1 ≤ n)
    (ell : ℕ)
    (X : Fin n → ℝ)
    (K : ℝ → ℝ) (hK_nonneg : ∀ u, 0 ≤ K u)
    (x h : ℝ) (hh : 0 < h) :
    let U : ℝ → Fin (ell + 1) → ℝ := fun u k ↦
      u ^ k.1 / (Nat.factorial k.1 : ℝ)
    let B : Matrix (Fin (ell + 1)) (Fin (ell + 1)) ℝ := fun a b ↦
      ((n : ℝ) * h)⁻¹ *
        ∑ i, U ((X i - x) / h) a * U ((X i - x) / h) b *
          K ((X i - x) / h)
    IsUnit B.det →
      let W : Fin n → ℝ := fun i ↦
        ((n : ℝ) * h)⁻¹ *
          (∑ a, U 0 a * ∑ b, B⁻¹ a b * U ((X i - x) / h) b) *
          K ((X i - x) / h)
      ∀ Q : Polynomial ℝ, Q.natDegree ≤ ell →
        ∑ i, W i * Q.eval (X i) = Q.eval x
:= by
  /- @proof-region region.root.b13f32ddb323 begin -/
  simp only []
  intro hB Q hQ
  let U : ℝ → Fin (ell + 1) → ℝ := fun u k => u ^ k.1 / (Nat.factorial k.1 : ℝ)
  let B : Matrix (Fin (ell + 1)) (Fin (ell + 1)) ℝ := fun a b =>
    ((n : ℝ) * h)⁻¹ *
      ∑ i, U ((X i - x) / h) a * U ((X i - x) / h) b * K ((X i - x) / h)
  let W : Fin n → ℝ := fun i =>
    ((n : ℝ) * h)⁻¹ *
      (∑ a, U 0 a * ∑ b, B⁻¹ a b * U ((X i - x) / h) b) * K ((X i - x) / h)
  let P : Polynomial ℝ := Q.comp (Polynomial.C x + Polynomial.C h * Polynomial.X)
  obtain ⟨hPdeg, hPeval, hPzero⟩ :=
    statopia_math_node_3849316766_249c6d5e ell x h Q hQ P rfl
  have hPexp : ∀ t : ℝ, P.eval t = ∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k * t ^ k := by
    intro t
    exact Polynomial.eval_eq_sum_range t
  have hmom : ∀ k : ℕ, k ≤ ell → ∑ i, W i * ((X i - x) / h) ^ k = (0 : ℝ) ^ k :=
    statopia_math_node_593824758_6f8045c5 n hn ell X K x h hh hB
  have hz : ∀ i : Fin n, Q.eval (X i) = P.eval ((X i - x) / h) := by
    intro i
    rw [hPeval ((X i - x) / h)]
    congr 1
    field_simp
    ring
  show ∑ i, W i * Q.eval (X i) = Q.eval x
  calc ∑ i, W i * Q.eval (X i)
      = ∑ i, W i * P.eval ((X i - x) / h) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hz i]
    _ = ∑ i, W i *
          (∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k * ((X i - x) / h) ^ k) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hPexp ((X i - x) / h)]
    _ = ∑ k ∈ Finset.range (P.natDegree + 1),
          ∑ i, W i * (P.coeff k * ((X i - x) / h) ^ k) := by
          simp only [Finset.mul_sum]
          exact Finset.sum_comm
    _ = ∑ k ∈ Finset.range (P.natDegree + 1),
          P.coeff k * ∑ i, W i * ((X i - x) / h) ^ k := by
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = ∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k * (0 : ℝ) ^ k := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [hmom k (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) hPdeg)]
    _ = Q.eval x := by
          rw [← hPexp 0]
          exact hPzero
  /- @proof-region region.root.b13f32ddb323 end -/
