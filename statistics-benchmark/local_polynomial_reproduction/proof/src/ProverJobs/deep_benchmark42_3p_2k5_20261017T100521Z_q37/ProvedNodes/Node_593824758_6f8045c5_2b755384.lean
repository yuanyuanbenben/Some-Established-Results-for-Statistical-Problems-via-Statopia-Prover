import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q37.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q37.Base

open Matrix

open Matrix

set_option autoImplicit false in
theorem statopia_math_node_593824758_6f8045c5 : ∀ (n : ℕ) (hn : 1 ≤ n)
    (ell : ℕ)
    (X : Fin n → ℝ)
    (K : ℝ → ℝ)
    (x h : ℝ) (hh : 0 < h),
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
      ∀ k : ℕ, k ≤ ell →
        ∑ i, W i * ((X i - x) / h) ^ k = (0 : ℝ) ^ k := by
  /- @proof-region region.target-node.session.e90ade6fa509649b begin -/
  intro n hn ell X K x h hh U B hB W k hk
  obtain ⟨k', rfl⟩ : ∃ k' : Fin (ell + 1), k'.1 = k := ⟨⟨k, Nat.lt_succ_of_le hk⟩, rfl⟩
  have hUval : ∀ (u : ℝ) (m : Fin (ell + 1)), U u m = u ^ m.1 / (Nat.factorial m.1 : ℝ) :=
    fun u m => rfl
  have hBval : ∀ a b, B a b =
      ((n : ℝ) * h)⁻¹ * ∑ i, U ((X i - x) / h) a * U ((X i - x) / h) b * K ((X i - x) / h) :=
    fun a b => rfl
  have hF : (Nat.factorial k'.1 : ℝ) ≠ 0 := by
    have hpos : (0 : ℝ) < (Nat.factorial k'.1 : ℝ) := by exact_mod_cast Nat.factorial_pos k'.1
    exact ne_of_gt hpos
  have hinv : ∀ a, ∑ b, B⁻¹ a b * B b k' = (1 : Matrix (Fin (ell + 1)) (Fin (ell + 1)) ℝ) a k' := by
    intro a
    rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul B hB]
  have key : ∀ (c0 : ℝ) (d : Fin (ell + 1) → ℝ) (e : Fin n → Fin (ell + 1) → ℝ)
      (g : Fin n → ℝ) (Bv : Fin (ell + 1) → Fin (ell + 1) → ℝ),
      ∑ i, c0 * (∑ a, d a * ∑ b, Bv a b * e i b) * g i * e i k'
        = ∑ a, ∑ b, d a * Bv a b * (c0 * ∑ i, e i b * e i k' * g i) := by
    intro c0 d e g Bv
    have h1 : ∀ i, c0 * (∑ a, d a * ∑ b, Bv a b * e i b) * g i * e i k'
        = ∑ a, ∑ b, d a * Bv a b * (c0 * (e i b * e i k' * g i)) := by
      intro i
      simp only [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
      ring
    have hexp : ∑ i, c0 * (∑ a, d a * ∑ b, Bv a b * e i b) * g i * e i k'
        = ∑ i, ∑ a, ∑ b, d a * Bv a b * (c0 * (e i b * e i k' * g i)) := by
      simp only [h1]
    have hswap : ∑ i, ∑ a, ∑ b, d a * Bv a b * (c0 * (e i b * e i k' * g i))
        = ∑ a, ∑ b, ∑ i, d a * Bv a b * (c0 * (e i b * e i k' * g i)) := by
      calc ∑ i, ∑ a, ∑ b, d a * Bv a b * (c0 * (e i b * e i k' * g i))
          = ∑ a, ∑ i, ∑ b, d a * Bv a b * (c0 * (e i b * e i k' * g i)) := Finset.sum_comm
        _ = ∑ a, ∑ b, ∑ i, d a * Bv a b * (c0 * (e i b * e i k' * g i)) := by
            refine Finset.sum_congr rfl (fun a _ => ?_)
            exact Finset.sum_comm
    rw [hexp, hswap]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [Finset.mul_sum]
    rw [← Finset.mul_sum]
  have key3 : ∀ (A Bv : Fin n → ℝ) (G F : ℝ), F ≠ 0 →
      (∑ i, A i * (Bv i / F)) * F = (G / F) * F → ∑ i, A i * Bv i = G := by
    intro A Bv G F hFF h
    have h1 : (∑ i, A i * (Bv i / F)) * F = ∑ i, A i * Bv i := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      field_simp
    have h2 : (G / F) * F = G := by field_simp
    rw [h1, h2] at h
    exact h
  have hUmain : ∑ i, (((n : ℝ) * h)⁻¹ * (∑ a, U 0 a * ∑ b, B⁻¹ a b * U ((X i - x) / h) b) *
      K ((X i - x) / h)) * U ((X i - x) / h) k' = U 0 k' := by
    calc ∑ i, (((n : ℝ) * h)⁻¹ * (∑ a, U 0 a * ∑ b, B⁻¹ a b * U ((X i - x) / h) b) *
          K ((X i - x) / h)) * U ((X i - x) / h) k'
        = ∑ a, ∑ b, U 0 a * B⁻¹ a b *
            (((n : ℝ) * h)⁻¹ * ∑ i, U ((X i - x) / h) b * U ((X i - x) / h) k' * K ((X i - x) / h)) :=
          key _ _ _ _ _
      _ = ∑ a, ∑ b, U 0 a * B⁻¹ a b * B b k' := by
          simp only [hBval]
      _ = U 0 k' := by
          calc ∑ a, ∑ b, U 0 a * B⁻¹ a b * B b k'
              = ∑ a, U 0 a * ∑ b, B⁻¹ a b * B b k' := by
                refine Finset.sum_congr rfl (fun a _ => ?_)
                simp only [mul_assoc]
                rw [← Finset.mul_sum]
            _ = ∑ a, U 0 a * (1 : Matrix (Fin (ell + 1)) (Fin (ell + 1)) ℝ) a k' := by
                simp only [hinv]
            _ = U 0 k' := by
                have hsingle : ∀ b ∈ (Finset.univ : Finset (Fin (ell + 1))), b ≠ k' →
                    U 0 b * (1 : Matrix (Fin (ell + 1)) (Fin (ell + 1)) ℝ) b k' = 0 := by
                  intro b _ hb
                  simp [Matrix.one_apply, hb]
                have hnot : k' ∉ (Finset.univ : Finset (Fin (ell + 1))) →
                    U 0 k' * (1 : Matrix (Fin (ell + 1)) (Fin (ell + 1)) ℝ) k' k' = 0 := by
                  intro hmem
                  exact absurd (Finset.mem_univ k') hmem
                rw [Finset.sum_eq_single k' hsingle hnot]
                simp [Matrix.one_apply]
  have hmain : ∑ i, (((n : ℝ) * h)⁻¹ * (∑ a, U 0 a * ∑ b, B⁻¹ a b * U ((X i - x) / h) b) *
      K ((X i - x) / h)) * (((X i - x) / h) ^ k'.1 / (Nat.factorial k'.1 : ℝ)) =
      ((0 : ℝ) ^ k'.1 / (Nat.factorial k'.1 : ℝ)) := hUmain
  show ∑ i, (((n : ℝ) * h)⁻¹ * (∑ a, U 0 a * ∑ b, B⁻¹ a b * U ((X i - x) / h) b) *
    K ((X i - x) / h)) * ((X i - x) / h) ^ k'.1 = (0 : ℝ) ^ k'.1
  exact key3 (fun i => ((n : ℝ) * h)⁻¹ * (∑ a, U 0 a * ∑ b, B⁻¹ a b * U ((X i - x) / h) b) *
      K ((X i - x) / h)) (fun i => ((X i - x) / h) ^ k'.1) ((0 : ℝ) ^ k'.1)
      (Nat.factorial k'.1 : ℝ) hF (congrArg (fun t => t * (Nat.factorial k'.1 : ℝ)) hmain)
  /- @proof-region region.target-node.session.e90ade6fa509649b end -/
