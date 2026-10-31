import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q07.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q07.Base

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

set_option autoImplicit false in
theorem statopia_math_node_2992835122_67aeacbc : ∀ {Ω : Type*} (X : ℕ → Ω → ℝ) (mean varianceSq : ℝ),
    let Xbar : ℕ → Ω → ℝ :=
      fun n ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, X i ω
    let V : ℕ → Ω → ℝ :=
      fun n ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, (X i ω - Xbar n ω) ^ 2
    let D : ℕ → Ω → ℝ := fun n ω => Xbar n ω - mean
    let Y : ℕ → Ω → ℝ := fun i ω => (X i ω - mean) ^ 2
    ∀ (n : ℕ) (ω : Ω),
      Real.sqrt (n : ℝ) * (V n ω - varianceSq)
        = (Real.sqrt (n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, (Y i ω - varianceSq)
          - Real.sqrt (n : ℝ) * (D n ω) ^ 2 := by
  /- @proof-region region.target-node.session.194d8e045b37a108 begin -/
  intro Ω X mean varianceSq
  dsimp only
  intro n ω
  by_cases hn : n = 0
  · subst n
    simp
  · have hN : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have hNpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    set s : ℝ := Real.sqrt (n : ℝ) with hsdef
    have hs : s ≠ 0 := by
      rw [hsdef]
      exact (Real.sqrt_pos.2 hNpos).ne'
    have hss : s * s = (n : ℝ) := by
      rw [hsdef]
      simpa [pow_two] using Real.sq_sqrt hNpos.le
    have key : ∀ (a b c d e : ℝ), a * a = b → a ≠ 0 →
        a * (b⁻¹ * (d - b * e ^ 2) - c) = a⁻¹ * (d - b * c) - a * e ^ 2 := by
      intro a b c d e hab ha
      have hb : b ≠ 0 := by
        rw [← hab]
        exact mul_ne_zero ha ha
      have hL : a * (a * (b⁻¹ * (d - b * e ^ 2) - c)) = d - b * e ^ 2 - b * c := by
        rw [← mul_assoc, hab, mul_sub, ← mul_assoc, mul_inv_cancel₀ hb, one_mul]
      have hR : a * (a⁻¹ * (d - b * c) - a * e ^ 2) = d - b * c - b * e ^ 2 := by
        have h1 : a * (a⁻¹ * (d - b * c)) = d - b * c := by
          rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]
        have h2 : a * (a * e ^ 2) = b * e ^ 2 := by
          rw [← mul_assoc, hab]
        rw [mul_sub, h1, h2]
      have hmul : a * (a * (b⁻¹ * (d - b * e ^ 2) - c))
          = a * (a⁻¹ * (d - b * c) - a * e ^ 2) := by
        rw [hL, hR]
        ring
      exact mul_left_cancel₀ ha hmul
    have hNB : (n : ℝ) * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, X i ω - mean)
        = ∑ i ∈ Finset.range n, (X i ω - mean) := by
      rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ hN, one_mul]
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hexp : ∀ (z : ℕ → ℝ) (b : ℝ),
        (∑ i ∈ Finset.range n, (z i - b) ^ 2)
          = (∑ i ∈ Finset.range n, (z i) ^ 2) - 2 * b * (∑ i ∈ Finset.range n, z i)
            + (n : ℝ) * b ^ 2 := by
      intro z b
      have hpt : ∀ i, (z i - b) ^ 2 = z i ^ 2 - 2 * b * z i + b ^ 2 := fun i => by ring
      simp only [hpt]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul]
    have hSx : (∑ i ∈ Finset.range n, (X i ω - (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, X j ω) ^ 2)
        = (∑ i ∈ Finset.range n, (X i ω - mean) ^ 2)
          - (n : ℝ) * ((n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, X j ω - mean) ^ 2 := by
      have hp : ∀ i, (X i ω - (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, X j ω) ^ 2
          = ((X i ω - mean) - ((n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, X j ω - mean)) ^ 2 :=
        fun i => by ring
      simp only [hp]
      rw [hexp (fun i => X i ω - mean) ((n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, X j ω - mean)]
      rw [← hNB]
      ring
    have hSy : (∑ i ∈ Finset.range n, ((X i ω - mean) ^ 2 - varianceSq))
        = (∑ i ∈ Finset.range n, (X i ω - mean) ^ 2) - (n : ℝ) * varianceSq := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hSx, hSy]
    exact key s (n : ℝ) varianceSq (∑ i ∈ Finset.range n, (X i ω - mean) ^ 2)
      ((n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, X j ω - mean) hss hs
  /- @proof-region region.target-node.session.194d8e045b37a108 end -/
