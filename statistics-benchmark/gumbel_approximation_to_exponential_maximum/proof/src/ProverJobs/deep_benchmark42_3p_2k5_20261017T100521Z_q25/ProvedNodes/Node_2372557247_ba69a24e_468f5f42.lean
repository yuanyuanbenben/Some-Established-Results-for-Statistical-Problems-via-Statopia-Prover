import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q25.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q25.Base

open MeasureTheory ProbabilityTheory
open scoped BigOperators

open MeasureTheory ProbabilityTheory
open scoped BigOperators

set_option autoImplicit false in
theorem statopia_math_node_2372557247_ba69a24e : ∀ (n : ℕ) (hn : 1 ≤ n) (B E : ℝ) (hB : 0 ≤ B) (hBE : B ≤ E),
    E ^ n - B ^ n ≤ (n : ℝ) * E ^ (n - 1) * (E - B) ∧
      (n = 1 → E ^ n - B ^ n = (n : ℝ) * E ^ (n - 1) * (E - B)) := by
  /- @proof-region region.target-node.session.0c3f36b9c9df7a2d begin -/
  intro n
  induction n with
  | zero =>
    intro h0
    exfalso
    omega
  | succ k ih =>
    intro hn B E hB hBE
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · refine ⟨?_, ?_⟩ <;> simp
    · have hk1 : 1 ≤ k := by omega
      obtain ⟨ihle, -⟩ := ih hk1 B E hB hBE
      have hE : 0 ≤ E := le_trans hB hBE
      have hEB : 0 ≤ E - B := sub_nonneg.mpr hBE
      have hpow : E ^ k = E ^ (k - 1) * E := by
        rw [← pow_succ, Nat.sub_add_cancel hk1]
      have h1 : E * (E ^ k - B ^ k) ≤ (k : ℝ) * E ^ k * (E - B) := by
        calc E * (E ^ k - B ^ k)
            ≤ E * ((k : ℝ) * E ^ (k - 1) * (E - B)) :=
              mul_le_mul_of_nonneg_left ihle hE
          _ = (k : ℝ) * E ^ k * (E - B) := by rw [hpow]; ring
      have hBkE : B ^ k ≤ E ^ k := pow_le_pow_left₀ hB hBE k
      have h2 : B ^ k * (E - B) ≤ E ^ k * (E - B) :=
        mul_le_mul_of_nonneg_right hBkE hEB
      have hmain : E ^ (k + 1) - B ^ (k + 1) ≤ ((k + 1 : ℕ) : ℝ) * E ^ k * (E - B) := by
        calc E ^ (k + 1) - B ^ (k + 1)
            = E * (E ^ k - B ^ k) + B ^ k * (E - B) := by
              rw [pow_succ, pow_succ]
              ring
          _ ≤ (k : ℝ) * E ^ k * (E - B) + E ^ k * (E - B) := add_le_add h1 h2
          _ = ((k + 1 : ℕ) : ℝ) * E ^ k * (E - B) := by
              rw [Nat.cast_add, Nat.cast_one]
              ring
      refine ⟨?_, ?_⟩
      · simpa using hmain
      · intro h1eq
        omega
  /- @proof-region region.target-node.session.0c3f36b9c9df7a2d end -/
