import ProverJobs.real_main_theorem_3393c3b8aa74.Vocabulary
import ProverJobs.real_main_theorem_3393c3b8aa74.Base

open TriangleGame

namespace TriangleGame

set_option autoImplicit false in
theorem statopia_math_node_4212101893_b868743c : ∀ (t : ℝ) (ht0 : 0 < t) (ht180 : t < 180)
    (h : ∃ z : ℤ, (180 : ℝ) = (z : ℝ) * t),
    ∃ n : ℕ, 2 ≤ n ∧ t = 180 / (n : ℝ) := by
  /- @proof-region region.target-node.session.84d818ed037e9b71 begin -/
  intro t ht0 ht180 h
  rcases h with ⟨z, hz⟩
  have hzt : (z : ℝ) * t = 180 := hz.symm
  have hz_pos : (0 : ℝ) < (z : ℝ) := by
    have hpos : 0 < t * (z : ℝ) := by rw [mul_comm, hzt]; norm_num
    exact pos_of_mul_pos_right hpos (le_of_lt ht0)
  have hz_gt1 : (1 : ℝ) < (z : ℝ) := by
    have h1 : (0 : ℝ) < ((z : ℝ) - 1) * t := by
      have heq : ((z : ℝ) - 1) * t = (z : ℝ) * t - t := by ring
      rw [heq, hzt]; linarith [ht180]
    have h1' : 0 < t * ((z : ℝ) - 1) := by rw [mul_comm]; exact h1
    have h2 : 0 < (z : ℝ) - 1 := pos_of_mul_pos_right h1' (le_of_lt ht0)
    linarith
  have hz_nonneg_int : (0 : ℤ) ≤ z := by exact_mod_cast (le_of_lt hz_pos)
  have hz_ge2 : (2 : ℤ) ≤ z := by
    have h1 : (1 : ℤ) < z := by exact_mod_cast hz_gt1
    omega
  let n : ℕ := z.toNat
  have hnz : (n : ℤ) = z := Int.toNat_of_nonneg hz_nonneg_int
  have hnR : (n : ℝ) = (z : ℝ) := by
    rw [← hnz]; simp
  have hnt : (n : ℝ) * t = 180 := by rw [hnR, hzt]
  have hn_ge2 : 2 ≤ n := by
    have h2 : (2 : ℤ) ≤ (n : ℤ) := by rw [hnz]; exact hz_ge2
    exact_mod_cast h2
  refine ⟨n, hn_ge2, ?_⟩
  have hnne : (n : ℝ) ≠ 0 := by
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      have : (0 : ℕ) < n := by omega
      exact_mod_cast this
    exact ne_of_gt hnpos
  rw [eq_div_iff hnne, mul_comm]
  exact hnt
  /- @proof-region region.target-node.session.84d818ed037e9b71 end -/

end TriangleGame
