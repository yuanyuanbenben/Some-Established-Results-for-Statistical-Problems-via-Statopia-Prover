import ProverJobs.real_main_theorem_3393c3b8aa74.Vocabulary
import ProverJobs.real_main_theorem_3393c3b8aa74.Base

open TriangleGame

namespace TriangleGame

set_option autoImplicit false in
theorem statopia_math_node_389705034_bebdf092 : ∀ (t lo hi : ℝ) (ht : 0 < t) (hlo : 0 ≤ lo)
    (hhi : hi - lo > t),
    ∃ m : ℕ, 1 ≤ m ∧ lo < (m : ℝ) * t ∧ (m : ℝ) * t < hi := by
  /- @proof-region region.target-node.session.bedfa2774332a49b begin -/
  intro t lo hi ht hlo hhi
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hr : (0 : ℝ) ≤ lo / t := div_nonneg hlo (le_of_lt ht)
  set z : ℤ := ⌊lo / t⌋ with hz
  have hz_nonneg : (0 : ℤ) ≤ z := by
    rw [hz]
    exact Mathlib.Meta.Positivity.int_floor_nonneg hr
  have hz1_nonneg : (0 : ℤ) ≤ z + 1 := by omega
  have hz1_le : (1 : ℤ) ≤ z + 1 := by omega
  refine ⟨(z + 1).toNat, ?_, ?_, ?_⟩
  · have hnat : (((z + 1).toNat : ℕ) : ℤ) = z + 1 := Int.toNat_of_nonneg hz1_nonneg
    have h1 : (1 : ℤ) ≤ (((z + 1).toNat : ℕ) : ℤ) := by rw [hnat]; exact hz1_le
    exact_mod_cast h1
  · have hnat : (((z + 1).toNat : ℕ) : ℤ) = z + 1 := Int.toNat_of_nonneg hz1_nonneg
    have hcast : (((z + 1).toNat : ℕ) : ℝ) = (z : ℝ) + 1 := by
      exact_mod_cast hnat
    have hlt : lo / t < (z : ℝ) + 1 := by
      have h := Int.lt_floor_add_one (lo / t)
      rwa [← hz] at h
    have hmul := mul_lt_mul_of_pos_right hlt ht
    rw [div_mul_cancel₀ lo ht0] at hmul
    rw [hcast]
    exact hmul
  · have hnat : (((z + 1).toNat : ℕ) : ℤ) = z + 1 := Int.toNat_of_nonneg hz1_nonneg
    have hcast : (((z + 1).toNat : ℕ) : ℝ) = (z : ℝ) + 1 := by
      exact_mod_cast hnat
    have hf : (z : ℝ) ≤ lo / t := (Int.le_floor (a := lo / t)).mp (le_of_eq hz)
    have hle : (z : ℝ) + 1 ≤ lo / t + 1 := by linarith
    have hmul : ((z : ℝ) + 1) * t ≤ lo + t := by
      have h1 : ((z : ℝ) + 1) * t ≤ (lo / t + 1) * t :=
        mul_le_mul_of_nonneg_right hle (le_of_lt ht)
      have h2 : (lo / t + 1) * t = lo + t := by
        rw [add_mul, one_mul, div_mul_cancel₀ lo ht0]
      rwa [h2] at h1
    rw [hcast]
    have hhi' : lo + t < hi := by linarith
    linarith
  /- @proof-region region.target-node.session.bedfa2774332a49b end -/

end TriangleGame
