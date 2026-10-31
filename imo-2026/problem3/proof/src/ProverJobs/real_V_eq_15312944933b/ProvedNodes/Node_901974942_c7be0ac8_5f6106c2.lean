import ProverJobs.real_V_eq_15312944933b.Vocabulary
import ProverJobs.real_V_eq_15312944933b.Base

open scoped BigOperators
open LiuBangXiangYu

open scoped BigOperators
namespace LiuBangXiangYu

set_option autoImplicit false in
theorem statopia_math_node_901974942_c7be0ac8 : ∀ (q : ℕ) (hq : 1 ≤ q)
    (a : Fin q → ℝ) (ha_pos : ∀ i, 0 < a i) (ha_sum : ∑ i : Fin q, a i = 1)
    (b : ℕ → ℝ) (hb : ∀ k, b k = ∑ i : Fin q, (if (i : ℕ) < k then a i else 0)),
    b 0 = 0 ∧ b q = 1 ∧ StrictMonoOn b (Set.Icc 0 q) ∧
      (∀ k : Fin q, b ((k : ℕ) + 1) - b (k : ℕ) = a k) := by
  /- @proof-region region.target-node.session.25255babf1d93aae begin -/
  intro q hq a ha_pos ha_sum b hb
  have hb0 : b 0 = 0 := by
    rw [hb 0]
    simp
  have hbq : b q = 1 := by
    rw [hb q, ← ha_sum]
    exact Finset.sum_congr rfl (fun i _ => if_pos i.isLt)
  have hbstep : ∀ k : Fin q, b ((k : ℕ) + 1) - b (k : ℕ) = a k := by
    intro k
    rw [hb ((k : ℕ) + 1), hb (k : ℕ), ← Finset.sum_sub_distrib]
    have hsingle : (∑ i : Fin q, (if (i : ℕ) = (k : ℕ) then a i else 0)) = a k := by
      refine (Finset.sum_eq_single k ?_ ?_).trans ?_
      · intro i _ hi
        exact if_neg (fun h => hi (Fin.ext h))
      · intro hk
        exact absurd (Finset.mem_univ k) hk
      · exact if_pos rfl
    rw [← hsingle]
    exact Finset.sum_congr rfl (fun i _ => by
      by_cases hlt : (i : ℕ) < (k : ℕ)
      · rw [if_pos (show (i : ℕ) < (k : ℕ) + 1 by omega), if_pos hlt,
          if_neg (show ¬ ((i : ℕ) = (k : ℕ)) by omega)]
        ring
      · by_cases heq : (i : ℕ) = (k : ℕ)
        · rw [if_pos (show (i : ℕ) < (k : ℕ) + 1 by omega), if_neg hlt, if_pos heq]
          ring
        · rw [if_neg (show ¬ ((i : ℕ) < (k : ℕ) + 1) by omega), if_neg hlt, if_neg heq]
          ring)
  have hble : ∀ k l : ℕ, k ≤ l → b k ≤ b l := by
    intro k l hkl
    rw [hb k, hb l]
    apply Finset.sum_le_sum
    intro i _
    by_cases hlt : (i : ℕ) < k
    · have h2 : (i : ℕ) < l := by omega
      simp only [if_pos hlt, if_pos h2, le_refl]
    · rw [if_neg hlt]
      split_ifs with h2
      · exact le_of_lt (ha_pos i)
      · exact le_refl 0
  have hmono : StrictMonoOn b (Set.Icc 0 q) := by
    intro k hk l hl hkl
    have hkq : k < q := lt_of_lt_of_le hkl hl.2
    have hpos : 0 < b (k + 1) - b k := by
      rw [hbstep ⟨k, hkq⟩]
      exact ha_pos ⟨k, hkq⟩
    have hle1 : b (k + 1) ≤ b l := hble (k + 1) l (Nat.succ_le_of_lt hkl)
    exact lt_of_lt_of_le (sub_pos.mp hpos) hle1
  exact ⟨hb0, hbq, hmono, hbstep⟩
  /- @proof-region region.target-node.session.25255babf1d93aae end -/

end LiuBangXiangYu
