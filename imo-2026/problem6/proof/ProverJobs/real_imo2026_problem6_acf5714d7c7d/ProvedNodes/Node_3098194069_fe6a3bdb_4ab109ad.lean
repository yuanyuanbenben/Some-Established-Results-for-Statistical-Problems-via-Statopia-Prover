import ProverJobs.real_imo2026_problem6_acf5714d7c7d.Vocabulary
import ProverJobs.real_imo2026_problem6_acf5714d7c7d.Base

open IMO2026P6

namespace IMO2026P6

set_option autoImplicit false in
theorem statopia_math_node_3098194069_fe6a3bdb : ∀ (a : Nat → Nat) (ha : IsValidSeq a)
    (N v : Nat) (hBv : a 0 ≤ v) (hvN : v ≤ a N)
    (hgcd : ∀ j, j ≤ N → 1 < Nat.gcd v (a j)),
    ∃ k, k ≤ N ∧ v = a k := by
  /- @proof-region region.target-node.session.fa0f75a6f49d72c2 begin -/
  intro a ha N v hBv hvN hgcd
  let P : Nat → Prop := fun j => v ≤ a j
  have hP : ∃ j, P j := ⟨N, hvN⟩
  let k := Nat.find hP
  have hkP : v ≤ a k := Nat.find_spec hP
  have hkN : k ≤ N := Nat.find_min' hP hvN
  have hkmin : ∀ j, j < k → a j < v := by
    intro j hj
    have h : ¬ (v ≤ a j) := Nat.find_min hP hj
    omega
  have hkey : v = a k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · rw [hk0] at hkP ⊢
      exact le_antisymm hkP hBv
    · have hk_eq : (k - 1) + 1 = k := by omega
      have hlt : k - 1 < k := by omega
      have ham : a (k - 1) < v := hkmin (k - 1) hlt
      by_cases hlt2 : v < a k
      · exfalso
        have h := (ha.2 (k - 1)).2.2 v ham (by rw [hk_eq]; exact hlt2)
        obtain ⟨i, hi_le, higcd⟩ := h
        have hiN : i ≤ N := by omega
        have hcontr := hgcd i hiN
        rw [higcd] at hcontr
        exact absurd hcontr (lt_irrefl 1)
      · omega
  exact ⟨k, hkN, hkey⟩
  /- @proof-region region.target-node.session.fa0f75a6f49d72c2 end -/

end IMO2026P6
