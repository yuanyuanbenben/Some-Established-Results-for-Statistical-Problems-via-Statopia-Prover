import ProverJobs.real_imo2026_problem6_acf5714d7c7d.Vocabulary
import ProverJobs.real_imo2026_problem6_acf5714d7c7d.Base
import ProverJobs.real_imo2026_problem6_acf5714d7c7d.ProvedNodes.Node_190487331_0bb17c24_6b422d58
import ProverJobs.real_imo2026_problem6_acf5714d7c7d.ProvedNodes.Node_3572779525_bbb7c22f_9e149e52
open IMO2026P6

namespace IMO2026P6

set_option autoImplicit false in
theorem statopia_math_node_202768106_72663a92 : ∀ (a : Nat → Nat) (ha : IsValidSeq a) (n : Nat),
    ∃ k : Nat,
      (∀ p : Nat, Nat.Prime p → p ∣ a k → p ∣ a n) ∧
      (∀ p : Nat, Nat.Prime p → p ∣ a k → p ≤ a 0) := by
  /- @proof-region region.target-node.session.1c8376bb884164bf begin -/
  classical
  intro a ha n
  revert n
  refine fun n => Nat.strongRecOn n ?_
  intro n ih
  by_cases hsmall : ∀ p : Nat, Nat.Prime p → p ∣ a n → p ≤ a 0
  · exact ⟨n, fun p hp hpk => hpk, hsmall⟩
  · push_neg at hsmall
    obtain ⟨q, hq, hqn, hqB⟩ := hsmall
    have hn : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · exfalso
        rw [h] at hqn
        have hle : q ≤ a 0 := Nat.le_of_dvd (by have := ha.1 0; omega) hqn
        omega
      · omega
    set m : Nat := a n / q with hm
    have han : a n = q * m := by
      rw [hm]
      exact (Nat.mul_div_cancel' hqn).symm
    have hgcd : ∀ j, j < n → 1 < Nat.gcd m (a j) := by
      intro j hj
      obtain ⟨k, hksub, hkbound⟩ := ih j hj
      obtain ⟨p, hp, hpn, hpk⟩ := (statopia_math_node_190487331_0bb17c24 a ha).2 n k
      have hpB : p ≤ a 0 := hkbound p hp hpk
      have hpj : p ∣ a j := hksub p hp hpk
      have hpne : p ≠ q := by
        intro hpq
        rw [hpq] at hpB
        exact absurd hpB (not_le.mpr hqB)
      have hpm : p ∣ m := by
        have hpqm : p ∣ q * m := by rw [← han]; exact hpn
        rcases (hp.dvd_mul).mp hpqm with hc | hc
        · exfalso
          rcases hq.eq_one_or_self_of_dvd p hc with h1 | h1
          · have := hp.two_le; omega
          · exact hpne h1
        · exact hc
      have hpg : p ∣ Nat.gcd m (a j) := Nat.dvd_gcd hpm hpj
      have hgpos : 0 < Nat.gcd m (a j) := by
        apply Nat.gcd_pos_of_pos_right
        have := ha.1 j
        omega
      have hle : p ≤ Nat.gcd m (a j) := Nat.le_of_dvd hgpos hpg
      have := hp.two_le
      omega
    obtain ⟨ell, helln, hellsub⟩ :=
      statopia_math_node_3572779525_bbb7c22f a ha n hn q hq hqB m han hgcd
    obtain ⟨k, hksub, hkbound⟩ := ih ell helln
    exact ⟨k, fun p hp hpk => hellsub p hp (hksub p hp hpk), hkbound⟩
  /- @proof-region region.target-node.session.1c8376bb884164bf end -/

end IMO2026P6
