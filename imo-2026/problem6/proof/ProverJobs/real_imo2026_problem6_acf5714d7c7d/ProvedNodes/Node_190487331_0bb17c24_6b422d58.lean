import ProverJobs.real_imo2026_problem6_acf5714d7c7d.Vocabulary
import ProverJobs.real_imo2026_problem6_acf5714d7c7d.Base

open IMO2026P6

namespace IMO2026P6

set_option autoImplicit false in
theorem statopia_math_node_190487331_0bb17c24 : ∀ (a : Nat -> Nat) (ha : IsValidSeq a),
    (forall i j : Nat, 1 < Nat.gcd (a i) (a j)) ∧
      (forall i j : Nat, exists p : Nat, p.Prime ∧ p ∣ a i ∧ p ∣ a j) := by
  /- @proof-region region.target-node.session.5733341f9b42ee33 begin -/
  intro a ha
  have ha1 : ∀ n, 1 < a n := ha.1
  have hg : ∀ n i, i ≤ n → 1 < Nat.gcd (a (n + 1)) (a i) := fun n => (ha.2 n).2.1
  have hcommon : ∀ i j, 1 < Nat.gcd (a i) (a j) := by
    intro i j
    rcases lt_trichotomy i j with hlt | heq | hgt
    · have h1 : i ≤ j - 1 := by omega
      have h2 : j - 1 + 1 = j := by omega
      have h := hg (j - 1) i h1
      rw [h2, Nat.gcd_comm] at h
      exact h
    · rw [heq, Nat.gcd_self]
      exact ha1 j
    · have h1 : j ≤ i - 1 := by omega
      have h2 : i - 1 + 1 = i := by omega
      have h := hg (i - 1) j h1
      rw [h2] at h
      exact h
  constructor
  · exact hcommon
  · intro i j
    have hne : Nat.gcd (a i) (a j) ≠ 1 := by have h := hcommon i j; omega
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    exact ⟨p, hp, dvd_trans hpdvd (Nat.gcd_dvd_left (a i) (a j)),
      dvd_trans hpdvd (Nat.gcd_dvd_right (a i) (a j))⟩
  /- @proof-region region.target-node.session.5733341f9b42ee33 end -/

end IMO2026P6
