import ProverJobs.real_main_theorem_edd06e2c7e6c.Vocabulary
import ProverJobs.real_main_theorem_edd06e2c7e6c.Base
import ProverJobs.real_main_theorem_edd06e2c7e6c.ProvedNodes.Node_1231998112_26c8ceab_5b4097d6


set_option autoImplicit false in
theorem statopia_math_node_230051687_03829abe : ∀ (a : ℕ → ℕ) (ha : IsValidSeq a),
    let S : ℕ → Prop := fun x => 0 < x ∧ ∀ i : ℕ, 1 < Nat.gcd x (a i)
    let M : Set ℕ := {m : ℕ | S m ∧ ∀ d : ℕ, d ∣ m → d < m → ¬ S d}
    ∀ m ∈ M, ∀ p : ℕ, p.Prime → ¬ p * p ∣ m := by
  /- @proof-region region.target-node.session.7e314281fc5b85ed begin -/
  intro a ha S M m hm p hp hpp
  obtain ⟨hmS, hmmin⟩ := hm
  obtain ⟨hmpos, hmgcd⟩ := hmS
  obtain ⟨k, hk⟩ := hpp
  have hp2 : 2 ≤ p := hp.two_le
  have hppos : 0 < p := by omega
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, mul_zero] at hk
      omega
    · exact h
  have hxpos : 0 < p * k := Nat.mul_pos hppos hkpos
  have hk_lt : k < p * k := by
    calc k = 1 * k := (one_mul k).symm
      _ < p * k := Nat.mul_lt_mul_of_pos_right (by omega : 1 < p) hkpos
  have hx_dvd : p * k ∣ m := by
    refine ⟨p, ?_⟩
    rw [hk]
    ring
  have hx_lt : p * k < m := by
    rw [hk]
    calc p * k < p * (p * k) := Nat.mul_lt_mul_of_pos_left hk_lt hppos
      _ = p * p * k := by ring
  have hSx : S (p * k) := by
    refine ⟨hxpos, ?_⟩
    intro i
    have hg : 1 < Nat.gcd m (a i) := hmgcd i
    obtain ⟨r, hpr, hrdvd⟩ :=
      Nat.exists_prime_and_dvd (n := Nat.gcd m (a i)) (by omega)
    have hrm : r ∣ m := dvd_trans hrdvd (Nat.gcd_dvd_left m (a i))
    have hra : r ∣ a i := dvd_trans hrdvd (Nat.gcd_dvd_right m (a i))
    have hrx : r ∣ p * k := by
      rw [hk] at hrm
      rcases (Nat.Prime.dvd_mul hpr).mp hrm with h | h
      · have hrp : r ∣ p := ((Nat.Prime.dvd_mul hpr).mp h).elim id id
        obtain ⟨c, hc⟩ := hrp
        exact ⟨c * k, by rw [hc, mul_assoc]⟩
      · obtain ⟨c, hc⟩ := h
        exact ⟨p * c, by rw [hc]; ring⟩
    have hrg : r ∣ Nat.gcd (p * k) (a i) := Nat.dvd_gcd hrx hra
    have hgpos : 0 < Nat.gcd (p * k) (a i) := Nat.gcd_pos_of_pos_left (a i) hxpos
    have hle : r ≤ Nat.gcd (p * k) (a i) := Nat.le_of_dvd hgpos hrg
    have hr2 : 2 ≤ r := hpr.two_le
    omega
  exact hmmin (p * k) hx_dvd hx_lt hSx
  /- @proof-region region.target-node.session.7e314281fc5b85ed end -/
