import ProverJobs.real_main_theorem_edd06e2c7e6c.Vocabulary
import ProverJobs.real_main_theorem_edd06e2c7e6c.Base
import ProverJobs.real_main_theorem_edd06e2c7e6c.ProvedNodes.Node_1231998112_26c8ceab_5b4097d6
import ProverJobs.real_main_theorem_edd06e2c7e6c.ProvedNodes.Node_2755318678_16f2be55_fa9b4632
import ProverJobs.real_main_theorem_edd06e2c7e6c.ProvedNodes.Node_3315247046_78d260c2_b5b0898c
import ProverJobs.real_main_theorem_edd06e2c7e6c.ProvedNodes.Node_3776635361_5eaf0306_47c63d95





set_option autoImplicit false in
theorem statopia_math_node_835102445_1358d677 : ∀ (a : ℕ → ℕ) (ha : IsValidSeq a)
    (m q : ℕ)
    (hmS : 0 < m ∧ ∀ i : ℕ, 1 < Nat.gcd m (a i))
    (hmMin : ∀ d : ℕ, d ∣ m → d < m → ¬ (0 < d ∧ ∀ i : ℕ, 1 < Nat.gcd d (a i)))
    (hq : Nat.Prime q) (hqm : q ∣ m),
    ∃ m' : ℕ, (0 < m' ∧ ∀ i : ℕ, 1 < Nat.gcd m' (a i)) ∧
      (∀ d : ℕ, d ∣ m' → d < m' → ¬ (0 < d ∧ ∀ i : ℕ, 1 < Nat.gcd d (a i))) ∧
      q ∣ m' ∧ m' / q ≤ a 0 := by
  /- @proof-region region.target-node.session.9e096d5022d11924 begin -/
  intro a ha m
  refine Nat.strong_induction_on m ?_
  intro n ih q hnS hnMin hq hqn
  by_cases hle : n / q ≤ a 0
  · exact ⟨n, hnS, hnMin, hqn, hle⟩
  · set x := n / q with hxdef
    have hxq : x * q = n := by rw [hxdef]; exact Nat.div_mul_cancel hqn
    have hxn : n = q * x := by rw [← hxq, Nat.mul_comm]
    have hxlt : x < n := by
      rcases Nat.eq_zero_or_pos x with h0 | hpos
      · rw [h0, Nat.zero_mul] at hxq
        omega
      · have h2 : 2 * x ≤ q * x := Nat.mul_le_mul_right x hq.two_le
        omega
    have hxdvd : x ∣ n := ⟨q, hxq.symm⟩
    have hxgt : a 0 < x := not_le.mp hle
    have hnotS : ¬ (0 < x ∧ ∀ i : ℕ, 1 < Nat.gcd x (a i)) := hnMin x hxdvd hxlt
    obtain ⟨i, hai_lt, hgcd⟩ := statopia_math_node_3315247046_78d260c2 a ha x hxgt hnotS
    have haiS : 0 < a i ∧ ∀ j : ℕ, 1 < Nat.gcd (a i) (a j) :=
      (statopia_math_node_3776635361_5eaf0306 a ha).2.2.2.2.2.1 i
    obtain ⟨m1, hm1M, hm1dvdai⟩ := (statopia_math_node_1231998112_26c8ceab a ha).2.1 (a i) haiS
    have hm1S : 0 < m1 ∧ ∀ j : ℕ, 1 < Nat.gcd m1 (a j) := hm1M.1
    have hm1Min : ∀ d : ℕ, d ∣ m1 → d < m1 → ¬ (0 < d ∧ ∀ k : ℕ, 1 < Nat.gcd d (a k)) :=
      hm1M.2
    have hm1le : m1 ≤ a i := Nat.le_of_dvd haiS.1 hm1dvdai
    have hm1lt : m1 < n :=
      lt_of_lt_of_le (lt_of_le_of_lt hm1le hai_lt) (Nat.le_of_dvd hnS.1 hxdvd)
    have hg1 : Nat.gcd m1 x = 1 := by
      have h1 : Nat.gcd m1 x ∣ Nat.gcd (a i) x :=
        Nat.dvd_gcd (dvd_trans (Nat.gcd_dvd_left m1 x) hm1dvdai) (Nat.gcd_dvd_right m1 x)
      have h2 : Nat.gcd (a i) x = 1 := by rw [Nat.gcd_comm]; exact hgcd
      rw [h2] at h1
      exact Nat.dvd_one.mp h1
    have hshare : 1 < Nat.gcd n m1 :=
      statopia_math_node_2755318678_16f2be55 a ha n m1 hnS hm1S
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hshare.ne'
    have hpdvdm1 : p ∣ m1 := dvd_trans hpdvd (Nat.gcd_dvd_right n m1)
    have hpnx : ¬ p ∣ x := by
      intro hpx
      have hpg : p ∣ Nat.gcd m1 x := Nat.dvd_gcd hpdvdm1 hpx
      rw [hg1] at hpg
      have h1 : p = 1 := Nat.dvd_one.mp hpg
      have h2 : 2 ≤ p := hp.two_le
      omega
    have hpq : p = q := by
      have hqx : p ∣ q ∨ p ∣ x :=
        hp.dvd_mul.mp (hxn ▸ dvd_trans hpdvd (Nat.gcd_dvd_left n m1))
      rcases hqx with h | h
      · exact (Nat.prime_dvd_prime_iff_eq hp hq).mp h
      · exact absurd h hpnx
    exact ih m1 hm1lt q hm1S hm1Min hq (hpq ▸ hpdvdm1)
  /- @proof-region region.target-node.session.9e096d5022d11924 end -/
