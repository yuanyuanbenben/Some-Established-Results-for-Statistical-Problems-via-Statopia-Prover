import ProverJobs.real_main_theorem_f979009c9fbd.Vocabulary
import ProverJobs.real_main_theorem_f979009c9fbd.Base


set_option autoImplicit false in
theorem statopia_math_node_571599843_c7abf9a7 : ∀ (B B' : Board) (m n : ℕ) (s : Board)
    (hm : 1 < m) (hn : 1 < n)
    (hB : B = m ::ₘ n ::ₘ s)
    (hB' : B' = Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s),
    Nat.gcd m n ≥ 1 ∧
      Nat.lcm m n / Nat.gcd m n ≥ 1 ∧
      Nat.gcd m n * (Nat.lcm m n / Nat.gcd m n) = Nat.lcm m n ∧
      B'.prod = Nat.lcm m n * s.prod ∧
      B.prod = Nat.gcd m n * Nat.lcm m n * s.prod ∧
      B.prod = Nat.gcd m n * B'.prod := by
  /- @proof-region region.target-node.session.3fec7a4fde2f6b83 begin -/
  intro B B' m n s hm hn hB hB'
  have hm0 : 0 < m := by omega
  have hn0 : 0 < n := by omega
  have hd1 : Nat.gcd m n ≥ 1 := by
    have h := Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left m n) hm0
    omega
  have hdvd : Nat.gcd m n ∣ Nat.lcm m n :=
    dvd_trans (Nat.gcd_dvd_left m n) (Nat.dvd_lcm_left m n)
  have hdq : Nat.gcd m n * (Nat.lcm m n / Nat.gcd m n) = Nat.lcm m n :=
    (mul_comm _ _).trans (Nat.div_mul_cancel hdvd)
  have hq1 : Nat.lcm m n / Nat.gcd m n ≥ 1 := by
    have hpos : 0 < Nat.lcm m n / Nat.gcd m n := by
      rw [Nat.pos_iff_ne_zero]
      intro hq0
      have hlcm0 : Nat.lcm m n = 0 := by rw [hdq.symm, hq0, mul_zero]
      have hmn0 : m * n = 0 := by rw [← Nat.gcd_mul_lcm m n, hlcm0, mul_zero]
      exact mul_ne_zero hm0.ne' hn0.ne' hmn0
    omega
  have hprodB' : B'.prod = Nat.lcm m n * s.prod := by
    rw [hB', Multiset.prod_cons, Multiset.prod_cons, ← mul_assoc, hdq]
  have hprodB : B.prod = Nat.gcd m n * Nat.lcm m n * s.prod := by
    rw [hB, Multiset.prod_cons, Multiset.prod_cons, ← mul_assoc, ← Nat.gcd_mul_lcm m n]
  have hprodBB' : B.prod = Nat.gcd m n * B'.prod := by
    rw [hprodB, hprodB']
    ring
  exact ⟨hd1, hq1, hdq, hprodB', hprodB, hprodBB'⟩
  /- @proof-region region.target-node.session.3fec7a4fde2f6b83 end -/
