import ProverJobs.real_main_theorem_f979009c9fbd.Vocabulary
import ProverJobs.real_main_theorem_f979009c9fbd.Base
import ProverJobs.real_main_theorem_f979009c9fbd.ProvedNodes.Node_571599843_c7abf9a7_16b1ea46

set_option autoImplicit false in
theorem statopia_math_node_1700959973_f12e7196 : ∀ (B B' : Board) (hMove : Move B B')
    (hPos : ∀ a ∈ B, 1 ≤ a),
    B.prod.primeFactors = B'.prod.primeFactors := by
  /- @proof-region region.target-node.session.e845c4a8bcad21dc begin -/
  intro B B' hMove _hPos
  obtain ⟨m, n, s, hm, hn, hB, hB'⟩ := hMove
  obtain ⟨_, _, _, hB'prod, hBprod, _⟩ :=
    statopia_math_node_571599843_c7abf9a7 B B' m n s hm hn hB hB'
  have hg0 : Nat.gcd m n ≠ 0 := by omega
  have hL0 : Nat.lcm m n ≠ 0 := by
    intro h
    have hq0 : Nat.lcm m n / Nat.gcd m n = 0 := by simp [h]
    omega
  have hgL : Nat.gcd m n ∣ Nat.lcm m n :=
    dvd_trans (Nat.gcd_dvd_left m n) (Nat.dvd_lcm_left m n)
  have hsafe : (Nat.gcd m n).primeFactors ⊆ (Nat.lcm m n).primeFactors := by
    intro p hp
    rw [Nat.mem_primeFactors] at hp
    rw [Nat.mem_primeFactors]
    exact ⟨hp.1, dvd_trans hp.2.1 hgL, hL0⟩
  have hunion : (Nat.gcd m n).primeFactors ∪ (Nat.lcm m n).primeFactors
      = (Nat.lcm m n).primeFactors := by
    apply Finset.ext
    intro p
    simp only [Finset.mem_union]
    constructor
    · rintro (hp | hp)
      · exact hsafe hp
      · exact hp
    · intro hp
      exact Or.inr hp
  by_cases hS0 : s.prod = 0
  · have hBz : B.prod = 0 := by rw [hBprod, hS0, mul_zero]
    have hB'z : B'.prod = 0 := by rw [hB'prod, hS0, mul_zero]
    rw [hBz, hB'z]
  · have hS0' : s.prod ≠ 0 := hS0
    calc
      B.prod.primeFactors
          = (Nat.gcd m n * Nat.lcm m n * s.prod).primeFactors := by rw [hBprod]
      _ = ((Nat.gcd m n).primeFactors ∪ (Nat.lcm m n).primeFactors) ∪ (s.prod).primeFactors := by
          rw [Nat.primeFactors_mul (mul_ne_zero hg0 hL0) hS0', Nat.primeFactors_mul hg0 hL0]
      _ = (Nat.lcm m n).primeFactors ∪ (s.prod).primeFactors := by rw [hunion]
      _ = (Nat.lcm m n * s.prod).primeFactors := by rw [← Nat.primeFactors_mul hL0 hS0']
      _ = B'.prod.primeFactors := by rw [hB'prod]
  /- @proof-region region.target-node.session.e845c4a8bcad21dc end -/
