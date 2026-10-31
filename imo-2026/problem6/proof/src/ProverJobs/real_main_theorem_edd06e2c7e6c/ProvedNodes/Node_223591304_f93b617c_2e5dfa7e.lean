import ProverJobs.real_main_theorem_edd06e2c7e6c.Vocabulary
import ProverJobs.real_main_theorem_edd06e2c7e6c.Base
import ProverJobs.real_main_theorem_edd06e2c7e6c.ProvedNodes.Node_1231998112_26c8ceab_5b4097d6
import ProverJobs.real_main_theorem_edd06e2c7e6c.ProvedNodes.Node_2027774880_d06a152e_dd4a1ad2
import ProverJobs.real_main_theorem_edd06e2c7e6c.ProvedNodes.Node_3776635361_5eaf0306_47c63d95




set_option autoImplicit false in
theorem statopia_math_node_223591304_f93b617c : ∀ (a : ℕ → ℕ) (ha : IsValidSeq a) (L : ℕ)
    (hL : 0 < L)
    (hdvd : ∀ m : ℕ, (0 < m ∧ ∀ i : ℕ, 1 < Nat.gcd m (a i)) ∧
        (∀ d : ℕ, d ∣ m → d < m → ¬ (0 < d ∧ ∀ i : ℕ, 1 < Nat.gcd d (a i))) → m ∣ L)
    (x : ℕ) (hx : 0 < x),
    ((0 < x ∧ ∀ i : ℕ, 1 < Nat.gcd x (a i)) ↔
      (0 < x + L ∧ ∀ i : ℕ, 1 < Nat.gcd (x + L) (a i))) := by
  /- @proof-region region.target-node.session.330fa11ab373d31e begin -/
  intro a ha L hL hdvd x hx
  let S : ℕ → Prop := fun y => 0 < y ∧ ∀ i : ℕ, 1 < Nat.gcd y (a i)
  let M : Set ℕ := {m : ℕ | S m ∧ ∀ d : ℕ, d ∣ m → d < m → ¬ S d}
  have hcov : ∀ y : ℕ, 0 < y → (S y ↔ ∃ m ∈ M, m ∣ y) := by
    intro y hy
    exact (statopia_math_node_1231998112_26c8ceab a ha).2.2 y hy
  have key : ∀ m ∈ M, (m ∣ x ↔ m ∣ x + L) := by
    intro m hm
    have hmdvd : m ∣ L := hdvd m hm
    have hmpos : 0 < m := hm.1.1
    constructor
    · intro h
      exact Nat.dvd_add h hmdvd
    · rintro ⟨u, hu⟩
      obtain ⟨s, hs⟩ := hmdvd
      have hsu : s ≤ u := by
        have hle : m * s ≤ m * u := by
          rw [← hs, ← hu]
          omega
        exact Nat.le_of_mul_le_mul_left hle hmpos
      refine ⟨u - s, ?_⟩
      rw [Nat.mul_sub_left_distrib, ← hu, ← hs]
      omega
  have hpos : 0 < x + L := by omega
  show S x ↔ S (x + L)
  rw [hcov x hx, hcov (x + L) hpos]
  constructor
  · rintro ⟨m, hm, h⟩
    exact ⟨m, hm, (key m hm).1 h⟩
  · rintro ⟨m, hm, h⟩
    exact ⟨m, hm, (key m hm).2 h⟩
  /- @proof-region region.target-node.session.330fa11ab373d31e end -/
