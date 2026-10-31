import ProverJobs.real_main_theorem_edd06e2c7e6c.Vocabulary
import ProverJobs.real_main_theorem_edd06e2c7e6c.Base
import ProverJobs.real_main_theorem_edd06e2c7e6c.ProvedNodes.Node_3776635361_5eaf0306_47c63d95


set_option autoImplicit false in
theorem statopia_math_node_1319170121_dbae7a97 : ∀ (a : ℕ → ℕ) (ha : IsValidSeq a) (x : ℕ),
    ((0 < x ∧ ∀ i : ℕ, 1 < Nat.gcd x (a i)) ∧ a 0 ≤ x) ↔ ∃ n : ℕ, x = a n := by
  /- @proof-region region.target-node.session.076b98740cdf7130 begin -/
  intro a ha x
  obtain ⟨-, -, hmono, -, hunb, hgood, -, -⟩ :=
    statopia_math_node_3776635361_5eaf0306 a ha
  constructor
  · rintro ⟨⟨-, hxgcd⟩, ha0x⟩
    obtain ⟨n, hn, hmin⟩ : ∃ n, x ≤ a n ∧ ∀ m, x ≤ a m → n ≤ m :=
      ⟨Nat.find (hunb x), Nat.find_spec (hunb x),
        fun m hm => Nat.find_min' (hunb x) hm⟩
    by_cases hcase : x = a n
    · exact ⟨n, hcase⟩
    · have hxn : x < a n := lt_of_le_of_ne hn hcase
      have hn0 : n ≠ 0 := by
        rintro rfl
        exact hcase (le_antisymm hn ha0x)
      obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      subst hm
      have hxam : a m < x := by
        by_contra hcon
        have hle : x ≤ a m := not_lt.mp hcon
        have hle' := hmin m hle
        omega
      obtain ⟨i, -, hi⟩ := (ha.2 m).2.2 x hxam hxn
      have hg := hxgcd i
      rw [hi] at hg
      exact absurd hg (lt_irrefl 1)
  · rintro ⟨n, hn⟩
    subst hn
    exact ⟨hgood n, hmono 0 n (Nat.zero_le n)⟩
  /- @proof-region region.target-node.session.076b98740cdf7130 end -/
