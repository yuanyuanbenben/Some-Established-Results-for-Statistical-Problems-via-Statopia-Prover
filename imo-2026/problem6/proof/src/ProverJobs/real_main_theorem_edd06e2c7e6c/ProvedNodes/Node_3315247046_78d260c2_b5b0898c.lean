import ProverJobs.real_main_theorem_edd06e2c7e6c.Vocabulary
import ProverJobs.real_main_theorem_edd06e2c7e6c.Base
import ProverJobs.real_main_theorem_edd06e2c7e6c.ProvedNodes.Node_3776635361_5eaf0306_47c63d95


set_option autoImplicit false in
theorem statopia_math_node_3315247046_78d260c2 : ∀ (a : ℕ → ℕ) (ha : IsValidSeq a) (x : ℕ)
    (hx : a 0 < x)
    (hnot : ¬ (0 < x ∧ ∀ i : ℕ, 1 < Nat.gcd x (a i))),
    ∃ i : ℕ, a i < x ∧ Nat.gcd x (a i) = 1 := by
  /- @proof-region region.target-node.session.adc40d5f1df4d713 begin -/
  intro a ha x hx hnot
  obtain ⟨_, _, hmono, _, hunb, hgood, _, _⟩ := statopia_math_node_3776635361_5eaf0306 a ha
  have hex : ∃ k, x ≤ a k := hunb x
  have hfind_ne : Nat.find hex ≠ 0 := by
    intro h0
    have hxle : x ≤ a 0 := h0 ▸ Nat.find_spec hex
    exact absurd hxle (not_le.mpr hx)
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hfind_ne
  have hxle : x ≤ a (m + 1) := by
    have h := Nat.find_spec hex
    rw [hm] at h
    exact h
  have ham : a m < x := by
    have hlt : m < Nat.find hex := by
      rw [hm]
      exact Nat.lt_succ_self m
    exact not_le.mp (Nat.find_min hex hlt)
  have hxlt : x < a (m + 1) := by
    rcases lt_or_eq_of_le hxle with h | h
    · exact h
    · exfalso
      apply hnot
      rw [h]
      exact hgood (m + 1)
  obtain ⟨i, hi, higcd⟩ := (ha.2 m).2.2 x ham hxlt
  exact ⟨i, lt_of_le_of_lt (hmono i m hi) ham, higcd⟩
  /- @proof-region region.target-node.session.adc40d5f1df4d713 end -/
