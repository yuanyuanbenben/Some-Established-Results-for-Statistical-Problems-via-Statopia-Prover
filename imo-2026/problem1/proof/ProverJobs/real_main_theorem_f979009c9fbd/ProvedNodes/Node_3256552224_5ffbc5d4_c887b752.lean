import ProverJobs.real_main_theorem_f979009c9fbd.Vocabulary
import ProverJobs.real_main_theorem_f979009c9fbd.Base


set_option autoImplicit false in
theorem statopia_math_node_3256552224_5ffbc5d4 : ∀ (B B' : Board) (h : Move B B')
    (hpos : ∀ a ∈ B, 1 ≤ a),
    (∀ a ∈ B', 1 ≤ a) ∧ B'.card = B.card := by
  /- @proof-region region.target-node.session.8f7e5af80f2dd894 begin -/
  intro B B' h hpos
  obtain ⟨m, n, s, hm, hn, hB, hB'⟩ := h
  subst hB
  subst hB'
  refine ⟨?_, ?_⟩
  · intro a ha
    simp only [Multiset.mem_cons] at ha
    rcases ha with rfl | rfl | ha
    · exact Nat.gcd_pos_of_pos_left n (by omega)
    · have hg : 0 < Nat.gcd m n := Nat.gcd_pos_of_pos_left n (by omega)
      have hdvd : Nat.gcd m n ∣ Nat.lcm m n :=
        dvd_trans (Nat.gcd_dvd_left m n) (Nat.dvd_lcm_left m n)
      have hmn : 0 < m * n := Nat.mul_pos (by omega) (by omega)
      have hgl : Nat.gcd m n * Nat.lcm m n = m * n := Nat.gcd_mul_lcm m n
      have hl : 0 < Nat.lcm m n := by
        rcases Nat.eq_zero_or_pos (Nat.lcm m n) with h0 | h0
        · rw [h0, mul_zero] at hgl
          omega
        · exact h0
      exact Nat.div_pos (Nat.le_of_dvd hl hdvd) hg
    · exact hpos a (by simp [ha])
  · simp [Multiset.card_cons]
  /- @proof-region region.target-node.session.8f7e5af80f2dd894 end -/
