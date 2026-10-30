import ProverJobs.real_main_theorem_f979009c9fbd.Vocabulary
import ProverJobs.real_main_theorem_f979009c9fbd.Base
import ProverJobs.real_main_theorem_f979009c9fbd.ProvedNodes.Node_2501567596_37502bdc_e945184d
import ProverJobs.real_main_theorem_f979009c9fbd.ProvedNodes.Node_3256552224_5ffbc5d4_c887b752

set_option autoImplicit false in
theorem statopia_math_node_2804265859_24cd4c8c : ∀ (B : Board) (hpos : ∀ a ∈ B, 1 ≤ a),
    ∃ B' : Board, Reachable B B' ∧ IsTerminal B' := by
  /- @proof-region region.target-node.session.cef59057514fee83 begin -/
  have two_large : ∀ B : Board, 1 < (B.filter (fun a => 1 < a)).card →
      ∃ (m n : ℕ) (s : Board), 1 < m ∧ 1 < n ∧ B = m ::ₘ n ::ₘ s := by
    intro B
    refine Multiset.induction_on B ?_ ?_
    · intro h
      simp at h
    · intro c t ih h
      by_cases hct : 1 < c
      · rw [Multiset.filter_cons_of_pos t hct, Multiset.card_cons] at h
        have ht2 : 0 < (t.filter (fun a => 1 < a)).card := Nat.lt_of_succ_lt_succ h
        obtain ⟨d, hd⟩ := Multiset.card_pos_iff_exists_mem.mp ht2
        have hdt : d ∈ t := (Multiset.mem_filter.mp hd).1
        have hdp : 1 < d := (Multiset.mem_filter.mp hd).2
        exact ⟨c, d, t.erase d, hct, hdp, by rw [Multiset.cons_erase hdt]⟩
      · rw [Multiset.filter_cons_of_neg t hct] at h
        obtain ⟨m, n, s, hm, hn, ht⟩ := ih h
        refine ⟨m, n, c ::ₘ s, hm, hn, ?_⟩
        rw [ht, Multiset.cons_swap c m (n ::ₘ s), Multiset.cons_swap c n s]
  have key : ∀ n : ℕ, ∀ B : Board,
      B.prod + (B.filter (fun a => 1 < a)).card = n →
      (∀ a ∈ B, 1 ≤ a) → ∃ B' : Board, Reachable B B' ∧ IsTerminal B' := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro B hPhi hpos
      by_cases hterm : (B.filter (fun a => 1 < a)).card ≤ 1
      · exact ⟨B, Relation.ReflTransGen.refl, hterm⟩
      · push_neg at hterm
        obtain ⟨m, nn, s, hm, hn, hB⟩ := two_large B hterm
        have hmove : Move B (Nat.gcd m nn ::ₘ (Nat.lcm m nn / Nat.gcd m nn) ::ₘ s) :=
          ⟨m, nn, s, hm, hn, hB, rfl⟩
        have hpos' : ∀ a ∈ (Nat.gcd m nn ::ₘ (Nat.lcm m nn / Nat.gcd m nn) ::ₘ s), 1 ≤ a :=
          (statopia_math_node_3256552224_5ffbc5d4 B
            (Nat.gcd m nn ::ₘ (Nat.lcm m nn / Nat.gcd m nn) ::ₘ s) hmove hpos).1
        have hdesc : (Nat.gcd m nn ::ₘ (Nat.lcm m nn / Nat.gcd m nn) ::ₘ s).prod +
            ((Nat.gcd m nn ::ₘ (Nat.lcm m nn / Nat.gcd m nn) ::ₘ s).filter
              (fun a => 1 < a)).card < n := by
          have h := statopia_math_node_2501567596_37502bdc B
            (Nat.gcd m nn ::ₘ (Nat.lcm m nn / Nat.gcd m nn) ::ₘ s) hmove hpos
          rw [hPhi] at h
          exact h
        obtain ⟨B''', hreach, hterm'⟩ := ih _ hdesc
          (Nat.gcd m nn ::ₘ (Nat.lcm m nn / Nat.gcd m nn) ::ₘ s) rfl hpos'
        exact ⟨B''', Relation.ReflTransGen.head hmove hreach, hterm'⟩
  intro B hpos
  exact key _ B rfl hpos
  /- @proof-region region.target-node.session.cef59057514fee83 end -/
