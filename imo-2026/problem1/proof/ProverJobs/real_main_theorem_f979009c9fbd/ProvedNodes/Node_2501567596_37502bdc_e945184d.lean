import ProverJobs.real_main_theorem_f979009c9fbd.Vocabulary
import ProverJobs.real_main_theorem_f979009c9fbd.Base
import ProverJobs.real_main_theorem_f979009c9fbd.ProvedNodes.Node_571599843_c7abf9a7_16b1ea46

set_option autoImplicit false in
theorem statopia_math_node_2501567596_37502bdc : ∀ (B B' : Board) (hMove : Move B B') (hpos : ∀ a ∈ B, 1 ≤ a),
    B'.prod + Multiset.card (B'.filter (fun a => 1 < a)) <
      B.prod + Multiset.card (B.filter (fun a => 1 < a)) := by
  /- @proof-region region.target-node.session.37d1ce4bb795a99f begin -/
  intro B B' hMove hpos
  obtain ⟨m, n, s, hm, hn, hB, hB'⟩ := hMove
  obtain ⟨hd1, hq1, hdq, hB'prod, hBprod, hBfac⟩ :=
    statopia_math_node_571599843_c7abf9a7 B B' m n s hm hn hB hB'
  have hS : 0 < s.prod := by
    rw [CanonicallyOrderedAdd.multiset_prod_pos]
    intro a ha
    have hmem : a ∈ B := by
      rw [hB]
      exact Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem ha)
    exact lt_of_lt_of_le Nat.zero_lt_one (hpos a hmem)
  have hApos : 0 < B'.prod := by
    rw [hB']
    simp only [Multiset.prod_cons]
    exact mul_pos (by omega) (mul_pos (by omega) hS)
  have hstep : ∀ (a : ℕ) (t : Board),
      ((a ::ₘ t).filter (fun x => 1 < x)).card ≤ 1 + (t.filter (fun x => 1 < x)).card := by
    intro a t
    by_cases ha : 1 < a
    · rw [Multiset.filter_cons_of_pos (p := fun x => 1 < x) t ha]
      simp only [Multiset.card_cons]
      omega
    · rw [Multiset.filter_cons_of_neg (p := fun x => 1 < x) t ha]
      omega
  have hBf : (B.filter (fun a => 1 < a)).card = 2 + (s.filter (fun a => 1 < a)).card := by
    rw [hB, Multiset.filter_cons_of_pos (p := fun x => 1 < x) (n ::ₘ s) hm,
        Multiset.filter_cons_of_pos (p := fun x => 1 < x) s hn]
    simp only [Multiset.card_cons]
    omega
  have hB'f : (B'.filter (fun a => 1 < a)).card ≤ 2 + (s.filter (fun a => 1 < a)).card := by
    rw [hB']
    have h1 := hstep (Nat.gcd m n) ((Nat.lcm m n / Nat.gcd m n) ::ₘ s)
    have h2 := hstep (Nat.lcm m n / Nat.gcd m n) s
    omega
  by_cases hgd : Nat.gcd m n = 1
  · have hP : B.prod = B'.prod := by rw [hBfac, hgd, one_mul]
    have hNB' : (B'.filter (fun a => 1 < a)).card ≤ 1 + (s.filter (fun a => 1 < a)).card := by
      rw [hB', hgd,
        Multiset.filter_cons_of_neg (p := fun x => 1 < x) ((Nat.lcm m n / 1) ::ₘ s)
          (show ¬ (1 < (1 : ℕ)) by decide)]
      exact hstep (Nat.lcm m n / 1) s
    have hcard : (B'.filter (fun a => 1 < a)).card < (B.filter (fun a => 1 < a)).card := by
      rw [hBf]; omega
    omega
  · have hd2 : 2 ≤ Nat.gcd m n := by omega
    have hPge : B'.prod + 1 ≤ B.prod := by
      rw [hBfac]
      have h2 : B'.prod + 1 ≤ 2 * B'.prod := by omega
      have h3 : 2 * B'.prod ≤ Nat.gcd m n * B'.prod := Nat.mul_le_mul hd2 le_rfl
      omega
    have hNB' : (B'.filter (fun a => 1 < a)).card ≤ (B.filter (fun a => 1 < a)).card := by
      rw [hBf]; omega
    omega
  /- @proof-region region.target-node.session.37d1ce4bb795a99f end -/
