import ProverJobs.real_main_theorem_f979009c9fbd.Vocabulary
import ProverJobs.real_main_theorem_f979009c9fbd.Base
import ProverJobs.real_main_theorem_f979009c9fbd.ProvedNodes.Node_3256552224_5ffbc5d4_c887b752
import ProverJobs.real_main_theorem_f979009c9fbd.ProvedNodes.Node_571599843_c7abf9a7_16b1ea46

set_option autoImplicit false in
theorem statopia_math_node_2196151784_b06f43aa : ∀ (B0 : Board) (hB0 : IsInitial B0)
    (Bp : Board) (hReach : Reachable B0 Bp),
    (∀ a ∈ Bp, 1 ≤ a) ∧ Bp.card = 2026 ∧ 1 < Bp.prod := by
  /- @proof-region region.target-node.session.837e01106009f284 begin -/
  intro B0 hB0 Bp hReach
  have key1 : ∀ (s : Board), (∀ a ∈ s, 1 ≤ a) → 1 ≤ s.prod := by
    intro s
    refine Multiset.induction_on s ?_ ?_
    · intro _
      simp
    · intro a t ih h
      rw [Multiset.prod_cons]
      calc (1 : ℕ) = 1 * 1 := (Nat.mul_one 1).symm
        _ ≤ a * t.prod := Nat.mul_le_mul (h a (by simp)) (ih (fun x hx => h x (by simp [hx])))
  have key2 : ∀ (s : Board), s.card = 2026 → (∀ a ∈ s, 1 < a) → 1 < s.prod := by
    intro s
    refine Multiset.induction_on s ?_ ?_
    · intro hc _
      exact absurd hc (by simp)
    · intro a t _ _ h
      rw [Multiset.prod_cons]
      have ha : 2 ≤ a := by have := h a (by simp); omega
      have ht : 1 ≤ t.prod := key1 t (fun x hx => le_of_lt (h x (by simp [hx])))
      calc (1 : ℕ) < 2 := by norm_num
        _ = 2 * 1 := (Nat.mul_one 2).symm
        _ ≤ a * t.prod := Nat.mul_le_mul ha ht
  unfold Reachable at hReach
  induction hReach with
  | refl =>
    exact ⟨fun a ha => le_of_lt (hB0.2 a ha), hB0.1, key2 B0 hB0.1 hB0.2⟩
  | tail _ hMove ih =>
    rcases ih with ⟨ihpos, ihcard, _⟩
    obtain ⟨hcpos, hccard⟩ :=
      statopia_math_node_3256552224_5ffbc5d4 _ _ hMove ihpos
    rcases hMove with ⟨m, n, s, hm, hn, hb, hc⟩
    obtain ⟨_, _, _, hc_prod, _, _⟩ :=
      statopia_math_node_571599843_c7abf9a7 _ _ m n s hm hn hb hc
    have hsprod : 1 ≤ s.prod := key1 s (fun a ha => ihpos a (by rw [hb]; simp [ha]))
    have h2lcm : 2 ≤ Nat.lcm m n := by
      have hmlcm : m ≤ Nat.lcm m n :=
        Nat.le_of_dvd (Nat.lcm_pos (by omega) (by omega)) (Nat.dvd_lcm_left m n)
      omega
    refine ⟨hcpos, hccard.trans ihcard, ?_⟩
    rw [hc_prod]
    calc (1 : ℕ) < 2 := by norm_num
      _ ≤ Nat.lcm m n := h2lcm
      _ = Nat.lcm m n * 1 := (Nat.mul_one _).symm
      _ ≤ Nat.lcm m n * s.prod := Nat.mul_le_mul (le_refl _) hsprod
  /- @proof-region region.target-node.session.837e01106009f284 end -/
