import ProverJobs.real_main_theorem_f979009c9fbd.Vocabulary
import ProverJobs.real_main_theorem_f979009c9fbd.MainSupport
import ProverJobs.real_main_theorem_f979009c9fbd.Base

theorem main_theorem :
    (∀ (B₀ : Board), IsInitial B₀ →
      ¬ ∃ f : ℕ → Board, f 0 = B₀ ∧ ∀ k, Move (f k) (f (k + 1))) ∧
    (∀ (B₀ : Board), IsInitial B₀ →
      ∀ (B' : Board), Reachable B₀ B' → IsTerminal B' → HasUniqueLarge B') ∧
    (∀ (B₀ : Board), IsInitial B₀ →
      ∀ (B₁ B₂ : Board), Reachable B₀ B₁ → Reachable B₀ B₂ →
        IsTerminal B₁ → IsTerminal B₂ →
        ∀ M, (1 < M ∧ M ∈ B₁) ↔ (1 < M ∧ M ∈ B₂)) ∧
    (∀ (B₀ : Board), IsInitial B₀ →
      ∀ (B' : Board), Reachable B₀ B' → IsTerminal B' →
        ∀ (M : ℕ), 1 < M → M ∈ B' → M = Mval B₀) ∧
    (∀ (B₀ : Board), IsInitial B₀ → 1 < Mval B₀)
:= by
  /- @proof-region region.root.c950d752b924 begin -/
  have hprod1_of : ∀ (M : Board), (∀ a ∈ M, 1 ≤ a) → (∀ a ∈ M, a ≤ 1) → M.prod = 1 :=
    fun M => Multiset.induction_on
      (p := fun s => (∀ a ∈ s, 1 ≤ a) → (∀ a ∈ s, a ≤ 1) → s.prod = 1) M
      (fun _ _ => by simp)
      (fun a t ih h1 h2 => by
        have ha : a = 1 := le_antisymm (h2 a (by simp)) (h1 a (by simp))
        have ht1 : t.prod = 1 :=
          ih (fun x hx => h1 x (by simp [hx])) (fun x hx => h2 x (by simp [hx]))
        rw [Multiset.prod_cons, ha, ht1, one_mul])
  have helement : ∀ (B₀ : Board), IsInitial B₀ → ∀ Bx : Board, Reachable B₀ Bx → ∃ a ∈ Bx, 1 < a := by
    intro B₀ hB0 Bx hR
    obtain ⟨hpos, _, hprod⟩ := statopia_math_node_2196151784_b06f43aa B₀ hB0 Bx hR
    by_contra h
    push_neg at h
    have hle : ∀ a ∈ Bx, a ≤ 1 := fun a ha => by have := h a ha; omega
    have h1 := hprod1_of Bx hpos hle
    omega
  have hcard_one : ∀ (B₀ : Board), IsInitial B₀ → ∀ Bx : Board, Reachable B₀ Bx → IsTerminal Bx →
      (Bx.filter (fun a => 1 < a)).card = 1 := by
    intro B₀ hB0 Bx hR hT
    obtain ⟨a, ha, ha1⟩ := helement B₀ hB0 Bx hR
    have hmem : a ∈ Bx.filter (fun a => 1 < a) := by simp [ha, ha1]
    have hge : 1 ≤ (Bx.filter (fun a => 1 < a)).card := by
      have hpos : 0 < (Bx.filter (fun a => 1 < a)).card :=
        Multiset.card_pos_iff_exists_mem.mpr ⟨a, hmem⟩
      omega
    exact le_antisymm hT hge
  have mval_step : ∀ B B' : Board, Move B B' → (∀ a ∈ B, 1 ≤ a) → Mval B' = Mval B := by
    intro B B' hM hpos
    have hsupp := statopia_math_node_1700959973_f12e7196 B B' hM hpos
    unfold Mval
    rw [hsupp]
    apply Finset.prod_congr rfl
    intro p hp
    rw [statopia_math_node_1799194065_328e73c0 B B' hM p (Nat.prime_of_mem_primeFactors hp)]
  have mval_lift : ∀ (B₀ : Board), IsInitial B₀ → ∀ (B' : Board), Reachable B₀ B' → Mval B' = Mval B₀ := by
    intro B₀ hB0 B' hR
    induction hR with
    | refl => rfl
    | tail hR' hM ih =>
      exact (mval_step _ _ hM ((statopia_math_node_2196151784_b06f43aa B₀ hB0 _ hR').1)).trans ih
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro B₀ hB0 hf
    obtain ⟨f, hf0, hfstep⟩ := hf
    have hreach : ∀ k, Reachable B₀ (f k) := by
      intro k
      induction k with
      | zero => rw [hf0]; exact Relation.ReflTransGen.refl
      | succ k ih => exact ih.tail (hfstep k)
    have hposf : ∀ k, ∀ a ∈ f k, 1 ≤ a :=
      fun k => (statopia_math_node_2196151784_b06f43aa B₀ hB0 (f k) (hreach k)).1
    have hdescent : ∀ B B' : Board, Move B B' → (∀ a ∈ B, 1 ≤ a) →
        B'.prod + (B'.filter (fun a => 1 < a)).card < B.prod + (B.filter (fun a => 1 < a)).card := by
      intro B B' hM hpos
      obtain ⟨m, n, s, hm, hn, hB, hB'⟩ := hM
      subst hB
      subst hB'
      have hs_pos : ∀ a ∈ s, 1 ≤ a := fun a ha => hpos a (by simp [ha])
      have hspos : 0 < s.prod :=
        CanonicallyOrderedAdd.multiset_prod_pos.mpr (fun x hx => by have := hs_pos x hx; omega)
      have hsp1 : 1 ≤ s.prod := by omega
      have hdq : Nat.gcd m n * (Nat.lcm m n / Nat.gcd m n) = Nat.lcm m n :=
        Nat.mul_div_cancel' ((Nat.gcd_dvd_left m n).trans (Nat.dvd_lcm_left m n))
      have hml : m * n = Nat.gcd m n * Nat.lcm m n := (Nat.gcd_mul_lcm m n).symm
      have hgcd1 : 1 ≤ Nat.gcd m n := by
        have hne : Nat.gcd m n ≠ 0 := by rintro h; rw [Nat.gcd_eq_zero_iff] at h; omega
        omega
      have hlcm2 : 2 ≤ Nat.lcm m n := by
        have hne : Nat.lcm m n ≠ 0 := by rintro h; rw [Nat.lcm_eq_zero_iff] at h; omega
        have hle : m ≤ Nat.lcm m n := Nat.le_of_dvd (by omega) (Nat.dvd_lcm_left m n)
        omega
      have hBprod : (m ::ₘ n ::ₘ s).prod = Nat.gcd m n * (Nat.lcm m n * s.prod) := by
        rw [Multiset.prod_cons, Multiset.prod_cons, ← mul_assoc, hml, mul_assoc]
      have hB'prod : (Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s).prod = Nat.lcm m n * s.prod := by
        rw [Multiset.prod_cons, Multiset.prod_cons, ← mul_assoc, hdq]
      have hB'prod1 : 1 ≤ Nat.lcm m n * s.prod := by
        have h1 : 1 ≤ Nat.lcm m n := by omega
        have := Nat.mul_le_mul h1 hsp1
        simpa using this
      have hcardB : ((m ::ₘ n ::ₘ s).filter (fun a => 1 < a)).card = (s.filter (fun a => 1 < a)).card + 2 := by
        rw [Multiset.filter_cons_of_pos (n ::ₘ s) hm, Multiset.filter_cons_of_pos s hn, Multiset.card_cons, Multiset.card_cons]
      have hcardB' : ((Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s).filter (fun a => 1 < a)).card
          ≤ (s.filter (fun a => 1 < a)).card + 2 := by
        by_cases hd : 1 < Nat.gcd m n
        · rw [Multiset.filter_cons_of_pos ((Nat.lcm m n / Nat.gcd m n) ::ₘ s) hd]
          by_cases hq : 1 < Nat.lcm m n / Nat.gcd m n
          · rw [Multiset.filter_cons_of_pos s hq, Multiset.card_cons, Multiset.card_cons]
          · rw [Multiset.filter_cons_of_neg s hq, Multiset.card_cons]
            show (Multiset.filter (fun a => 1 < a) s).card + 1 ≤ (Multiset.filter (fun a => 1 < a) s).card + 2
            omega
        · rw [Multiset.filter_cons_of_neg ((Nat.lcm m n / Nat.gcd m n) ::ₘ s) hd]
          by_cases hq : 1 < Nat.lcm m n / Nat.gcd m n
          · rw [Multiset.filter_cons_of_pos s hq, Multiset.card_cons]
            show (Multiset.filter (fun a => 1 < a) s).card + 1 ≤ (Multiset.filter (fun a => 1 < a) s).card + 2
            omega
          · rw [Multiset.filter_cons_of_neg s hq]
            show (Multiset.filter (fun a => 1 < a) s).card ≤ (Multiset.filter (fun a => 1 < a) s).card + 2
            omega
      by_cases hgd : Nat.gcd m n = 1
      · have hqeq : Nat.lcm m n / Nat.gcd m n = Nat.lcm m n := by rw [hgd, Nat.div_one]
        have hqgt : 1 < Nat.lcm m n / Nat.gcd m n := by rw [hqeq]; omega
        have hdnot : ¬ 1 < Nat.gcd m n := by omega
        have hc : ((Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s).filter (fun a => 1 < a)).card
            = (s.filter (fun a => 1 < a)).card + 1 := by
          rw [Multiset.filter_cons_of_neg ((Nat.lcm m n / Nat.gcd m n) ::ₘ s) hdnot, Multiset.filter_cons_of_pos s hqgt, Multiset.card_cons]
        have hpeq : (Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s).prod = (m ::ₘ n ::ₘ s).prod := by
          rw [hB'prod, hBprod, hgd, one_mul]
        rw [hpeq, hc, hcardB]
        omega
      · have hgd2 : 2 ≤ Nat.gcd m n := by omega
        have hprod_ge : (Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s).prod + 1
            ≤ (m ::ₘ n ::ₘ s).prod := by
          rw [hB'prod, hBprod]
          nlinarith [hB'prod1, hgd2]
        omega
    have hdec : ∀ k, (f (k + 1)).prod + ((f (k + 1)).filter (fun a => 1 < a)).card
        < (f k).prod + ((f k).filter (fun a => 1 < a)).card :=
      fun k => hdescent (f k) (f (k + 1)) (hfstep k) (hposf k)
    have hbound : ∀ k, ((f k).prod + ((f k).filter (fun a => 1 < a)).card) + k
        ≤ (f 0).prod + ((f 0).filter (fun a => 1 < a)).card := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have := hdec k
        omega
    have := hbound (((f 0).prod + ((f 0).filter (fun a => 1 < a)).card) + 1)
    omega
  · intro B₀ hB0 B' hR hT
    exact hcard_one B₀ hB0 B' hR hT
  · intro B₀ hB0 B₁ B₂ hR1 hR2 hT1 hT2 M
    have key : ∀ Bx : Board, Reachable B₀ Bx → IsTerminal Bx → ((1 < M ∧ M ∈ Bx) ↔ M = Mval B₀) := by
      intro Bx hRx hTx
      constructor
      · intro ⟨hM1, hMB1⟩
        obtain ⟨hposx, _, _⟩ := statopia_math_node_2196151784_b06f43aa B₀ hB0 Bx hRx
        have huniqx := hcard_one B₀ hB0 Bx hRx hTx
        have hev := statopia_math_node_1605230802_c7534198 Bx hposx huniqx M hM1 hMB1
        exact hev.symm.trans (mval_lift B₀ hB0 Bx hRx)
      · intro hMeq
        obtain ⟨hposx, _, _⟩ := statopia_math_node_2196151784_b06f43aa B₀ hB0 Bx hRx
        have huniqx := hcard_one B₀ hB0 Bx hRx hTx
        obtain ⟨a, haBx, ha1⟩ := helement B₀ hB0 Bx hRx
        have haeq : a = Mval B₀ := by
          have hev := statopia_math_node_1605230802_c7534198 Bx hposx huniqx a ha1 haBx
          exact hev.symm.trans (mval_lift B₀ hB0 Bx hRx)
        rw [hMeq]
        exact ⟨haeq ▸ ha1, haeq ▸ haBx⟩
    constructor
    · intro h
      exact (key B₂ hR2 hT2).mpr ((key B₁ hR1 hT1).mp h)
    · intro h
      exact (key B₁ hR1 hT1).mpr ((key B₂ hR2 hT2).mp h)
  · intro B₀ hB0 B' hR hT M hM hMB
    obtain ⟨hpos, _, _⟩ := statopia_math_node_2196151784_b06f43aa B₀ hB0 B' hR
    have huniq := hcard_one B₀ hB0 B' hR hT
    have hev := statopia_math_node_1605230802_c7534198 B' hpos huniq M hM hMB
    exact hev.symm.trans (mval_lift B₀ hB0 B' hR)
  · intro B₀ hB0
    have hpos0 : ∀ a ∈ B₀, 1 ≤ a := fun a ha => le_of_lt (hB0.2 a ha)
    obtain ⟨B', hR, hT⟩ := statopia_math_node_2804265859_24cd4c8c B₀ hpos0
    obtain ⟨a, ha, ha1⟩ := helement B₀ hB0 B' hR
    obtain ⟨hpos', _, _⟩ := statopia_math_node_2196151784_b06f43aa B₀ hB0 B' hR
    have huniq := hcard_one B₀ hB0 B' hR hT
    have hev := statopia_math_node_1605230802_c7534198 B' hpos' huniq a ha1 ha
    have hval : Mval B₀ = a := (mval_lift B₀ hB0 B' hR).symm.trans hev
    rw [hval]
    exact ha1
  /- @proof-region region.root.c950d752b924 end -/
