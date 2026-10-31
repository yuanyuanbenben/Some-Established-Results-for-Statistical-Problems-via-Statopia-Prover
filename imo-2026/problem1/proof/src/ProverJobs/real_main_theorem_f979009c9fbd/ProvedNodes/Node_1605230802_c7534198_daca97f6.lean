import ProverJobs.real_main_theorem_f979009c9fbd.Vocabulary
import ProverJobs.real_main_theorem_f979009c9fbd.Base


set_option autoImplicit false in
theorem statopia_math_node_1605230802_c7534198 : ∀ (B' : Board)
    (hpos : ∀ a ∈ B', 1 ≤ a)
    (hunique : Multiset.card (B'.filter (fun a => 1 < a)) = 1)
    (M : ℕ)
    (hM : 1 < M)
    (hMB : M ∈ B'),
    Mval B' = M := by
  /- @proof-region region.target-node.session.2067214ae0f9fa8e begin -/
  intro B' hpos hunique M hM hMB
  obtain ⟨c, hc⟩ := Multiset.card_eq_one.mp hunique
  have hMmem : M ∈ B'.filter (fun a => 1 < a) :=
    Multiset.mem_filter.mpr ⟨hMB, hM⟩
  have hcM : c = M := by
    rw [hc] at hMmem
    exact (Multiset.mem_singleton.mp hMmem).symm
  have hfilter : B'.filter (fun a => 1 < a) = {M} := by rw [hc, hcM]
  have hother : ∀ b ∈ B', b ≠ M → b = 1 := by
    intro b hb hbne
    have hbpos : 1 ≤ b := hpos b hb
    have hnotlt : ¬ (1 < b) := by
      intro hlt
      have hbmem : b ∈ B'.filter (fun a => 1 < a) :=
        Multiset.mem_filter.mpr ⟨hb, hlt⟩
      rw [hfilter] at hbmem
      exact hbne (Multiset.mem_singleton.mp hbmem)
    omega
  have hcount1 : B'.count M = 1 := by
    have hup : B'.count M ≤ 1 := by
      have heq : (B'.filter (fun a => 1 < a)).count M = B'.count M := by
        rw [Multiset.count_filter]
        simp [hM]
      rw [← heq, hfilter]
      simp
    have hlo : 1 ≤ B'.count M := by
      have hB' : B' = M ::ₘ (B'.erase M) := (Multiset.cons_erase hMB).symm
      rw [hB', Multiset.count_cons_self]
      omega
    omega
  have hprod : B'.prod = M := by
    have hB' : B' = M ::ₘ (B'.erase M) := (Multiset.cons_erase hMB).symm
    have herase : (B'.erase M).prod = 1 := by
      apply Multiset.prod_eq_one
      intro b hb
      have hbB : b ∈ B' := Multiset.mem_of_mem_erase hb
      rcases eq_or_ne b M with hbM | hbne
      · exfalso
        have hzero : (B'.erase M).count M = 0 := by
          have h := hcount1
          rw [hB', Multiset.count_cons_self] at h
          omega
        have hpos : 0 < (B'.erase M).count M := Multiset.count_pos.mpr (hbM ▸ hb)
        omega
      · exact hother b hbB hbne
    rw [hB', Multiset.prod_cons, herase, mul_one]
  have hgExp : ∀ p ∈ M.primeFactors, gExp p B' = M.factorization p := by
    intro p hp
    have hpprime : p.Prime := (Nat.mem_primeFactors.mp hp).1
    have hB'' : B' = M ::ₘ (B'.erase M) := (Multiset.cons_erase hMB).symm
    have hzeros : ∀ x ∈ (B'.erase M).map (fun a => padicValNat p a), x = 0 := by
      intro x hx
      obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.mp hx
      have hbB : b ∈ B' := Multiset.mem_of_mem_erase hb
      have hbne : b ≠ M := by
        intro hbM
        have hzero : (B'.erase M).count M = 0 := by
          have h := hcount1
          rw [hB'', Multiset.count_cons_self] at h
          omega
        have hpos : 0 < (B'.erase M).count M := Multiset.count_pos.mpr (hbM ▸ hb)
        omega
      rw [hother b hbB hbne]
      simp
    have hgcd : gExp p B' = padicValNat p M := by
      unfold gExp
      rw [hB'', Multiset.map_cons, Multiset.gcd_cons]
      have hgen : ∀ s : Multiset ℕ, (∀ x ∈ s, x = 0) → s.gcd = 0 := by
        intro s
        refine Multiset.induction_on s ?_ ?_
        · intro _
          rw [Multiset.gcd_zero]
        · intro a s ih hs
          rw [Multiset.gcd_cons, hs a (Multiset.mem_cons_self a s),
            ih (fun x hx => hs x (Multiset.mem_cons_of_mem hx))]
          simp
      rw [hgen _ hzeros]
      simp
    have hfac : M.factorization p = padicValNat p M := by
      simp [Nat.factorization, hpprime]
    rw [hgcd, hfac]
  have hrecon : ∏ p ∈ M.primeFactors, p ^ M.factorization p = M := by
    simpa only [Finsupp.prod] using Nat.factorization_prod_pow_eq_self (n := M) (by omega)
  unfold Mval
  rw [hprod]
  exact (Finset.prod_congr rfl fun p hp => by rw [hgExp p hp]).trans hrecon
  /- @proof-region region.target-node.session.2067214ae0f9fa8e end -/
