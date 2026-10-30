import ProverJobs.real_imo2026_problem6_acf5714d7c7d.Vocabulary
import ProverJobs.real_imo2026_problem6_acf5714d7c7d.Base
import ProverJobs.real_imo2026_problem6_acf5714d7c7d.ProvedNodes.Node_785998125_3d52cb03_36064cc7
open IMO2026P6

namespace IMO2026P6

set_option autoImplicit false in
theorem statopia_math_node_2415587922_861ebcd7 : ∀ (a : Nat → Nat) (ha : IsValidSeq a),
    ∃ L : Nat, 0 < L ∧ ∀ b : Nat, a 0 ≤ b →
      ((1 < b ∧ ∀ n : Nat, 1 < Nat.gcd b (a n)) ↔
        (1 < b + L ∧ ∀ n : Nat, 1 < Nat.gcd (b + L) (a n))) := by
  /- @proof-region region.target-node.session.71f4595a072089f6 begin -/
  intro a ha
  obtain ⟨F, hFne, hFactual, hFsub, hFcover⟩ :=
    statopia_math_node_785998125_3d52cb03 a ha
  let U : Finset Nat := F.biUnion id
  let L : Nat := U.prod id
  have hmemU : ∀ M ∈ F, M ⊆ U := by
    intro M hM p hp
    change p ∈ F.biUnion id
    rw [Finset.mem_biUnion]
    exact ⟨M, hM, hp⟩
  have hUprime : ∀ p ∈ U, Nat.Prime p := by
    intro p hp
    change p ∈ F.biUnion id at hp
    rw [Finset.mem_biUnion] at hp
    obtain ⟨M, hM, hpM⟩ := hp
    exact (Finset.mem_filter.mp (hFsub M hM hpM)).2
  have hLpos : 0 < L :=
    Finset.prod_pos (fun p hp => (hUprime p hp).pos)
  refine ⟨L, hLpos, fun b hb => ?_⟩
  have hb1 : 1 < b := lt_of_lt_of_le (ha.1 0) hb
  have hbL : 1 < b + L := lt_of_lt_of_le hb1 (Nat.le_add_right b L)
  have hb0 : b ≠ 0 := by omega
  have hbL0 : b + L ≠ 0 := by omega
  have hmem_pf : ∀ {n p : Nat}, n ≠ 0 → (p ∈ n.primeFactors ↔ Nat.Prime p ∧ p ∣ n) := by
    intro n p hn
    rw [Nat.mem_primeFactors]
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hn⟩⟩
  have hchar : ∀ c : Nat, c ≠ 0 →
      ((∀ n, 1 < Nat.gcd c (a n)) ↔ ∀ M ∈ F, (c.primeFactors ∩ M).Nonempty) := by
    intro c hc
    constructor
    · intro h M hM
      obtain ⟨k, hk⟩ := hFactual M hM
      have hg : 1 < Nat.gcd c (a k) := h k
      obtain ⟨p, hpp, hpd⟩ := Nat.exists_prime_and_dvd (ne_of_gt hg)
      have hpc : p ∣ c := dvd_trans hpd (Nat.gcd_dvd_left c (a k))
      have hpa : p ∣ a k := dvd_trans hpd (Nat.gcd_dvd_right c (a k))
      have hak0 : a k ≠ 0 := by have := ha.1 k; omega
      refine ⟨p, ?_⟩
      rw [Finset.mem_inter]
      exact ⟨(hmem_pf hc).mpr ⟨hpp, hpc⟩,
        by rw [hk]; exact (hmem_pf hak0).mpr ⟨hpp, hpa⟩⟩
    · intro h n
      obtain ⟨M, hM, hMsub⟩ := hFcover n
      obtain ⟨p, hp⟩ := h M hM
      rw [Finset.mem_inter] at hp
      obtain ⟨hpc, hpM⟩ := hp
      have hpp : Nat.Prime p := ((hmem_pf hc).mp hpc).1
      have hpd_c : p ∣ c := ((hmem_pf hc).mp hpc).2
      have hpd_a : p ∣ a n := ((hmem_pf (by have := ha.1 n; omega)).mp (hMsub hpM)).2
      have hg : p ∣ Nat.gcd c (a n) := Nat.dvd_gcd hpd_c hpd_a
      have hgpos : 0 < Nat.gcd c (a n) :=
        Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_right c (a n)) (by have := ha.1 n; omega)
      exact lt_of_lt_of_le hpp.one_lt (Nat.le_of_dvd hgpos hg)
  have hpf_iff : ∀ M ∈ F, ∀ p ∈ M, (p ∈ b.primeFactors ↔ p ∈ (b + L).primeFactors) := by
    intro M hM p hpM
    have hpU : p ∈ U := hmemU M hM hpM
    have hpL : p ∣ L := by
      have h := Finset.dvd_prod_of_mem (fun x : Nat => x) hpU
      simpa [L] using h
    have hdvd : p ∣ b ↔ p ∣ b + L := by
      constructor
      · intro h
        exact Nat.dvd_add h hpL
      · intro h
        have hsub : p ∣ (b + L) - L := Nat.dvd_sub h hpL
        simpa using hsub
    rw [hmem_pf (n := b) (p := p) hb0, hmem_pf (n := b + L) (p := p) hbL0]
    exact and_congr Iff.rfl hdvd
  have htrans : (∀ M ∈ F, (b.primeFactors ∩ M).Nonempty) ↔
      (∀ M ∈ F, ((b + L).primeFactors ∩ M).Nonempty) := by
    constructor
    · intro h M hM
      obtain ⟨p, hp⟩ := h M hM
      rw [Finset.mem_inter] at hp
      obtain ⟨hpb, hpM⟩ := hp
      exact ⟨p, by rw [Finset.mem_inter]; exact ⟨(hpf_iff M hM p hpM).mp hpb, hpM⟩⟩
    · intro h M hM
      obtain ⟨p, hp⟩ := h M hM
      rw [Finset.mem_inter] at hp
      obtain ⟨hpbl, hpM⟩ := hp
      exact ⟨p, by rw [Finset.mem_inter]; exact ⟨(hpf_iff M hM p hpM).mpr hpbl, hpM⟩⟩
  have hkey : (∀ n, 1 < Nat.gcd b (a n)) ↔ (∀ n, 1 < Nat.gcd (b + L) (a n)) := by
    rw [hchar b hb0, hchar (b + L) hbL0]
    exact htrans
  exact ⟨fun h => ⟨hbL, hkey.mp h.2⟩, fun h => ⟨hb1, hkey.mpr h.2⟩⟩
  /- @proof-region region.target-node.session.71f4595a072089f6 end -/

end IMO2026P6
