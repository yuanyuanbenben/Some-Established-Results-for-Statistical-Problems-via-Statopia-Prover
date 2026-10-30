import ProverJobs.real_imo2026_problem6_acf5714d7c7d.Vocabulary
import ProverJobs.real_imo2026_problem6_acf5714d7c7d.Base
import ProverJobs.real_imo2026_problem6_acf5714d7c7d.ProvedNodes.Node_202768106_72663a92_6d8b7395
open IMO2026P6

namespace IMO2026P6

set_option autoImplicit false in
theorem statopia_math_node_785998125_3d52cb03 : ∀ (a : Nat → Nat) (ha : IsValidSeq a),
    ∃ F : Finset (Finset Nat),
      F.Nonempty ∧
      (∀ M ∈ F, ∃ k : Nat, M = (a k).primeFactors) ∧
      (∀ M ∈ F, M ⊆ (Finset.range (a 0 + 1)).filter Nat.Prime) ∧
      (∀ n : Nat, ∃ M ∈ F, M ⊆ (a n).primeFactors) := by
  /- @proof-region region.target-node.session.89b378ea128d895e begin -/
  intro a ha
  classical
  let P : Finset Nat := (Finset.range (a 0 + 1)).filter Nat.Prime
  let F : Finset (Finset Nat) := P.powerset.filter (fun M => ∃ k : Nat, M = (a k).primeFactors)
  have hpos : ∀ n : Nat, a n ≠ 0 := by
    intro n h
    have := ha.1 n
    omega
  have hmemF : ∀ k : Nat, (∀ p : Nat, Nat.Prime p → p ∣ a k → p ≤ a 0) →
      (a k).primeFactors ∈ F := by
    intro k hk
    have hsub : (a k).primeFactors ⊆ P := by
      intro p hp
      rw [Nat.mem_primeFactors] at hp
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hk p hp.1 hp.2.1)), hp.1⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsub, ⟨k, rfl⟩⟩
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · obtain ⟨k, _, hk2⟩ := statopia_math_node_202768106_72663a92 a ha 0
    exact ⟨(a k).primeFactors, hmemF k hk2⟩
  · intro M hM
    exact (Finset.mem_filter.mp hM).2
  · intro M hM
    exact Finset.mem_powerset.mp (Finset.mem_filter.mp hM).1
  · intro n
    obtain ⟨k, hk1, hk2⟩ := statopia_math_node_202768106_72663a92 a ha n
    refine ⟨(a k).primeFactors, hmemF k hk2, ?_⟩
    intro p hp
    rw [Nat.mem_primeFactors] at hp
    rw [Nat.mem_primeFactors]
    exact ⟨hp.1, hk1 p hp.1 hp.2.1, hpos n⟩
  /- @proof-region region.target-node.session.89b378ea128d895e end -/

end IMO2026P6
