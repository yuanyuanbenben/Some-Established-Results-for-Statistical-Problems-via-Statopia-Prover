import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q22.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q22.Base

open Finset
open Msc62GroundTruth

open Finset
namespace Msc62GroundTruth

set_option autoImplicit false in
theorem statopia_math_node_945440442_dbf9c5cc : ∀ (N m : ℕ) (hm : 1 ≤ m) (hmN : m ≤ N)
    (r : Fin N),
    (((Finset.univ : Finset (Fin N)).powersetCard m).filter (fun A => r ∈ A)).card
      = (N - 1).choose (m - 1) := by
  /- @proof-region region.target-node.session.5357e8392634bf9d begin -/
  intro N m hm hmN r
  have key : ∀ {n : ℕ} {s t : Finset (Fin N)}, s ∈ t.powersetCard n ↔ (s ⊆ t ∧ s.card = n) := by
    intro n s t
    exact (Finset.mem_powersetCard).trans (by tauto)
  have hcarderase : ((Finset.univ : Finset (Fin N)).erase r).card = N - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ r), Finset.card_univ, Fintype.card_fin]
  have hbij : (((Finset.univ : Finset (Fin N)).powersetCard m).filter (fun A => r ∈ A)).card
      = (((Finset.univ : Finset (Fin N)).erase r).powersetCard (m - 1)).card := by
    refine Finset.card_bij (fun A _ => A.erase r) ?_ ?_ ?_
    · intro A hA
      rw [Finset.mem_filter] at hA
      obtain ⟨-, hAcard⟩ := key.mp hA.1
      show A.erase r ∈ (Finset.univ.erase r).powersetCard (m - 1)
      refine key.mpr ⟨?_, ?_⟩
      · intro x hx
        rw [Finset.mem_erase] at hx ⊢
        exact ⟨hx.1, Finset.mem_univ x⟩
      · rw [Finset.card_erase_of_mem hA.2, hAcard]
    · intro A1 hA1 A2 hA2 heq
      rw [Finset.mem_filter] at hA1 hA2
      have heq' : A1.erase r = A2.erase r := heq
      rw [← Finset.insert_erase hA1.2, ← Finset.insert_erase hA2.2, heq']
    · intro B hB
      obtain ⟨hBsub, hBcard⟩ := key.mp hB
      have hrB : r ∉ B := by
        intro h
        have h2 : r ∈ (Finset.univ : Finset (Fin N)).erase r := hBsub h
        rw [Finset.mem_erase] at h2
        exact h2.1 rfl
      refine ⟨insert r B, ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨?_, Finset.mem_insert_self r B⟩
        refine key.mpr ⟨Finset.subset_univ _, ?_⟩
        rw [Finset.card_insert_of_notMem hrB, hBcard, Nat.sub_add_cancel hm]
      · simpa using Finset.erase_insert hrB
  rw [hbij, Finset.card_powersetCard, hcarderase]
  /- @proof-region region.target-node.session.5357e8392634bf9d end -/

end Msc62GroundTruth
