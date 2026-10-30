import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q21.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q21.Base

open Finset
open Msc62GroundTruth

open Finset
namespace Msc62GroundTruth

set_option autoImplicit false in
theorem statopia_math_node_1343175658_819cdf6e : ∀ {α : Type*} [DecidableEq α]
    (s : Finset α) (i : α) (hi : i ∈ s)
    (D : Finset α) (hD : D ⊆ s.erase i)
    (k : ℕ) (hk : 1 ≤ k),
    ((s.powersetCard k).filter (fun S => i ∈ S ∧ S ∩ D = ∅)).card
      = ((s.erase i) \ D).card.choose (k - 1) := by
  /- @proof-region region.target-node.session.4413ca330d33088f begin -/
  classical
  intro α _ s i hi D hD k hk
  have hiD : i ∉ D := by
    intro h
    have h' := hD h
    rw [Finset.mem_erase] at h'
    exact h'.1 rfl
  have key : ((s.powersetCard k).filter (fun S => i ∈ S ∧ S ∩ D = ∅)).card
      = ((s.erase i \ D).powersetCard (k - 1)).card := by
    refine Finset.card_bij (fun S _ => S.erase i) ?_ ?_ ?_
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_powersetCard] at hS
      obtain ⟨⟨hSs, hScard⟩, hiS, hdisj⟩ := hS
      simp only [Finset.mem_powersetCard]
      refine ⟨?_, ?_⟩
      · intro x hx
        rw [Finset.mem_erase] at hx
        rw [Finset.mem_sdiff, Finset.mem_erase]
        refine ⟨⟨hx.1, hSs hx.2⟩, ?_⟩
        intro hxD
        have hmem : x ∈ S ∩ D := Finset.mem_inter.mpr ⟨hx.2, hxD⟩
        rw [hdisj] at hmem
        exact absurd hmem (by simp)
      · rw [Finset.card_erase_of_mem hiS, hScard]
    · intro S hS S' hS' heq
      simp only [Finset.mem_filter, Finset.mem_powersetCard] at hS hS'
      have heq' : S.erase i = S'.erase i := heq
      rw [← Finset.insert_erase hS.2.1, ← Finset.insert_erase hS'.2.1, heq']
    · intro X hX
      rw [Finset.mem_powersetCard] at hX
      obtain ⟨hXsub, hXcard⟩ := hX
      have hiX : i ∉ X := by
        intro h
        have h' := hXsub h
        rw [Finset.mem_sdiff, Finset.mem_erase] at h'
        exact h'.1.1 rfl
      have hsub : insert i X ⊆ s := by
        intro x hx
        rw [Finset.mem_insert] at hx
        rcases hx with rfl | hx
        · exact hi
        · have h' := hXsub hx
          rw [Finset.mem_sdiff, Finset.mem_erase] at h'
          exact h'.1.2
      have hcard : (insert i X).card = k := by
        rw [Finset.card_insert_of_notMem hiX, hXcard]
        exact Nat.sub_add_cancel hk
      have hdisjX : insert i X ∩ D = ∅ := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hx, hxD⟩
          · exact absurd hxD hiD
          · have h' := hXsub hx
            rw [Finset.mem_sdiff] at h'
            exact absurd hxD h'.2
        · intro h
          exact absurd h (by simp)
      have hmem : insert i X ∈ (s.powersetCard k).filter (fun S => i ∈ S ∧ S ∩ D = ∅) := by
        rw [Finset.mem_filter, Finset.mem_powersetCard]
        exact ⟨⟨hsub, hcard⟩, Finset.mem_insert.mpr (Or.inl rfl), hdisjX⟩
      exact ⟨insert i X, hmem, Finset.erase_insert hiX⟩
  rw [key, Finset.card_powersetCard]
  /- @proof-region region.target-node.session.4413ca330d33088f end -/

end Msc62GroundTruth
