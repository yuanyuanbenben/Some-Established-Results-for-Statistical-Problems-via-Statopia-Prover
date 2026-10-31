import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q22.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q22.Base

open Finset
open Msc62GroundTruth

open Finset
namespace Msc62GroundTruth

set_option autoImplicit false in
theorem statopia_math_node_3130791264_39ee0da9 : ∀ (N m : ℕ) (hm : 2 ≤ m) (hmN : m ≤ N)
    (r s : Fin N) (hrs : r ≠ s),
    (((Finset.univ : Finset (Fin N)).powersetCard m).filter
        (fun A => r ∈ A ∧ s ∈ A)).card = (N - 2).choose (m - 2) := by
  /- @proof-region region.target-node.session.75c3aaf117535365 begin -/
  intro N m hm hmN r s hrs
  have hUcard : (((Finset.univ : Finset (Fin N)).erase r).erase s).card = N - 2 := by
    have hs_in : s ∈ (Finset.univ : Finset (Fin N)).erase r :=
      Finset.mem_erase.mpr ⟨hrs.symm, Finset.mem_univ s⟩
    have hUc : (Finset.univ : Finset (Fin N)).card = N := by simp
    rw [Finset.card_erase_of_mem hs_in, Finset.card_erase_of_mem (Finset.mem_univ r), hUc]
    omega
  have hcard :
      (((Finset.univ : Finset (Fin N)).powersetCard m).filter (fun A => r ∈ A ∧ s ∈ A)).card
        = ((((Finset.univ : Finset (Fin N)).erase r).erase s).powersetCard (m - 2)).card := by
    apply Finset.card_bij (i := fun A _ => (A.erase r).erase s)
    · intro A hA
      show (A.erase r).erase s ∈ (((Finset.univ : Finset (Fin N)).erase r).erase s).powersetCard (m - 2)
      obtain ⟨hApow, hrA, hsA⟩ := Finset.mem_filter.mp hA
      obtain ⟨-, hAcard⟩ := Finset.mem_powersetCard.mp hApow
      rw [Finset.mem_powersetCard]
      refine ⟨?_, ?_⟩
      · intro x hx
        exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hx).1,
          Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1, Finset.mem_univ x⟩⟩
      · have hsm : s ∈ A.erase r := Finset.mem_erase.mpr ⟨hrs.symm, hsA⟩
        rw [Finset.card_erase_of_mem hsm, Finset.card_erase_of_mem hrA, hAcard]
        omega
    · intro A1 hA1 A2 hA2 heq
      have heq' : (A1.erase r).erase s = (A2.erase r).erase s := heq
      obtain ⟨hA1pow, hr1, hs1⟩ := Finset.mem_filter.mp hA1
      obtain ⟨hA2pow, hr2, hs2⟩ := Finset.mem_filter.mp hA2
      have hs1' : s ∈ A1.erase r := Finset.mem_erase.mpr ⟨hrs.symm, hs1⟩
      have hs2' : s ∈ A2.erase r := Finset.mem_erase.mpr ⟨hrs.symm, hs2⟩
      calc A1 = insert r (insert s ((A1.erase r).erase s)) := by
              rw [Finset.insert_erase hs1', Finset.insert_erase hr1]
        _ = insert r (insert s ((A2.erase r).erase s)) := by rw [heq']
        _ = A2 := by rw [Finset.insert_erase hs2', Finset.insert_erase hr2]
    · intro B hB
      obtain ⟨hBsub, hBcard⟩ := Finset.mem_powersetCard.mp hB
      have hrB : r ∉ B := by
        intro h
        exact (Finset.mem_erase.mp (Finset.mem_erase.mp (hBsub h)).2).1 rfl
      have hsB : s ∉ B := by
        intro h
        exact (Finset.mem_erase.mp (hBsub h)).1 rfl
      have hr_notin : r ∉ insert s B := by
        rw [Finset.mem_insert, not_or]; exact ⟨hrs, hrB⟩
      refine ⟨insert r (insert s B), ?_, ?_⟩
      · rw [Finset.mem_filter, Finset.mem_powersetCard]
        refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
        · intro x _; exact Finset.mem_univ x
        · rw [Finset.card_insert_of_notMem hr_notin, Finset.card_insert_of_notMem hsB, hBcard]
          omega
        · exact Finset.mem_insert_self r _
        · exact Finset.mem_insert_of_mem (Finset.mem_insert_self s B)
      · show ((insert r (insert s B)).erase r).erase s = B
        rw [Finset.erase_insert hr_notin, Finset.erase_insert hsB]
  rw [hcard, Finset.card_powersetCard, hUcard]
  /- @proof-region region.target-node.session.75c3aaf117535365 end -/

end Msc62GroundTruth
