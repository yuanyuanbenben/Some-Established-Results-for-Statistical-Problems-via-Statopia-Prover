import ProverJobs.job_paper_7aa885023a494b54a3d0f82a9b80e7b2.Vocabulary
import ProverJobs.job_paper_7aa885023a494b54a3d0f82a9b80e7b2.Base

open MeasureTheory
open scoped ENNReal BigOperators
open Statlib.Imported

open MeasureTheory
open scoped ENNReal BigOperators
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_763218555_b6110431 : ∀ (n : ℕ) (c θ : ℝ) (s : ℕ) (A : Fin s → Finset (Fin n))
    (hc : 0 < c) (hs : 1 ≤ s)
    (hA_nonempty : ∀ h : Fin s, (A h).Nonempty)
    (hA_disjoint : ∀ h h' : Fin s, h ≠ h' → Disjoint (A h) (A h')),
    partitionEvent n c θ s A =
      {X : Fin n → ℝ |
        ∀ i : Fin n, (X i ∈ Set.Icc (θ - c) (θ + c) ↔ i ∈ Finset.univ.biUnion A)} := by
  /- @proof-region region.target-node.session.a6711ad5845f7cb9 begin -/
  intro n c θ s A hc hs hne hdisj
  ext X
  constructor
  · intro hX
    simp only [partitionEvent, Set.mem_setOf_eq] at hX
    obtain ⟨-, -, -, -, h5⟩ := hX
    intro i
    rw [h5]
    simp [hitSet]
  · intro hX
    simp only [Set.mem_setOf_eq] at hX
    have hhit : hitSet n c θ X = Finset.univ.biUnion A := by
      ext i
      simp only [hitSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hX i
    simp only [partitionEvent, Set.mem_setOf_eq]
    refine ⟨?_, hne, ?_, hdisj, ?_⟩
    · have hcard : (Finset.univ.biUnion A).card = ∑ h : Fin s, (A h).card :=
        Finset.card_biUnion (fun x _ y _ hxy => hdisj x y hxy)
      have hle : s ≤ ∑ h : Fin s, (A h).card := by
        calc s = ∑ _h : Fin s, 1 := by simp
          _ ≤ ∑ h : Fin s, (A h).card :=
            Finset.sum_le_sum (fun h _ => Finset.card_pos.mpr (hne h))
      rw [hhit, hcard]
      exact hle
    · intro h i hi
      rw [hhit]
      exact Finset.mem_biUnion.mpr ⟨h, Finset.mem_univ h, hi⟩
    · exact hhit.symm
  /- @proof-region region.target-node.session.a6711ad5845f7cb9 end -/

end Statlib.Imported
