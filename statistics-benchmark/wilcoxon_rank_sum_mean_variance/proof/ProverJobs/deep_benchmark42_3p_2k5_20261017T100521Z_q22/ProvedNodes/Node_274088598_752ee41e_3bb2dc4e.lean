import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q22.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q22.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q22.ProvedNodes.Node_3130791264_39ee0da9_364b2110

open Finset
open Msc62GroundTruth

open Finset
namespace Msc62GroundTruth

set_option autoImplicit false in
theorem statopia_math_node_274088598_752ee41e : ∀ (N m : ℕ) (hN : 2 ≤ N) (hm : 1 ≤ m) (hmN : m ≤ N)
    (r s : Fin N) (hrs : r ≠ s),
    let P : Finset (Finset (Fin N)) := (Finset.univ : Finset (Fin N)).powersetCard m
    ((P.filter (fun A => r ∈ A ∧ s ∈ A)).card : ℝ) * ((N : ℝ) * ((N : ℝ) - 1)) =
      (P.card : ℝ) * ((m : ℝ) * ((m : ℝ) - 1)) := by
  /- @proof-region region.target-node.session.0fad4be16eff3e45 begin -/
  intro N m hN hm hmN r s hrs
  dsimp only
  rcases Nat.lt_or_ge m 2 with hlt | hge
  · have hm1 : m = 1 := by omega
    subst hm1
    have hfilter :
        ((Finset.univ : Finset (Fin N)).powersetCard 1).filter (fun A => r ∈ A ∧ s ∈ A) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      rintro A hA ⟨hrA, hsA⟩
      have hAcard : A.card = 1 := (Finset.mem_powersetCard.mp hA).2
      have hsub : ({r, s} : Finset (Fin N)) ⊆ A := by
        rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨hrA, hsA⟩
      have h2 : ({r, s} : Finset (Fin N)).card ≤ A.card := Finset.card_le_card hsub
      have h2' : ({r, s} : Finset (Fin N)).card = 2 := by simp [hrs]
      rw [h2', hAcard] at h2
      omega
    rw [hfilter]
    simp
  · have hcount : (((Finset.univ : Finset (Fin N)).powersetCard m).filter (fun A => r ∈ A ∧ s ∈ A)).card
        = (N - 2).choose (m - 2) :=
      statopia_math_node_3130791264_39ee0da9 N m hge hmN r s hrs
    have hC : ((Finset.univ : Finset (Fin N)).powersetCard m).card = N.choose m := by
      simp [Finset.card_powersetCard]
    have e1 : N.choose m * m = N * (N - 1).choose (m - 1) := by
      have h := Nat.choose_mul (n := N) (k := m) (s := 1) hm
      simpa [Nat.choose_one_right] using h
    have hsub1 : (N - 1) - 1 = N - 2 := by omega
    have hsub2 : (m - 1) - 1 = m - 2 := by omega
    have e2 : (N - 1).choose (m - 1) * (m - 1) = (N - 1) * (N - 2).choose (m - 2) := by
      have h := Nat.choose_mul (n := N - 1) (k := m - 1) (s := 1) (by omega : 1 ≤ m - 1)
      rw [hsub1, hsub2] at h
      simpa [Nat.choose_one_right] using h
    have hmc : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub hm]
      simp
    have hNc : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ N)]
      simp
    have e1R : (N.choose m : ℝ) * (m : ℝ) = (N : ℝ) * (((N - 1).choose (m - 1) : ℕ) : ℝ) := by
      have h := congrArg (fun x : ℕ => (x : ℝ)) e1
      simpa using h
    have e2R : (((N - 1).choose (m - 1) : ℕ) : ℝ) * ((m : ℝ) - 1)
        = ((N : ℝ) - 1) * (((N - 2).choose (m - 2) : ℕ) : ℝ) := by
      have h := congrArg (fun x : ℕ => (x : ℝ)) e2
      simp only [Nat.cast_mul] at h
      rw [hmc, hNc] at h
      exact h
    have main : (N.choose m : ℝ) * ((m : ℝ) * ((m : ℝ) - 1))
        = ((N : ℝ) * ((N : ℝ) - 1)) * (((N - 2).choose (m - 2) : ℕ) : ℝ) := by
      calc (N.choose m : ℝ) * ((m : ℝ) * ((m : ℝ) - 1))
          = ((N.choose m : ℝ) * (m : ℝ)) * ((m : ℝ) - 1) := by ring
        _ = ((N : ℝ) * (((N - 1).choose (m - 1) : ℕ) : ℝ)) * ((m : ℝ) - 1) := by rw [e1R]
        _ = (N : ℝ) * ((((N - 1).choose (m - 1) : ℕ) : ℝ) * ((m : ℝ) - 1)) := by ring
        _ = (N : ℝ) * (((N : ℝ) - 1) * (((N - 2).choose (m - 2) : ℕ) : ℝ)) := by rw [e2R]
        _ = ((N : ℝ) * ((N : ℝ) - 1)) * (((N - 2).choose (m - 2) : ℕ) : ℝ) := by ring
    rw [hcount, hC]
    calc (((N - 2).choose (m - 2) : ℕ) : ℝ) * ((N : ℝ) * ((N : ℝ) - 1))
        = ((N : ℝ) * ((N : ℝ) - 1)) * (((N - 2).choose (m - 2) : ℕ) : ℝ) := by ring
      _ = (N.choose m : ℝ) * ((m : ℝ) * ((m : ℝ) - 1)) := main.symm
  /- @proof-region region.target-node.session.0fad4be16eff3e45 end -/

end Msc62GroundTruth
