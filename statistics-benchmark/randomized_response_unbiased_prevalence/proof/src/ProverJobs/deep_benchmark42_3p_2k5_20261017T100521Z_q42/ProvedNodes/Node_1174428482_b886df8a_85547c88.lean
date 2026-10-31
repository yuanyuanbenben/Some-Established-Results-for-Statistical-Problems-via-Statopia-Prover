import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q42.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q42.Base

open Msc62GroundTruth

namespace Msc62GroundTruth

set_option autoImplicit false in
theorem statopia_math_node_1174428482_b886df8a : ∀ (n : ℕ) (q : ℝ) (x : Fin n → Bool) (i : Fin n),
    let bit : Bool → ℝ := fun b => if b then (1 : ℝ) else 0
    let reportProb : (Fin n → Bool) → ℝ :=
      fun y => ∏ j : Fin n, if y j = x j then q else 1 - q
    (∑ y : Fin n → Bool, reportProb y * bit (y i)) = (1 - q) + (2 * q - 1) * bit (x i) := by
  /- @proof-region region.target-node.session.7464cf0683522a6a begin -/
  intro n q x i
  dsimp only
  obtain ⟨t, ht⟩ : ∃ t : Fin n → Finset Bool,
      t = fun j => if j = i then ({true} : Finset Bool) else Finset.univ := ⟨_, rfl⟩
  have hmem : ∀ y : Fin n → Bool, y ∈ Fintype.piFinset t ↔ y i = true := by
    intro y
    rw [Fintype.mem_piFinset]
    constructor
    · intro h
      simpa [ht] using h i
    · intro h j
      by_cases hj : j = i
      · subst hj
        simpa [ht] using h
      · simp [ht, hj]
  have hfac_ne : ∀ j : Fin n, j ≠ i → (∑ a ∈ t j, (if a = x j then q else 1 - q)) = 1 := by
    intro j hj
    have htj : t j = Finset.univ := by simp [ht, hj]
    rw [htj]
    cases hx : x j <;> simp [hx] <;> ring
  have key : (∏ j : Fin n, (∑ a ∈ t j, (if a = x j then q else 1 - q)))
      = ∑ y ∈ Fintype.piFinset t, ∏ j : Fin n, (if y j = x j then q else 1 - q) :=
    Finset.prod_univ_sum t (fun j a => (if a = x j then q else 1 - q))
  have hzero : ∀ y ∈ (Finset.univ : Finset (Fin n → Bool)), y ∉ Fintype.piFinset t →
      (∏ j : Fin n, (if y j = x j then q else 1 - q)) * (if y i then (1 : ℝ) else 0) = 0 := by
    intro y _ hy
    have hne : y i ≠ true := fun h => hy ((hmem y).2 h)
    have hfalse : y i = false := by
      cases h : y i
      · rfl
      · exact absurd h hne
    simp [hfalse]
  have hsum1 : (∑ y : Fin n → Bool, (∏ j : Fin n, (if y j = x j then q else 1 - q)) * (if y i then (1 : ℝ) else 0))
      = ∑ y ∈ Fintype.piFinset t,
          (∏ j : Fin n, (if y j = x j then q else 1 - q)) * (if y i then (1 : ℝ) else 0) :=
    (Finset.sum_subset (Finset.subset_univ (s := Fintype.piFinset t)) hzero).symm
  have hsum2 : (∑ y ∈ Fintype.piFinset t,
          (∏ j : Fin n, (if y j = x j then q else 1 - q)) * (if y i then (1 : ℝ) else 0))
      = ∑ y ∈ Fintype.piFinset t, ∏ j : Fin n, (if y j = x j then q else 1 - q) := by
    apply Finset.sum_congr rfl
    intro y hy
    rw [if_pos ((hmem y).1 hy), mul_one]
  have hL : (∏ j : Fin n, (∑ a ∈ t j, (if a = x j then q else 1 - q)))
      = (1 - q) + (2 * q - 1) * (if x i then (1 : ℝ) else 0) := by
    have hsplit := Finset.prod_eq_mul_prod_diff_singleton (s := (Finset.univ : Finset (Fin n)))
      (i := i) (Finset.mem_univ i) (fun j => (∑ a ∈ t j, (if a = x j then q else 1 - q)))
    rw [hsplit]
    have hprod1 : (∏ j ∈ (Finset.univ : Finset (Fin n)) \ {i},
        (∑ a ∈ t j, (if a = x j then q else 1 - q))) = 1 := by
      apply Finset.prod_eq_one
      intro j hj
      exact hfac_ne j (by simpa using hj)
    rw [hprod1, mul_one]
    have hti : (∑ a ∈ t i, (if a = x i then q else 1 - q)) = (if x i then q else 1 - q) := by
      rw [show t i = ({true} : Finset Bool) from by simp [ht], Finset.sum_singleton]
      cases hx : x i <;> simp [hx]
    rw [hti]
    cases hx : x i
    · simp
    · simp
      ring
  rw [hsum1, hsum2, ← key]
  exact hL
  /- @proof-region region.target-node.session.7464cf0683522a6a end -/

end Msc62GroundTruth
