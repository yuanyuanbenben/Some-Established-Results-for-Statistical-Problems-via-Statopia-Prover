import ProverJobs.real_main_theorem_edd06e2c7e6c.Vocabulary
import ProverJobs.real_main_theorem_edd06e2c7e6c.Base
import ProverJobs.real_main_theorem_edd06e2c7e6c.ProvedNodes.Node_1231998112_26c8ceab_5b4097d6
import ProverJobs.real_main_theorem_edd06e2c7e6c.ProvedNodes.Node_2246720384_db986540_9bc93e2b
import ProverJobs.real_main_theorem_edd06e2c7e6c.ProvedNodes.Node_230051687_03829abe_7482e2dd
import ProverJobs.real_main_theorem_edd06e2c7e6c.ProvedNodes.Node_3776635361_5eaf0306_47c63d95





set_option autoImplicit false in
theorem statopia_math_node_2027774880_d06a152e : ∀ (a : ℕ → ℕ) (ha : IsValidSeq a),
    let S : ℕ → Prop := fun x => 0 < x ∧ ∀ i : ℕ, 1 < Nat.gcd x (a i)
    let M : Set ℕ := {m : ℕ | S m ∧ ∀ d : ℕ, d ∣ m → d < m → ¬ S d}
    let P : Set ℕ := {p : ℕ | Nat.Prime p ∧ ∃ m ∈ M, p ∣ m}
    ∀ (hP : P.Finite), let L : ℕ := ∏ p ∈ hP.toFinset, p
      0 < L ∧ (∀ m ∈ M, m ∣ L) ∧ M.Finite := by
  /- @proof-region region.target-node.session.30affe6169381495 begin -/
  classical
  intro a ha
  let S : ℕ → Prop := fun x => 0 < x ∧ ∀ i : ℕ, 1 < Nat.gcd x (a i)
  let M : Set ℕ := {m : ℕ | S m ∧ ∀ d : ℕ, d ∣ m → d < m → ¬ S d}
  let P : Set ℕ := {p : ℕ | Nat.Prime p ∧ ∃ m ∈ M, p ∣ m}
  show ∀ (hP : P.Finite), let L : ℕ := ∏ p ∈ hP.toFinset, p
      0 < L ∧ (∀ m ∈ M, m ∣ L) ∧ M.Finite
  intro hP
  let L : ℕ := ∏ p ∈ hP.toFinset, p
  show 0 < L ∧ (∀ m ∈ M, m ∣ L) ∧ M.Finite
  have hmem : ∀ q : ℕ, q ∈ hP.toFinset ↔ q ∈ P := by
    intro q
    have hcoe := Set.Finite.coe_toFinset hP
    constructor
    · intro hq
      rw [← hcoe]
      exact hq
    · intro hq
      rw [← hcoe] at hq
      exact hq
  have hLne : L ≠ 0 := by
    show (∏ p ∈ hP.toFinset, p) ≠ 0
    rw [Finset.prod_ne_zero_iff]
    intro q hq
    have hqP : q ∈ P := (hmem q).1 hq
    have hqprime : Nat.Prime q := hqP.1
    have hq2 : 2 ≤ q := hqprime.two_le
    omega
  have hLpos : 0 < L := Nat.pos_of_ne_zero hLne
  have hmsq : ∀ m ∈ M, ∀ p : ℕ, Nat.Prime p → ¬ p * p ∣ m :=
    statopia_math_node_230051687_03829abe a ha
  have hMdiv : ∀ m ∈ M, m ∣ L := by
    intro m hmM
    have hsq : Squarefree m :=
      Nat.squarefree_iff_prime_squarefree.mpr (hmsq m hmM)
    have hprod : ∏ p ∈ m.primeFactors, p = m :=
      Nat.prod_primeFactors_of_squarefree hsq
    rw [← hprod]
    refine Finset.prod_dvd_prod_of_subset m.primeFactors hP.toFinset (fun p => p) ?_
    intro p hp
    have hpprime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hpdvd : p ∣ m := Nat.dvd_of_mem_primeFactors hp
    refine (hmem p).2 ?_
    exact ⟨hpprime, m, hmM, hpdvd⟩
  refine ⟨hLpos, hMdiv, ?_⟩
  have hdivfin : ({d : ℕ | d ∣ L}).Finite := by
    refine Set.Finite.subset (s := ↑(Finset.range (L + 1))) ?_ ?_
    · exact (Finset.range (L + 1)).finite_toSet
    · intro d hd
      have hdle : d ≤ L := Nat.le_of_dvd hLpos hd
      simp only [Finset.coe_range, Set.mem_Iio]
      omega
  exact hdivfin.subset (fun m hm => hMdiv m hm)
  /- @proof-region region.target-node.session.30affe6169381495 end -/
