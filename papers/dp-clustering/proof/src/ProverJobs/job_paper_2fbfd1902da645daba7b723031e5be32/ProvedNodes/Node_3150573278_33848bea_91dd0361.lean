import ProverJobs.job_paper_2fbfd1902da645daba7b723031e5be32.Vocabulary
import ProverJobs.job_paper_2fbfd1902da645daba7b723031e5be32.Base

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators
open Statlib.Imported

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_3150573278_33848bea : ∀ (t : ℕ) (sigma : ℕ → Fin t)
    (hpos : ∀ i : ℕ, 1 ≤ (sigma i).val),
    ∃ (s' : Fin t) (phi : ℕ → ℕ),
      StrictMono phi ∧
      (∀ n : ℕ, sigma (phi n) = s') ∧
      (∀ B : ℕ, {n : ℕ | phi n < B}.Finite) ∧
      1 ≤ s'.val ∧ s'.val < t := by
  /- @proof-region region.target-node.session.c76aa1c17bb20385 begin -/
  intro t sigma hpos
  obtain ⟨s', hs'⟩ := Finite.exists_infinite_fiber sigma
  let p : ℕ → Prop := fun i => sigma i = s'
  have hset : (setOf p).Infinite := Set.infinite_coe_iff.mp hs'
  have hmono : StrictMono (Nat.nth p) := Nat.nth_strictMono hset
  have hconst : ∀ n : ℕ, sigma (Nat.nth p n) = s' := fun n => Nat.nth_mem_of_infinite hset n
  have hle : ∀ n : ℕ, n ≤ Nat.nth p n := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ k ih => exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (hmono (Nat.lt_succ_self k)))
  have hfin : ∀ B : ℕ, {n : ℕ | Nat.nth p n < B}.Finite := by
    intro B
    exact (Set.finite_lt_nat B).subset (fun n hn => lt_of_le_of_lt (hle n) hn)
  have hpos' : 1 ≤ s'.val := by
    have h := hpos (Nat.nth p 0)
    rwa [hconst 0] at h
  exact ⟨s', Nat.nth p, hmono, hconst, hfin, hpos', s'.isLt⟩
  /- @proof-region region.target-node.session.c76aa1c17bb20385 end -/

end Statlib.Imported
