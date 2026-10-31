import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q21.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q21.Base

open Finset
open Msc62GroundTruth

open Finset
namespace Msc62GroundTruth

set_option autoImplicit false in
theorem statopia_math_node_2596964945_1e623ff4 : ∀ {α : Type*} [Fintype α] [DecidableEq α]
    (P : Finset (Finset α)) (g : α → α → ℝ),
    P.sum (fun S => S.sum (fun i => S.sum (fun j => g i j)))
      = ∑ i : α, ∑ j : α,
          g i j * ((P.filter (fun S => i ∈ S ∧ j ∈ S)).card : ℝ) := by
  /- @proof-region region.target-node.session.23355bd1958795c5 begin -/
  intro α _ _ P g
  have hmem : ∀ (S : Finset α) (f : α → ℝ),
      S.sum f = ∑ x : α, (if x ∈ S then f x else 0) := by
    intro S f
    rw [← Finset.sum_filter]
    have h : (Finset.univ.filter (fun x : α => x ∈ S)) = S := by
      ext x
      simp
    rw [h]
  have hS : ∀ S : Finset α,
      S.sum (fun i => S.sum (fun j => g i j))
        = ∑ i : α, ∑ j : α,
            (if i ∈ S then (if j ∈ S then g i j else 0) else 0) := by
    intro S
    rw [hmem S (fun i => S.sum (fun j => g i j))]
    refine Finset.sum_congr rfl ?_
    intro i _
    by_cases hi : i ∈ S
    · simpa [hi] using hmem S (fun j => g i j)
    · simp [hi]
  have hF : ∀ (S : Finset α) (i j : α),
      (if i ∈ S then (if j ∈ S then g i j else 0) else 0)
        = g i j * (if i ∈ S ∧ j ∈ S then (1 : ℝ) else 0) := by
    intro S i j
    by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp [hi, hj]
  have hcard : ∀ i j : α,
      (∑ S ∈ P, (if i ∈ S ∧ j ∈ S then (1 : ℝ) else 0))
        = ((P.filter (fun S => i ∈ S ∧ j ∈ S)).card : ℝ) := by
    intro i j
    rw [← Finset.sum_filter]
    simp
  have hsum : ∀ i j : α,
      (∑ S ∈ P, (if i ∈ S then (if j ∈ S then g i j else 0) else 0))
        = g i j * ((P.filter (fun S => i ∈ S ∧ j ∈ S)).card : ℝ) := by
    intro i j
    have h1 : (∑ S ∈ P, (if i ∈ S then (if j ∈ S then g i j else 0) else 0))
        = ∑ S ∈ P, g i j * (if i ∈ S ∧ j ∈ S then (1 : ℝ) else 0) :=
      Finset.sum_congr rfl (fun S _ => hF S i j)
    rw [h1, ← Finset.mul_sum, hcard i j]
  have hLHS : P.sum (fun S => S.sum (fun i => S.sum (fun j => g i j)))
      = ∑ S ∈ P, ∑ i : α, ∑ j : α,
          (if i ∈ S then (if j ∈ S then g i j else 0) else 0) :=
    Finset.sum_congr rfl (fun S _ => hS S)
  have step1 : (∑ S ∈ P, ∑ i : α, ∑ j : α,
        (if i ∈ S then (if j ∈ S then g i j else 0) else 0))
      = ∑ i : α, ∑ S ∈ P, ∑ j : α,
        (if i ∈ S then (if j ∈ S then g i j else 0) else 0) :=
    Finset.sum_comm
  have step2 : (∑ i : α, ∑ S ∈ P, ∑ j : α,
        (if i ∈ S then (if j ∈ S then g i j else 0) else 0))
      = ∑ i : α, ∑ j : α, ∑ S ∈ P,
        (if i ∈ S then (if j ∈ S then g i j else 0) else 0) :=
    Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
  rw [hLHS, step1, step2]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hsum i j))
  /- @proof-region region.target-node.session.23355bd1958795c5 end -/

end Msc62GroundTruth
