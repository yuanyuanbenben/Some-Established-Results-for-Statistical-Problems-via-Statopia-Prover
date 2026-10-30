import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q22.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q22.Base

open Finset
open Msc62GroundTruth

open Finset
namespace Msc62GroundTruth

set_option autoImplicit false in
theorem statopia_math_node_3704713494_2c790cca : ∀ (N : ℕ) (hN : 1 ≤ N),
    let f : Fin N → ℝ := fun r => ((r.val + 1 : ℕ) : ℝ);
    (∑ r : Fin N, f r) = (N : ℝ) * ((N : ℝ) + 1) / 2 ∧
      (∑ r : Fin N, (f r) ^ 2) =
        (N : ℝ) * ((N : ℝ) + 1) * (2 * (N : ℝ) + 1) / 6 := by
  /- @proof-region region.target-node.session.a9530a8a93c82936 begin -/
  intro N hN
  dsimp only
  have h1 : ∀ n : ℕ,
      (∑ i ∈ Finset.range n, ((i : ℝ) + 1)) = (n : ℝ) * ((n : ℝ) + 1) / 2 := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  have h2 : ∀ n : ℕ,
      (∑ i ∈ Finset.range n, ((i : ℝ) + 1) ^ 2) =
        (n : ℝ) * ((n : ℝ) + 1) * (2 * (n : ℝ) + 1) / 6 := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  have step1 : (∑ r : Fin N, ((r.val + 1 : ℕ) : ℝ)) =
      ∑ i ∈ Finset.range N, ((i : ℝ) + 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ((i + 1 : ℕ) : ℝ))]
    exact Finset.sum_congr rfl fun i _ => by push_cast; ring
  have step2 : (∑ r : Fin N, ((r.val + 1 : ℕ) : ℝ) ^ 2) =
      ∑ i ∈ Finset.range N, ((i : ℝ) + 1) ^ 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ((i + 1 : ℕ) : ℝ) ^ 2)]
    exact Finset.sum_congr rfl fun i _ => by push_cast; ring
  exact ⟨by rw [step1]; exact h1 N, by rw [step2]; exact h2 N⟩
  /- @proof-region region.target-node.session.a9530a8a93c82936 end -/

end Msc62GroundTruth
