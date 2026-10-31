import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q42.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q42.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q42.ProvedNodes.Node_1174428482_b886df8a_85547c88

open Msc62GroundTruth

namespace Msc62GroundTruth

set_option autoImplicit false in
theorem statopia_math_node_3416877917_94a68e1c : ∀ (n : ℕ) (hn : 1 ≤ n) (q : ℝ) (x : Fin n → Bool),
    let bit : Bool → ℝ := fun b => if b then (1 : ℝ) else 0
    let prevalence : ℝ := (1 / (n : ℝ)) * ∑ i : Fin n, bit (x i)
    let reportProb : (Fin n → Bool) → ℝ :=
      fun y => ∏ i : Fin n, if y i = x i then q else 1 - q
    let reportedMean : (Fin n → Bool) → ℝ :=
      fun y => (1 / (n : ℝ)) * ∑ i : Fin n, bit (y i)
    (∑ y : Fin n → Bool, reportProb y * reportedMean y)
      = (1 - q) + (2 * q - 1) * prevalence := by
  /- @proof-region region.target-node.session.04fca4450e227c49 begin -/
  intro n hn q x
  show (∑ y : Fin n → Bool, (∏ i : Fin n, (if y i = x i then q else 1 - q)) *
      ((1 / (n : ℝ)) * ∑ i : Fin n, (if y i then (1 : ℝ) else 0)))
    = (1 - q) + (2 * q - 1) * ((1 / (n : ℝ)) * ∑ i : Fin n, (if x i then (1 : ℝ) else 0))
  have h1n : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hdep : ∀ i : Fin n,
      (∑ y : Fin n → Bool, (∏ j : Fin n, (if y j = x j then q else 1 - q)) * (if y i then (1 : ℝ) else 0))
        = (1 - q) + (2 * q - 1) * (if x i then (1 : ℝ) else 0) := by
    intro i
    exact statopia_math_node_1174428482_b886df8a n q x i
  have hstep : ∀ y : Fin n → Bool,
      (∏ i : Fin n, (if y i = x i then q else 1 - q)) * ((1 / (n : ℝ)) * ∑ i : Fin n, (if y i then (1 : ℝ) else 0))
        = ∑ i : Fin n, (1 / (n : ℝ)) * ((∏ j : Fin n, (if y j = x j then q else 1 - q)) * (if y i then (1 : ℝ) else 0)) := by
    intro y
    have hS : (∏ i : Fin n, (if y i = x i then q else 1 - q)) * (∑ i : Fin n, (if y i then (1 : ℝ) else 0))
        = ∑ i : Fin n, (∏ j : Fin n, (if y j = x j then q else 1 - q)) * (if y i then (1 : ℝ) else 0) := by
      rw [Finset.mul_sum]
    calc (∏ i : Fin n, (if y i = x i then q else 1 - q)) * ((1 / (n : ℝ)) * ∑ i : Fin n, (if y i then (1 : ℝ) else 0))
        = (1 / (n : ℝ)) * ((∏ i : Fin n, (if y i = x i then q else 1 - q)) * (∑ i : Fin n, (if y i then (1 : ℝ) else 0))) := by ring
      _ = (1 / (n : ℝ)) * ∑ i : Fin n, (∏ j : Fin n, (if y j = x j then q else 1 - q)) * (if y i then (1 : ℝ) else 0) := by rw [hS]
      _ = ∑ i : Fin n, (1 / (n : ℝ)) * ((∏ j : Fin n, (if y j = x j then q else 1 - q)) * (if y i then (1 : ℝ) else 0)) := by rw [Finset.mul_sum]
  have hcard : (∑ _i : Fin n, (1 : ℝ)) = (n : ℝ) := by simp
  have hconst : (∑ _i : Fin n, (1 - q)) = (n : ℝ) * (1 - q) := by
    rw [← hcard, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hsplit : (∑ i : Fin n, ((1 - q) + (2 * q - 1) * (if x i then (1 : ℝ) else 0)))
      = (n : ℝ) * (1 - q) + (2 * q - 1) * ∑ i : Fin n, (if x i then (1 : ℝ) else 0) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hconst]
  have hcancel : (1 / (n : ℝ)) * (n : ℝ) = 1 := by
    rw [one_div, inv_mul_cancel₀ hn0]
  calc (∑ y : Fin n → Bool, (∏ i : Fin n, (if y i = x i then q else 1 - q)) *
        ((1 / (n : ℝ)) * ∑ i : Fin n, (if y i then (1 : ℝ) else 0)))
      = ∑ y : Fin n → Bool, ∑ i : Fin n, (1 / (n : ℝ)) * ((∏ j : Fin n, (if y j = x j then q else 1 - q)) * (if y i then (1 : ℝ) else 0)) := Finset.sum_congr rfl (fun y _ => hstep y)
    _ = ∑ i : Fin n, ∑ y : Fin n → Bool, (1 / (n : ℝ)) * ((∏ j : Fin n, (if y j = x j then q else 1 - q)) * (if y i then (1 : ℝ) else 0)) := Finset.sum_comm
    _ = ∑ i : Fin n, (1 / (n : ℝ)) * ∑ y : Fin n → Bool, (∏ j : Fin n, (if y j = x j then q else 1 - q)) * (if y i then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
    _ = ∑ i : Fin n, (1 / (n : ℝ)) * ((1 - q) + (2 * q - 1) * (if x i then (1 : ℝ) else 0)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hdep i]
    _ = (1 / (n : ℝ)) * ∑ i : Fin n, ((1 - q) + (2 * q - 1) * (if x i then (1 : ℝ) else 0)) := by
        rw [Finset.mul_sum]
    _ = (1 - q) + (2 * q - 1) * ((1 / (n : ℝ)) * ∑ i : Fin n, (if x i then (1 : ℝ) else 0)) := by
        rw [hsplit]
        calc (1 / (n : ℝ)) * ((n : ℝ) * (1 - q) + (2 * q - 1) * ∑ i : Fin n, (if x i then (1 : ℝ) else 0))
            = ((1 / (n : ℝ)) * (n : ℝ)) * (1 - q) + (2 * q - 1) * ((1 / (n : ℝ)) * ∑ i : Fin n, (if x i then (1 : ℝ) else 0)) := by ring
          _ = (1 - q) + (2 * q - 1) * ((1 / (n : ℝ)) * ∑ i : Fin n, (if x i then (1 : ℝ) else 0)) := by
              rw [hcancel]
              ring
  /- @proof-region region.target-node.session.04fca4450e227c49 end -/

end Msc62GroundTruth
