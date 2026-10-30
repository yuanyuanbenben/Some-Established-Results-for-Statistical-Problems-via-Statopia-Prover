import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q22.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q22.Base

open Finset
open Msc62GroundTruth

open Finset
namespace Msc62GroundTruth

set_option autoImplicit false in
theorem statopia_math_node_1775715242_093567d1 : ∀ (α : Type) (Q : Finset α) (c : ℕ) (hc : c = Q.card) (hc0 : c ≠ 0)
    (g : α → ℝ),
    (1 / (c : ℝ)) * ∑ x ∈ Q, (g x - (1 / (c : ℝ)) * ∑ y ∈ Q, g y) ^ 2
      = (1 / (c : ℝ)) * ∑ x ∈ Q, (g x) ^ 2
          - ((1 / (c : ℝ)) * ∑ x ∈ Q, g x) ^ 2 := by
  /- @proof-region region.target-node.session.9e97c5668754cfea begin -/
  intro α Q c hc hc0 g
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc0
  have hcardR : (Q.card : ℝ) = (c : ℝ) := by rw [hc]
  generalize hμdef : (1 / (c : ℝ)) * ∑ y ∈ Q, g y = μ
  have hS : ∑ x ∈ Q, g x = (c : ℝ) * μ := by
    rw [← hμdef]
    field_simp
  have hsq : ∑ x ∈ Q, (g x - μ) ^ 2 = (∑ x ∈ Q, (g x) ^ 2) - (c : ℝ) * μ ^ 2 := by
    have h1 : ∀ x ∈ Q, (g x - μ) ^ 2 = (g x) ^ 2 - 2 * μ * g x + μ ^ 2 := by
      intro x _
      ring
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have h2 : ∑ x ∈ Q, μ ^ 2 = (Q.card : ℝ) * μ ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have h3 : ∑ x ∈ Q, 2 * μ * g x = 2 * μ * (∑ x ∈ Q, g x) := by
      rw [Finset.mul_sum]
    rw [h2, hcardR, h3, hS]
    ring
  have hcc : (1 / (c : ℝ)) * ((c : ℝ) * μ ^ 2) = μ ^ 2 := by
    field_simp
  rw [hsq, mul_sub, hcc]
  /- @proof-region region.target-node.session.9e97c5668754cfea end -/

end Msc62GroundTruth
