import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q02.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q02.Base

open MeasureTheory ProbabilityTheory

open MeasureTheory ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_488559670_a6d524b3 : ∀ (n : ℕ) (hn : 1 ≤ n) (y : Fin n → ℝ),
    (2 * (n : ℝ) ^ 2)⁻¹ * (∑ j : Fin n, ∑ l : Fin n, (y j - y l) ^ 2)
      = (n : ℝ)⁻¹ * (∑ j : Fin n, (y j - ((n : ℝ)⁻¹ * ∑ i : Fin n, y i)) ^ 2) := by
  /- @proof-region region.target-node.session.e12b9c97e91a892b begin -/
  intro n hn y
  have hn0 : (n : ℝ) ≠ 0 := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  let c : ℝ := (n : ℝ)⁻¹ * ∑ i : Fin n, y i
  have hcn : (n : ℝ) * c = ∑ i : Fin n, y i := by
    show (n : ℝ) * ((n : ℝ)⁻¹ * ∑ i : Fin n, y i) = ∑ i : Fin n, y i
    rw [← mul_assoc, mul_inv_cancel₀ hn0, one_mul]
  have hzero : ∑ j : Fin n, (y j - c) = 0 := by
    rw [Finset.sum_sub_distrib]
    have h2 : ∑ j : Fin n, c = (n : ℝ) * c := by
      simp [Finset.sum_const, nsmul_eq_mul]
    rw [h2, hcn]
    simp
  have hcross : ∀ j : Fin n, ∑ l : Fin n, 2 * ((y j - c) * (y l - c)) = 0 := by
    intro j
    have h1 : ∑ l : Fin n, 2 * ((y j - c) * (y l - c))
        = 2 * (y j - c) * ∑ l : Fin n, (y l - c) := by
      simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [h1, hzero, mul_zero]
  have hinner : ∀ j : Fin n,
      ∑ l : Fin n, ((y j - c) ^ 2 + (y l - c) ^ 2 - 2 * ((y j - c) * (y l - c)))
        = (n : ℝ) * (y j - c) ^ 2 + ∑ l : Fin n, (y l - c) ^ 2 := by
    intro j
    have h2 : ∑ l : Fin n, (y j - c) ^ 2 = (n : ℝ) * (y j - c) ^ 2 := by
      simp [Finset.sum_const, nsmul_eq_mul]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hcross j, h2]
    ring
  have hA : ∑ j : Fin n, (n : ℝ) * (y j - c) ^ 2 = (n : ℝ) * ∑ j : Fin n, (y j - c) ^ 2 := by
    simp [Finset.mul_sum]
  have hB : ∑ j : Fin n, (∑ l : Fin n, (y l - c) ^ 2) = (n : ℝ) * ∑ j : Fin n, (y j - c) ^ 2 := by
    simp [Finset.sum_const, nsmul_eq_mul]
  have hdbl : ∑ j : Fin n, ∑ l : Fin n, (y j - y l) ^ 2
      = 2 * (n : ℝ) * ∑ j : Fin n, (y j - c) ^ 2 := by
    have h1 : ∑ j : Fin n, ∑ l : Fin n, (y j - y l) ^ 2
        = ∑ j : Fin n, ∑ l : Fin n,
            ((y j - c) ^ 2 + (y l - c) ^ 2 - 2 * ((y j - c) * (y l - c))) := by
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
    have h2 : ∑ j : Fin n, ∑ l : Fin n,
          ((y j - c) ^ 2 + (y l - c) ^ 2 - 2 * ((y j - c) * (y l - c)))
        = ∑ j : Fin n, ((n : ℝ) * (y j - c) ^ 2 + ∑ l : Fin n, (y l - c) ^ 2) := by
      exact Finset.sum_congr rfl fun j _ => hinner j
    have h3 : ∑ j : Fin n, ((n : ℝ) * (y j - c) ^ 2 + ∑ l : Fin n, (y l - c) ^ 2)
        = ∑ j : Fin n, ((n : ℝ) * (y j - c) ^ 2)
          + ∑ j : Fin n, (∑ l : Fin n, (y l - c) ^ 2) := by
      simp [Finset.sum_add_distrib]
    rw [h1, h2, h3, hA, hB]
    ring
  have key : (2 * (n : ℝ) ^ 2)⁻¹ * (2 * (n : ℝ) * (∑ j : Fin n, (y j - c) ^ 2))
      = (n : ℝ)⁻¹ * ∑ j : Fin n, (y j - c) ^ 2 := by
    have hcoef : (2 * (n : ℝ) ^ 2)⁻¹ * (2 * (n : ℝ)) = (n : ℝ)⁻¹ := by
      have h2n : (2 * (n : ℝ)) ≠ 0 := mul_ne_zero two_ne_zero hn0
      rw [show (2 * (n : ℝ) ^ 2) = (2 * (n : ℝ)) * (n : ℝ) by ring]
      rw [mul_inv_rev, mul_assoc, inv_mul_cancel₀ h2n, mul_one]
    rw [← mul_assoc, hcoef]
  rw [hdbl]
  exact key
  /- @proof-region region.target-node.session.e12b9c97e91a892b end -/
