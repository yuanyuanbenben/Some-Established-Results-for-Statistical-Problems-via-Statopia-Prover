import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q38.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q38.Base

open MeasureTheory ProbabilityTheory
open scoped BigOperators

open MeasureTheory ProbabilityTheory
open scoped BigOperators

set_option autoImplicit false in
theorem statopia_math_node_1006963914_bdbc5482 : ∀ (n : ℕ) (hn : 1 ≤ n) (x : Fin n → ℝ) (mu : ℝ),
    let xbar : ℝ := (n : ℝ)⁻¹ * ∑ i : Fin n, x i
    let y : Fin n → ℝ := fun i => x i - mu
    let ybar : ℝ := (n : ℝ)⁻¹ * ∑ i : Fin n, y i
    (∑ i : Fin n, (x i - xbar) ^ 2 = ∑ i : Fin n, x i ^ 2 - (n : ℝ) * xbar ^ 2) ∧
      (∑ i : Fin n, x i ^ 2 - (n : ℝ) * xbar ^ 2 =
        ∑ i : Fin n, ∑ j : Fin n,
          ((if i = j then (1 : ℝ) else 0) - (n : ℝ)⁻¹) * x i * x j) ∧
      (∀ i : Fin n, x i - xbar = y i - ybar) ∧
      (∑ i : Fin n, (x i - xbar) ^ 2 =
        ∑ i : Fin n, ∑ j : Fin n,
          ((if i = j then (1 : ℝ) else 0) - (n : ℝ)⁻¹) * y i * y j) := by
  /- @proof-region region.target-node.session.550047e62576a882 begin -/
  intro n hn x mu
  dsimp only
  have hn0 : (n : ℝ) ≠ 0 := by
    have hn' : n ≠ 0 := by omega
    exact_mod_cast hn'
  have hfin : ∀ S : ℝ, (n : ℝ) * ((n : ℝ)⁻¹ * S) ^ 2 = (n : ℝ)⁻¹ * (S * S) := by
    intro S
    have hc : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hn0
    calc (n : ℝ) * ((n : ℝ)⁻¹ * S) ^ 2
        = ((n : ℝ) * (n : ℝ)⁻¹) * ((n : ℝ)⁻¹ * (S * S)) := by ring
      _ = 1 * ((n : ℝ)⁻¹ * (S * S)) := by rw [hc]
      _ = (n : ℝ)⁻¹ * (S * S) := by ring
  have hkey : ∀ z : Fin n → ℝ,
      ∑ i : Fin n, z i ^ 2 - (n : ℝ) * ((n : ℝ)⁻¹ * ∑ k : Fin n, z k) ^ 2
        = ∑ i : Fin n, ∑ j : Fin n,
            ((if i = j then (1 : ℝ) else 0) - (n : ℝ)⁻¹) * z i * z j := by
    intro z
    have hinner : ∀ i : Fin n,
        (∑ j : Fin n, ((if i = j then (1 : ℝ) else 0) - (n : ℝ)⁻¹) * z i * z j)
          = z i ^ 2 - (n : ℝ)⁻¹ * (z i * ∑ k : Fin n, z k) := by
      intro i
      have e1 : (∑ j : Fin n, ((if i = j then (1 : ℝ) else 0) - (n : ℝ)⁻¹) * z i * z j)
          = ∑ j : Fin n,
              (((if i = j then (1 : ℝ) else 0) * z i * z j) - ((n : ℝ)⁻¹ * (z i * z j))) := by
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [e1, Finset.sum_sub_distrib]
      have e2 : (∑ j : Fin n, (if i = j then (1 : ℝ) else 0) * z i * z j) = z i ^ 2 := by
        rw [Finset.sum_eq_single i]
        · rw [if_pos rfl]
          ring
        · intro j _ hj
          simp [Ne.symm hj]
        · intro h
          exact absurd (Finset.mem_univ i) h
      have e3 : (∑ j : Fin n, (n : ℝ)⁻¹ * (z i * z j))
          = (n : ℝ)⁻¹ * (z i * ∑ k : Fin n, z k) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]
      rw [e2, e3]
    have hsum : (∑ i : Fin n, (z i ^ 2 - (n : ℝ)⁻¹ * (z i * ∑ k : Fin n, z k)))
        = ∑ i : Fin n, z i ^ 2
            - (n : ℝ)⁻¹ * ((∑ i : Fin n, z i) * (∑ i : Fin n, z i)) := by
      have hX : (∑ i : Fin n, (n : ℝ)⁻¹ * (z i * ∑ k : Fin n, z k))
          = (n : ℝ)⁻¹ * ((∑ i : Fin n, z i) * (∑ i : Fin n, z i)) := by
        rw [← Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_sub_distrib, hX]
    calc ∑ i : Fin n, z i ^ 2 - (n : ℝ) * ((n : ℝ)⁻¹ * ∑ k : Fin n, z k) ^ 2
        = ∑ i : Fin n, z i ^ 2
            - (n : ℝ)⁻¹ * ((∑ k : Fin n, z k) * (∑ k : Fin n, z k)) := by
          rw [hfin (∑ k : Fin n, z k)]
      _ = ∑ i : Fin n, (z i ^ 2 - (n : ℝ)⁻¹ * (z i * ∑ k : Fin n, z k)) := hsum.symm
      _ = ∑ i : Fin n, ∑ j : Fin n,
            ((if i = j then (1 : ℝ) else 0) - (n : ℝ)⁻¹) * z i * z j := by
          apply Finset.sum_congr rfl
          intro i _
          exact (hinner i).symm
  have hsq : ∀ z : Fin n → ℝ,
      ∑ i : Fin n, (z i - (n : ℝ)⁻¹ * ∑ k : Fin n, z k) ^ 2
        = ∑ i : Fin n, z i ^ 2 - (n : ℝ) * ((n : ℝ)⁻¹ * ∑ k : Fin n, z k) ^ 2 := by
    intro z
    have hexp : (∑ i : Fin n, (z i - (n : ℝ)⁻¹ * ∑ k : Fin n, z k) ^ 2)
        = ∑ i : Fin n, (z i ^ 2 - 2 * ((n : ℝ)⁻¹ * ∑ k : Fin n, z k) * z i
            + ((n : ℝ)⁻¹ * ∑ k : Fin n, z k) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have hlin : (∑ i : Fin n, 2 * ((n : ℝ)⁻¹ * ∑ k : Fin n, z k) * z i)
        = 2 * ((n : ℝ)⁻¹ * ∑ k : Fin n, z k) * (∑ i : Fin n, z i) := by
      rw [← Finset.mul_sum]
    have hconst : (∑ i : Fin n, ((n : ℝ)⁻¹ * ∑ k : Fin n, z k) ^ 2)
        = (n : ℝ) * ((n : ℝ)⁻¹ * ∑ k : Fin n, z k) ^ 2 := by
      simp [Finset.sum_const, nsmul_eq_mul]
    rw [hlin, hconst]
    have hst : 2 * ((n : ℝ)⁻¹ * (∑ k : Fin n, z k)) * (∑ i : Fin n, z i)
        = 2 * ((n : ℝ) * ((n : ℝ)⁻¹ * (∑ k : Fin n, z k)) ^ 2) := by
      rw [hfin (∑ k : Fin n, z k)]
      ring
    rw [hst]
    ring
  have hybar : (n : ℝ)⁻¹ * ∑ i : Fin n, (x i - mu) = (n : ℝ)⁻¹ * ∑ i : Fin n, x i - mu := by
    have h1 : ∑ i : Fin n, (x i - mu) = (∑ i : Fin n, x i) - (n : ℝ) * mu := by
      rw [Finset.sum_sub_distrib]
      have hm : (∑ i : Fin n, mu) = (n : ℝ) * mu := by
        simp [Finset.sum_const, nsmul_eq_mul]
      rw [hm]
    have h2 : (n : ℝ)⁻¹ * ((n : ℝ) * mu) = mu := by
      rw [← mul_assoc, inv_mul_cancel₀ hn0, one_mul]
    rw [h1, mul_sub, h2]
  refine ⟨hsq x, hkey x, ?_, ?_⟩
  · intro i
    rw [hybar]
    ring
  · have hcongr : (∑ i : Fin n, (x i - (n : ℝ)⁻¹ * ∑ k : Fin n, x k) ^ 2)
        = ∑ i : Fin n, ((x i - mu) - (n : ℝ)⁻¹ * ∑ k : Fin n, (x k - mu)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hybar]
      ring
    calc ∑ i : Fin n, (x i - (n : ℝ)⁻¹ * ∑ k : Fin n, x k) ^ 2
        = ∑ i : Fin n, ((x i - mu) - (n : ℝ)⁻¹ * ∑ k : Fin n, (x k - mu)) ^ 2 := hcongr
      _ = ∑ i : Fin n, (x i - mu) ^ 2
            - (n : ℝ) * ((n : ℝ)⁻¹ * ∑ k : Fin n, (x k - mu)) ^ 2 := hsq (fun i => x i - mu)
      _ = ∑ i : Fin n, ∑ j : Fin n,
            ((if i = j then (1 : ℝ) else 0) - (n : ℝ)⁻¹) * (x i - mu) * (x j - mu) :=
          hkey (fun i => x i - mu)
  /- @proof-region region.target-node.session.550047e62576a882 end -/
