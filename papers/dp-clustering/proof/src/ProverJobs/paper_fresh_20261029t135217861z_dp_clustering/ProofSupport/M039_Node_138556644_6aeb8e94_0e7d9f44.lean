import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.Definitions
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M031_Vocabulary
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M032_Base

/- Original module ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.ProvedNodes.Node_138556644_6aeb8e94_0e7d9f44; genuine source relocated, namespace-isolated only. -/
namespace DPCompletedProof
open _root_.Statlib.Imported

open MeasureTheory
open Statlib.Imported

noncomputable section
open MeasureTheory
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_138556644_6aeb8e94 : ∀ (t ε δ β : ℝ) (n : ℕ) (π : ℝ → ℝ)
    (hn : 2 ≤ n) (hdelta : 0 < δ)
    (hA : ∀ α ∈ Set.Ioo (0 : ℝ) ε, δ⁻¹ * α ^ β ≤ π α),
    ∀ α ∈ Set.Ioo (0 : ℝ) ε,
      (δ⁻¹ / ((n - 1).factorial : ℝ)) *
          (α ^ (t + β - 1) * Real.exp (-(1 + Real.log (n : ℝ)) * α))
        ≤ α ^ t / risingFac α n * π α := by
  /- @proof-region region.target-node.session.02024d4366e8a97c begin -/
  intro t ε δ β n π hn hdelta hA α hα
  obtain ⟨hα0, hαε⟩ := hα
  have hnpos : (0 : ℕ) < n := by omega
  have hH : (∑ k ∈ Finset.range (n - 1), (1 : ℝ) / ((k : ℝ) + 1)) ≤ 1 + Real.log (n : ℝ) := by
    have key : ∀ m : ℕ, 1 ≤ m →
        (∑ k ∈ Finset.range m, (1 : ℝ) / ((k : ℝ) + 1)) ≤ 1 + Real.log (m : ℝ) := by
      intro m
      induction m with
      | zero =>
        intro h
        omega
      | succ m ih =>
        intro hm
        rcases Nat.eq_zero_or_pos m with hm0 | hmpos
        · subst hm0
          norm_num [Finset.sum_range_succ]
        · have hstep : (1 : ℝ) / ((m : ℝ) + 1) ≤
              Real.log ((m : ℝ) + 1) - Real.log (m : ℝ) := by
            have hm0' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
            have hmn : ((m : ℝ) + 1) ≠ 0 := by linarith
            have hdiv : Real.log ((m : ℝ) / ((m : ℝ) + 1)) ≤
                ((m : ℝ) / ((m : ℝ) + 1)) - 1 :=
              Real.log_le_sub_one_of_pos (x := (m : ℝ) / ((m : ℝ) + 1))
                (div_pos hm0' (by linarith))
            rw [Real.log_div hm0'.ne' hmn] at hdiv
            have hsub : (m : ℝ) / ((m : ℝ) + 1) - 1 = -((1 : ℝ) / ((m : ℝ) + 1)) := by
              field_simp
              ring
            rw [hsub] at hdiv
            linarith
          have hprev := ih hmpos
          rw [Finset.sum_range_succ]
          push_cast
          linarith
    have hn2 : 1 ≤ n - 1 := by omega
    have h1 := key (n - 1) hn2
    have hlog : Real.log (((n - 1 : ℕ) : ℝ)) ≤ Real.log (n : ℝ) := by
      apply Real.log_le_log
      · have hpos : (0 : ℕ) < n - 1 := by omega
        exact_mod_cast hpos
      · have hle : n - 1 ≤ n := by omega
        exact_mod_cast hle
    linarith
  have hbound : risingFac α n ≤ α * ((n - 1).factorial : ℝ) * Real.exp ((1 + Real.log (n : ℝ)) * α) := by
    have hfac : (∏ k ∈ Finset.range (n - 1), ((k : ℝ) + 1)) = ((n - 1).factorial : ℝ) := by
      rw [Nat.factorial_eq_prod_range_add_one]
      push_cast
      rfl
    have hsplit : (∏ k ∈ Finset.range (n - 1), (α + ((k : ℝ) + 1)))
        = (∏ k ∈ Finset.range (n - 1), ((k : ℝ) + 1)) *
          (∏ k ∈ Finset.range (n - 1), (1 + α / ((k : ℝ) + 1))) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro k hk
      have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring
    have hB : (∏ k ∈ Finset.range (n - 1), (1 + α / ((k : ℝ) + 1))) ≤
        Real.exp ((1 + Real.log (n : ℝ)) * α) := by
      have hstep1 : (∏ k ∈ Finset.range (n - 1), (1 + α / ((k : ℝ) + 1))) ≤
          ∏ k ∈ Finset.range (n - 1), Real.exp (α / ((k : ℝ) + 1)) := by
        apply Finset.prod_le_prod
        · intro k hk
          have hk1 : (0 : ℝ) ≤ ((k : ℝ) + 1) := by positivity
          have hd : 0 ≤ α / ((k : ℝ) + 1) := div_nonneg hα0.le hk1
          linarith
        · intro k hk
          simpa [add_comm] using Real.add_one_le_exp (α / ((k : ℝ) + 1))
      have hstep2 : (∏ k ∈ Finset.range (n - 1), Real.exp (α / ((k : ℝ) + 1))) =
          Real.exp (α * (∑ k ∈ Finset.range (n - 1), (1 : ℝ) / ((k : ℝ) + 1))) := by
        rw [← Real.exp_sum]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        simp only [div_eq_mul_inv, one_mul]
      rw [hstep2] at hstep1
      refine le_trans hstep1 ?_
      apply Real.exp_le_exp_of_le
      calc α * (∑ k ∈ Finset.range (n - 1), (1 : ℝ) / ((k : ℝ) + 1))
          ≤ α * (1 + Real.log (n : ℝ)) := mul_le_mul_of_nonneg_left hH hα0.le
        _ = (1 + Real.log (n : ℝ)) * α := by ring
    have h1 : risingFac α n = (∏ k ∈ Finset.range (n - 1), (α + ((k : ℝ) + 1))) * α := by
      unfold risingFac
      have hn_eq : n = (n - 1) + 1 := by omega
      rw [hn_eq, Finset.prod_range_succ']
      push_cast
      ring
    have hFnn : (0 : ℝ) ≤ ((n - 1).factorial : ℝ) := by positivity
    have hstep : ((n - 1).factorial : ℝ) *
          (∏ k ∈ Finset.range (n - 1), (1 + α / ((k : ℝ) + 1))) * α
        ≤ α * ((n - 1).factorial : ℝ) * Real.exp ((1 + Real.log (n : ℝ)) * α) := by
      have h2 : ((n - 1).factorial : ℝ) *
            (∏ k ∈ Finset.range (n - 1), (1 + α / ((k : ℝ) + 1)))
          ≤ ((n - 1).factorial : ℝ) * Real.exp ((1 + Real.log (n : ℝ)) * α) :=
        mul_le_mul_of_nonneg_left hB hFnn
      calc ((n - 1).factorial : ℝ) *
            (∏ k ∈ Finset.range (n - 1), (1 + α / ((k : ℝ) + 1))) * α
          ≤ ((n - 1).factorial : ℝ) * Real.exp ((1 + Real.log (n : ℝ)) * α) * α :=
              mul_le_mul_of_nonneg_right h2 hα0.le
        _ = α * ((n - 1).factorial : ℝ) * Real.exp ((1 + Real.log (n : ℝ)) * α) := by ring
    rw [h1, hsplit, hfac]
    exact hstep
  have hRpos : 0 < risingFac α n := by
    unfold risingFac
    apply Finset.prod_pos
    intro k hk
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
    linarith
  have hA' : δ⁻¹ * α ^ β ≤ π α := hA α ⟨hα0, hαε⟩
  have hFpos : 0 < ((n - 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (n - 1)
  have hFne : ((n - 1).factorial : ℝ) ≠ 0 := hFpos.ne'
  have hEpos : 0 < Real.exp ((1 + Real.log (n : ℝ)) * α) := Real.exp_pos _
  have hEne : Real.exp ((1 + Real.log (n : ℝ)) * α) ≠ 0 := hEpos.ne'
  have hαFE : 0 < α * ((n - 1).factorial : ℝ) * Real.exp ((1 + Real.log (n : ℝ)) * α) :=
    mul_pos (mul_pos hα0 hFpos) hEpos
  have hPpos : 0 < δ⁻¹ * α ^ (t + β) := by
    have h1 : 0 < δ⁻¹ := by positivity
    have h2 : 0 < α ^ (t + β) := Real.rpow_pos_of_pos hα0 (t + β)
    exact mul_pos h1 h2
  have hrpow : α ^ (t + β) = α ^ (t + β - 1) * α := by
    have h := Real.rpow_add hα0 (t + β - 1) 1
    rw [Real.rpow_one] at h
    have h1 : t + β - 1 + 1 = t + β := by ring
    rw [h1] at h
    exact h
  calc (δ⁻¹ / ((n - 1).factorial : ℝ)) *
        (α ^ (t + β - 1) * Real.exp (-(1 + Real.log (n : ℝ)) * α))
      = (δ⁻¹ * α ^ (t + β - 1)) /
          (((n - 1).factorial : ℝ) * Real.exp ((1 + Real.log (n : ℝ)) * α)) := by
          rw [neg_mul, Real.exp_neg]
          field_simp
    _ = (δ⁻¹ * α ^ (t + β)) /
          (α * ((n - 1).factorial : ℝ) * Real.exp ((1 + Real.log (n : ℝ)) * α)) := by
          rw [hrpow]
          field_simp
    _ ≤ (δ⁻¹ * α ^ (t + β)) / risingFac α n := by
          rw [div_le_div_iff₀ hαFE hRpos]
          exact mul_le_mul_of_nonneg_left hbound hPpos.le
    _ ≤ (α ^ t * π α) / risingFac α n := by
          rw [div_le_div_iff_of_pos_right hRpos]
          calc δ⁻¹ * α ^ (t + β) = α ^ t * (δ⁻¹ * α ^ β) := by
                rw [Real.rpow_add hα0 t β]; ring
            _ ≤ α ^ t * π α :=
                mul_le_mul_of_nonneg_left hA' (Real.rpow_pos_of_pos hα0 t).le
    _ = α ^ t / risingFac α n * π α := by
          ring_nf
  /- @proof-region region.target-node.session.02024d4366e8a97c end -/

end Statlib.Imported
end
end DPCompletedProof
