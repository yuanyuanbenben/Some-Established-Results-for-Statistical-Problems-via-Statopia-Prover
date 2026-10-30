import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q20.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q20.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q20.ProvedNodes.Node_4171527340_5abf08e7_cb6a2334
open MeasureTheory ProbabilityTheory
open scoped BigOperators

open MeasureTheory ProbabilityTheory
open scoped BigOperators

set_option autoImplicit false in
theorem statopia_math_node_4239247027_57d53a0d : ∀ (rho : NNReal) (r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1),
    Integrable (fun k : ℕ => r ^ k) (poissonMeasure rho) ∧
      ∫ k : ℕ, r ^ k ∂(poissonMeasure rho) =
        Real.exp ((rho : ℝ) * (r - 1)) := by
  /- @proof-region region.target-node.session.e2b1e077df77b68b begin -/
  intro rho r hr0 hr1
  haveI : IsProbabilityMeasure (poissonMeasure rho) :=
    PMF.toMeasure.isProbabilityMeasure (poissonPMF rho)
  have hint : Integrable (fun k : ℕ => r ^ k) (poissonMeasure rho) := by
    refine MeasureTheory.Integrable.of_bound ?_ 1 (Filter.Eventually.of_forall ?_)
    · fun_prop
    · intro k
      rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg hr0]
      exact pow_le_one₀ hr0 hr1
  refine ⟨hint, ?_⟩
  have hInt : ∫ k : ℕ, r ^ k ∂(poissonMeasure rho) =
      ∑' k : ℕ, (poissonPMF rho k).toReal * r ^ k := by
    have h := PMF.integral_eq_tsum (poissonPMF rho) (fun k : ℕ => r ^ k) hint
    rw [show poissonMeasure rho = (poissonPMF rho).toMeasure from rfl, h]
    refine tsum_congr fun k => ?_
    simp only [smul_eq_mul]
  have hsum : ∑' k : ℕ, (poissonPMF rho k).toReal * r ^ k =
      Real.exp ((rho : ℝ) * (r - 1)) := by
    have htoReal : ∀ k : ℕ, (poissonPMF rho k).toReal = poissonPMFReal rho k := by
      intro k
      exact ENNReal.toReal_ofReal poissonPMFReal_nonneg
    have hbody : ∀ k : ℕ, poissonPMFReal rho k =
        Real.exp (-(rho : ℝ)) * (rho : ℝ) ^ k / (Nat.factorial k : ℝ) := by
      intro k
      simp only [poissonPMFReal]
      try ring_nf
    calc ∑' k : ℕ, (poissonPMF rho k).toReal * r ^ k
        = ∑' k : ℕ, (Real.exp (-(rho : ℝ)) * (rho : ℝ) ^ k / (Nat.factorial k : ℝ)) * r ^ k := by
          refine tsum_congr fun k => ?_
          rw [htoReal k, hbody k]
      _ = ∑' k : ℕ, Real.exp (-(rho : ℝ)) * (((rho : ℝ) * r) ^ k / (Nat.factorial k : ℝ)) := by
          refine tsum_congr fun k => ?_
          rw [mul_pow]
          ring_nf
      _ = Real.exp (-(rho : ℝ)) * ∑' k : ℕ, ((rho : ℝ) * r) ^ k / (Nat.factorial k : ℝ) := by
          rw [tsum_mul_left]
      _ = Real.exp (-(rho : ℝ)) * NormedSpace.exp ((rho : ℝ) * r) := by
          congr 1
          exact (NormedSpace.expSeries_div_hasSum_exp ((rho : ℝ) * r)).tsum_eq
      _ = Real.exp ((rho : ℝ) * (r - 1)) := by
        rw [statopia_math_node_4171527340_5abf08e7 ((rho : ℝ) * r), ← Real.exp_add]
        congr 1
        ring
  rw [hInt, hsum]
  /- @proof-region region.target-node.session.e2b1e077df77b68b end -/
