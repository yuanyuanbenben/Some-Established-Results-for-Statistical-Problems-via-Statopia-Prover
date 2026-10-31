import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q13.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q13.Base

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

set_option autoImplicit false in
theorem statopia_math_node_3356630755_4409a240 : ∀ (lambda : ℝ) (hlambda : 0 < lambda),
    IsProbabilityMeasure (expMeasure lambda) ∧
      ∀ t : ℝ,
        (expMeasure lambda) (Set.Iic t) =
          if t ≤ 0 then 0 else ENNReal.ofReal (1 - Real.exp (-(lambda * t))) := by
  /- @proof-region region.target-node.session.1f99bf191baf9235 begin -/
  intro lambda hlambda
  haveI : IsProbabilityMeasure (expMeasure lambda) := isProbabilityMeasure_expMeasure hlambda
  refine ⟨inferInstance, ?_⟩
  intro t
  have hμ : (expMeasure lambda) (Set.Iic t) =
      ENNReal.ofReal ((↑(cdf (expMeasure lambda)) : ℝ → ℝ) t) := by
    have hIic := StieltjesFunction.measure_Iic (cdf (expMeasure lambda))
      (ProbabilityTheory.tendsto_cdf_atBot (expMeasure lambda)) t
    rw [ProbabilityTheory.measure_cdf (expMeasure lambda)] at hIic
    simpa using hIic
  rw [hμ, ProbabilityTheory.cdf_expMeasure_eq hlambda t]
  by_cases ht : t ≤ 0
  · rw [if_pos ht]
    by_cases h0 : 0 ≤ t
    · have ht0 : t = 0 := le_antisymm ht h0
      rw [ht0]
      simp
    · rw [if_neg h0]
      simp
  · rw [if_neg ht]
    have h0 : 0 ≤ t := le_of_lt (lt_of_not_ge ht)
    rw [if_pos h0]
  /- @proof-region region.target-node.session.1f99bf191baf9235 end -/
