import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q36.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q36.Base

open MeasureTheory ProbabilityTheory Filter Topology

open MeasureTheory ProbabilityTheory Filter Topology

set_option autoImplicit false in
theorem statopia_math_node_4054383514_ec564b99 : ∀ (mu : Measure ℝ) [IsProbabilityMeasure mu] (a : ℝ),
    ENNReal.toReal (mu (Set.Ioi a)) = 1 - cdf mu a := by
  /- @proof-region region.target-node.session.2b2adb43350db417 begin -/
  intro mu _ a
  have hle : mu (Set.Iic a) ≤ 1 := by
    have h : mu (Set.Iic a) ≤ mu Set.univ := measure_mono (Set.subset_univ (Set.Iic a))
    simpa using h
  have hfin : mu (Set.Iic a) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hle
  have htail : mu (Set.Ioi a) = 1 - mu (Set.Iic a) := by
    rw [← Set.compl_Iic, measure_compl measurableSet_Iic hfin]
    simp
  have hcdf : (mu (Set.Iic a)).toReal = cdf mu a := by
    rw [← ProbabilityTheory.ofReal_cdf mu a,
      ENNReal.toReal_ofReal (ProbabilityTheory.cdf_nonneg mu a)]
  rw [htail, ENNReal.toReal_sub_of_le hle ENNReal.one_ne_top, ENNReal.toReal_one, hcdf]
  /- @proof-region region.target-node.session.2b2adb43350db417 end -/
