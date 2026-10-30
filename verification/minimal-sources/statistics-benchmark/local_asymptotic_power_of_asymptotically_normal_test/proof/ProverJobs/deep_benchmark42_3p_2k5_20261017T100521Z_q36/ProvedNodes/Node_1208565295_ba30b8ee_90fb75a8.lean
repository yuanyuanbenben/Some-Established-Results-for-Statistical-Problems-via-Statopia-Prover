import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q36.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q36.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q36.ProvedNodes.Node_4054383514_ec564b99_5f9e363c

open MeasureTheory ProbabilityTheory Filter Topology

open MeasureTheory ProbabilityTheory Filter Topology

set_option autoImplicit false in
theorem statopia_math_node_1208565295_ba30b8ee : ∀ (mu : ℕ → ProbabilityMeasure ℝ)
    (gamma : ProbabilityMeasure ℝ)
    (hgamma : NoAtoms (gamma : Measure ℝ))
    (hweak : Tendsto mu atTop (𝓝 gamma))
    (a : ℝ),
    Tendsto (fun n => ENNReal.toReal ((mu n : Measure ℝ) (Set.Ioi a))) atTop
      (𝓝 (1 - cdf (gamma : Measure ℝ) a)) := by
  /- @proof-region region.target-node.session.f5c21beb6995c267 begin -/
  intro mu gamma hgamma hweak a
  have hfront : (gamma : Measure ℝ) (frontier (Set.Ioi a)) = 0 := by
    rw [frontier_Ioi]
    exact hgamma.measure_singleton a
  have hconv : Tendsto (fun n => (mu n : Measure ℝ) (Set.Ioi a)) atTop
      (𝓝 ((gamma : Measure ℝ) (Set.Ioi a))) :=
    MeasureTheory.ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hweak hfront
  have hfin : (gamma : Measure ℝ) (Set.Ioi a) ≠ ⊤ := by
    have hle : (gamma : Measure ℝ) (Set.Ioi a) ≤ (gamma : Measure ℝ) Set.univ :=
      measure_mono (Set.subset_univ (Set.Ioi a))
    rw [measure_univ] at hle
    exact ne_top_of_le_ne_top (by simp) hle
  have hreal : Tendsto (fun n => ENNReal.toReal ((mu n : Measure ℝ) (Set.Ioi a))) atTop
      (𝓝 (ENNReal.toReal ((gamma : Measure ℝ) (Set.Ioi a)))) :=
    (ENNReal.tendsto_toReal hfin).comp hconv
  have hcdf : ENNReal.toReal ((gamma : Measure ℝ) (Set.Ioi a))
      = 1 - cdf (gamma : Measure ℝ) a :=
    statopia_math_node_4054383514_ec564b99 (gamma : Measure ℝ) a
  rw [hcdf] at hreal
  exact hreal
  /- @proof-region region.target-node.session.f5c21beb6995c267 end -/
