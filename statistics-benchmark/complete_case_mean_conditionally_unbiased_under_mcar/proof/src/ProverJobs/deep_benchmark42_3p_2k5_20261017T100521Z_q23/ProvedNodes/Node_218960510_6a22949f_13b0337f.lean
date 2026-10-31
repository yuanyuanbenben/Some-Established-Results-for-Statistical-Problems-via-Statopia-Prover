import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q23.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q23.Base

open MeasureTheory ProbabilityTheory
open scoped BigOperators

open MeasureTheory ProbabilityTheory
open scoped BigOperators

set_option autoImplicit false in
theorem statopia_math_node_218960510_6a22949f : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ)
    (hXmeas : Measurable X) (hYmeas : Measurable Y)
    (hIndep : IndepFun X Y P)
    (hXbound : ∀ ω, |X ω| ≤ 1)
    (hYint : Integrable Y P),
    Integrable (fun ω => X ω * Y ω) P ∧
      ∫ ω, X ω * Y ω ∂P = (∫ ω, X ω ∂P) * (∫ ω, Y ω ∂P) := by
  /- @proof-region region.target-node.session.22055f1ae2ef9e1e begin -/
  intro Ω _ P _ X Y hXmeas hYmeas hIndep hXbound hYint
  constructor
  · have hXint : Integrable X P := by
      refine Integrable.mono' (integrable_const (1 : ℝ)) hXmeas.aestronglyMeasurable ?_
      filter_upwards with ω
      simpa using hXbound ω
    simpa [Pi.mul_apply] using hIndep.integrable_mul hXint hYint
  · exact hIndep.integral_fun_mul_eq_mul_integral hXmeas.aestronglyMeasurable
      hYmeas.aestronglyMeasurable
  /- @proof-region region.target-node.session.22055f1ae2ef9e1e end -/
