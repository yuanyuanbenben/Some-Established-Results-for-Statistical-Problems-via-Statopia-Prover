import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q01.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q01.Base

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

set_option autoImplicit false in
theorem statopia_math_node_1950684925_391067fc : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (d : ℕ)
    (A B : Ω → EuclideanSpace ℝ (Fin d))
    (hA : Measurable A)
    (hB : Measurable B)
    (hAB : IndepFun A B P),
    ∀ t : EuclideanSpace ℝ (Fin d),
      charFun (P.map (fun ω => A ω + B ω)) t =
        charFun (P.map A) t * charFun (P.map B) t := by
  /- @proof-region region.target-node.session.31e9b462c8c659e6 begin -/
  intro Ω _ P _ d A B hA hB hAB t
  exact congrFun (ProbabilityTheory.IndepFun.charFun_map_add_eq_mul (P := P) (X := A) (Y := B)
    hA.aemeasurable hB.aemeasurable hAB) t
  /- @proof-region region.target-node.session.31e9b462c8c659e6 end -/
