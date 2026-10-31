import ProverJobs.job_paper_b0cf39bbf6c845c9a6b30a5db43f8efa.Vocabulary
import ProverJobs.job_paper_b0cf39bbf6c845c9a6b30a5db43f8efa.Base

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal MeasureTheory Topology BigOperators
open Statlib.Imported
open Statlib.Imported.DPMModel

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal MeasureTheory Topology BigOperators
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_115472241_0d96c29c : ∀ {Θ X : Type*} [MeasurableSpace Θ] [TopologicalSpace Θ] [MeasurableSpace X]
    (k : Θ → X → ℝ) (hk_meas : Measurable (Function.uncurry k)),
    Measurable (fun P : ProbabilityMeasure Θ => fun x : X =>
      ∫⁻ θ : Θ, ENNReal.ofReal (k θ x) ∂P.toMeasure) := by
  /- @proof-region region.target-node.session.1e0f6dfec7a8e5b4 begin -/
  intro Θ X _ _ _ k hk_meas
  rw [measurable_pi_iff]
  intro x
  have hsec : Measurable fun θ : Θ => (θ, x) := measurable_id.prodMk measurable_const
  have hf : Measurable fun θ : Θ => ENNReal.ofReal (k θ x) :=
    (hk_meas.comp hsec).ennreal_ofReal
  simpa using (MeasureTheory.Measure.measurable_lintegral hf).comp measurable_subtype_coe
  /- @proof-region region.target-node.session.1e0f6dfec7a8e5b4 end -/

end Statlib.Imported
