import ProverJobs.job_paper_b0cf39bbf6c845c9a6b30a5db43f8efa.Vocabulary
import ProverJobs.job_paper_b0cf39bbf6c845c9a6b30a5db43f8efa.Base
import ProverJobs.job_paper_b0cf39bbf6c845c9a6b30a5db43f8efa.ProvedNodes.Node_1617600847_73f32bf3_3d768aa1

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal MeasureTheory Topology BigOperators
open Statlib.Imported
open Statlib.Imported.DPMModel

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal MeasureTheory Topology BigOperators
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_1750728313_95a4e01c : ∀ (Θ : Type*) [TopologicalSpace Θ]
    [MeasurableSpace Θ],
    Measurable (fun P : ProbabilityMeasure Θ =>
      (Measure.dirac P).prod (Measure.infinitePi (fun _ : ℕ => (P : Measure Θ)))) := by
  /- @proof-region region.target-node.session.69d07d3ba3e21b82 begin -/
  intro Θ _ _
  have hsub : Measurable fun P : ProbabilityMeasure Θ => (↑P : Measure Θ) := measurable_subtype_coe
  have hda : Measurable fun P : ProbabilityMeasure Θ => Measure.dirac P := Measure.measurable_dirac
  have hip : Measurable fun P : ProbabilityMeasure Θ =>
      Measure.infinitePi (fun _ : ℕ => (↑P : Measure Θ)) :=
    statopia_math_node_1617600847_73f32bf3 Θ
  have hpair : Measurable fun P : ProbabilityMeasure Θ =>
      ((⟨Measure.dirac P, inferInstance⟩ : ProbabilityMeasure (ProbabilityMeasure Θ)),
        (⟨Measure.infinitePi (fun _ : ℕ => (↑P : Measure Θ)), inferInstance⟩ :
          ProbabilityMeasure (ℕ → Θ))) := by
    refine Measurable.prodMk ?_ ?_ <;> measurability
  simpa [Function.comp] using ProbabilityMeasure.measurable_fun_prod.comp hpair
  /- @proof-region region.target-node.session.69d07d3ba3e21b82 end -/

end Statlib.Imported
