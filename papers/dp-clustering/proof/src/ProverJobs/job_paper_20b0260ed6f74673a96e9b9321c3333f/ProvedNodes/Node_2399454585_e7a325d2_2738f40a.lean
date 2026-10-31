import ProverJobs.job_paper_20b0260ed6f74673a96e9b9321c3333f.Vocabulary
import ProverJobs.job_paper_20b0260ed6f74673a96e9b9321c3333f.Base

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_2399454585_e7a325d2 : ∀ {Ω 𝒴 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒴]
    (μ : Measure Ω) (T Tp : Ω → 𝒴)
    (hT : Measurable T) (hTp : Measurable Tp)
    (hpush : Measure.map Tp μ = Measure.map T μ)
    (H : 𝒴 → ℝ)
    (hH : AEStronglyMeasurable H (Measure.map T μ))
    (hHint : Integrable (fun ω => H (T ω)) μ),
    Integrable (fun ω => H (Tp ω)) μ ∧
      ∫ ω, H (Tp ω) ∂μ = ∫ ω, H (T ω) ∂μ := by
  /- @proof-region region.target-node.session.9a6dc7a76a05d89b begin -/
  intro Ω 𝒴 _ _ μ T T' hT hT' hpush H hHmeas hH
  have hTae : AEMeasurable T μ := hT.aemeasurable
  have hT'ae : AEMeasurable T' μ := hT'.aemeasurable
  have hHν : Integrable H (Measure.map T μ) :=
    (MeasureTheory.integrable_map_measure hHmeas hTae).mpr hH
  have hHν' : Integrable H (Measure.map T' μ) := by
    rw [hpush]
    exact hHν
  have hν' : AEStronglyMeasurable H (Measure.map T' μ) := by
    rw [hpush]
    exact hHmeas
  refine ⟨(MeasureTheory.integrable_map_measure hν' hT'ae).mp hHν', ?_⟩
  calc ∫ ω, H (T' ω) ∂μ = ∫ y, H y ∂Measure.map T' μ :=
        (MeasureTheory.integral_map hT'ae hν').symm
    _ = ∫ y, H y ∂Measure.map T μ := by rw [hpush]
    _ = ∫ ω, H (T ω) ∂μ := MeasureTheory.integral_map hTae hHmeas
  /- @proof-region region.target-node.session.9a6dc7a76a05d89b end -/

end Statlib.Imported
