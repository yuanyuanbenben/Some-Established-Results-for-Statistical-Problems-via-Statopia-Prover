import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q16.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q16.Base

open MeasureTheory Matrix ProbabilityTheory

open MeasureTheory Matrix ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_359342246_18c0b9ff : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ)
    (epsilon : Ω → Fin n → ℝ)
    (hgaussian : ∀ i : Fin n, ∃ v : NNReal,
      HasLaw (fun ω => epsilon ω i) (gaussianReal 0 v) P),
    AEMeasurable epsilon P := by
  /- @proof-region region.target-node.session.80ab8bcc21a9cf98 begin -/
  intro Ω _ P _ n epsilon hgaussian
  refine aemeasurable_pi_iff.2 (fun i => ?_)
  obtain ⟨v, hv⟩ := hgaussian i
  exact hv.1
  /- @proof-region region.target-node.session.80ab8bcc21a9cf98 end -/
