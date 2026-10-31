import ProverJobs.paper_fresh_20261028t224543381z_hmc_22.Base

namespace PaperProofTasks.paper_fresh_20261028t224543381z_hmc_22

-- External DAG node: ext_model_1 (AXIOM)
example : Prop := (open MeasureTheory ProbabilityTheory Filter in (open scoped ENNReal Topology in (∀ (d : ℕ)
    (P : Statlib.Imported.HMCState d → Measure (Statlib.Imported.HMCState d))
    (π : Measure (Statlib.Imported.HMCState d)) [IsProbabilityMeasure π]
    (hlocal : ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ x : Statlib.Imported.HMCState d,
        P x (Metric.ball x δ) > ENNReal.ofReal (1 - η)),
    Statlib.Imported.IsGeometricallyErgodic P π →
      ∃ β : ℝ, 0 < β ∧ ∫⁻ x, ENNReal.ofReal (Real.exp (β * ‖x‖)) ∂π < ⊤)))
axiom ext_model_1 : (open MeasureTheory ProbabilityTheory Filter in (open scoped ENNReal Topology in (∀ (d : ℕ)
    (P : Statlib.Imported.HMCState d → Measure (Statlib.Imported.HMCState d))
    (π : Measure (Statlib.Imported.HMCState d)) [IsProbabilityMeasure π]
    (hlocal : ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ x : Statlib.Imported.HMCState d,
        P x (Metric.ball x δ) > ENNReal.ofReal (1 - η)),
    Statlib.Imported.IsGeometricallyErgodic P π →
      ∃ β : ℝ, 0 < β ∧ ∫⁻ x, ENNReal.ofReal (Real.exp (β * ‖x‖)) ∂π < ⊤)))

