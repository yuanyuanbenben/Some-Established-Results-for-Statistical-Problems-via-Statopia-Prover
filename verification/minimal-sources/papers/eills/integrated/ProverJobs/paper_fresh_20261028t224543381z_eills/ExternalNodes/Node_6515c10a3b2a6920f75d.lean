import ProverJobs.paper_fresh_20261028t224543381z_eills.Base

namespace PaperProofTasks.paper_fresh_20261028t224543381z_eills

-- External DAG node: ext_model_1 (AXIOM)
example : Prop := (open MeasureTheory ProbabilityTheory in (open Statlib.Imported.StrongConvexityMain in (∀ (k : ℕ) (x y : EuclideanSpace ℝ (Fin k)),
    |(inner ℝ x y : ℝ)| ≤ ‖x‖ * ‖y‖ ∧
    (inner ℝ x y : ℝ) ^ 2 ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2 ∧
    (∀ t : ℝ, 0 < t → 2 * (inner ℝ x y : ℝ) ≤ t * ‖x‖ ^ 2 + t⁻¹ * ‖y‖ ^ 2))))
axiom ext_model_1 : (open MeasureTheory ProbabilityTheory in (open Statlib.Imported.StrongConvexityMain in (∀ (k : ℕ) (x y : EuclideanSpace ℝ (Fin k)),
    |(inner ℝ x y : ℝ)| ≤ ‖x‖ * ‖y‖ ∧
    (inner ℝ x y : ℝ) ^ 2 ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2 ∧
    (∀ t : ℝ, 0 < t → 2 * (inner ℝ x y : ℝ) ≤ t * ‖x‖ ^ 2 + t⁻¹ * ‖y‖ ^ 2))))

