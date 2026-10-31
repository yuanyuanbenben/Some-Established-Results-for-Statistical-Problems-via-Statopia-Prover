import ProverJobs.job_paper_7ad7b898530c48b2be48d9fe88a3d538.Vocabulary
import ProverJobs.job_paper_7ad7b898530c48b2be48d9fe88a3d538.ProvedNodes
import ProverJobs.job_paper_7ad7b898530c48b2be48d9fe88a3d538.Base

namespace PaperProofTasks.job_paper_7ad7b898530c48b2be48d9fe88a3d538

namespace Statlib.Imported
open MeasureTheory ProbabilityTheory

theorem paper_7ad7b898530c48b2be48d9fe88a3d538 (d : ℕ)
    (U : Config d → ℝ) (hU_nonneg : ∀ x, 0 ≤ U x) (hU_diff : Differentiable ℝ U)
    (𝔏 : Measure ℕ) [IsProbabilityMeasure 𝔏] (h𝔏 : 𝔏 {0} = 0)
    (hA1 : (0 < 𝔏 {1}) ∧
      ∀ (x₀ p₀ : Config d) (ε : ℝ), 0 < ε →
        ∃ s : ℝ, 0 < s ∧
          ∫⁻ L, ENNReal.ofReal (Real.exp (s * ‖leapfrogPos U ε L x₀ p₀‖)) ∂𝔏 < ⊤) :
    (0 < 𝔏 {1}) ∧
      ∀ (x₀ p₀ : Config d) (ε : ℝ), 0 < ε →
        ∃ s : ℝ, 0 < s ∧
          ∫⁻ L, ENNReal.ofReal (Real.exp (s * ‖leapfrogPos U ε L x₀ p₀‖)) ∂𝔏 < ⊤
:= by
  /- @proof-region region.root.ec2407354990 begin -/ exact hA1  /- @proof-region region.root.ec2407354990 end -/

end Statlib.Imported

-- Paper root revision 685b9bda-1fdd-44b1-b86a-1a871568cf48

