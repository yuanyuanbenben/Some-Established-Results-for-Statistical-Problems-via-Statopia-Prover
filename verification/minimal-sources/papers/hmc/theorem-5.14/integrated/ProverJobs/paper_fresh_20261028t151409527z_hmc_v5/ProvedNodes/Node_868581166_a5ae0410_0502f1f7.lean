import ProverJobs.paper_fresh_20261028t151409527z_hmc_v5.Vocabulary
import ProverJobs.paper_fresh_20261028t151409527z_hmc_v5.Base

namespace PaperProofTasks.paper_fresh_20261028t151409527z_hmc_v5

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal
open _root_.PaperProofTasks.paper_fresh_20261028t151409527z_hmc_v5.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal
namespace Statlib.Imported


set_option autoImplicit false in
theorem statopia_math_node_868581166_a5ae0410 : ∀ (d : ℕ) (U : HMCState d → ℝ) (π : Measure (HMCState d))
    (hpi_density : ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      π = c • volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-(U x)))))
    (hf : Measurable (fun x : HMCState d => ENNReal.ofReal (Real.exp (-(U x)))))
    (hvol : ∀ y : HMCState d, volume {y} = 0),
    ∀ x : HMCState d, π {x} = 0 := by
  /- @proof-region region.target-node.session.78d63c9ed7cbd662 begin -/
  intro d U π hπ_density hf_meas hvol_singleton x
  obtain ⟨c, _hc0, _hctop, rfl⟩ := hπ_density
  have hzero : (volume.withDensity fun y : HMCState d => ENNReal.ofReal (Real.exp (-(U y)))) {x} = 0 := by
    rw [withDensity_apply_eq_zero hf_meas]
    exact measure_mono_null Set.inter_subset_right (hvol_singleton x)
  rw [Measure.smul_apply, hzero, smul_zero]
  /- @proof-region region.target-node.session.78d63c9ed7cbd662 end -/

end Statlib.Imported
end

