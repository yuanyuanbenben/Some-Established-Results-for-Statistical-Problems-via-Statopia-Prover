import ProverJobs.paper_fresh_20261028t224543381z_gaussian.Vocabulary
import ProverJobs.paper_fresh_20261028t224543381z_gaussian.Base

namespace PaperProofTasks.paper_fresh_20261028t224543381z_gaussian

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open _root_.PaperProofTasks.paper_fresh_20261028t224543381z_gaussian.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace Statlib.Imported
open _root_.Statlib

set_option autoImplicit false in
theorem statopia_math_node_550003712_e9ee920c : ∀ (mu nu rho : Measure ℝ)
    (hmu : ∀ t : ℝ, mu.real (Set.Iic t) ∈ Set.Icc (0 : ℝ) 1)
    (hnu : ∀ t : ℝ, nu.real (Set.Iic t) ∈ Set.Icc (0 : ℝ) 1)
    (hrho : ∀ t : ℝ, rho.real (Set.Iic t) ∈ Set.Icc (0 : ℝ) 1),
    dK mu nu ≤ dK mu rho + dK rho nu := by
  /- @proof-region region.target-node.session.f1c20c2311304d0f begin -/
  intro mu nu rho hmu hnu hrho
  have abs_sub_le_one : ∀ a b : ℝ, a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 → |a - b| ≤ 1 :=
    fun a b ha hb => abs_le.mpr ⟨by linarith [ha.1, hb.2], by linarith [ha.2, hb.1]⟩
  have hbdd_f : BddAbove (Set.range fun s : ℝ => |mu.real (Set.Iic s) - rho.real (Set.Iic s)|) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨s, rfl⟩
    exact abs_sub_le_one _ _ (hmu s) (hrho s)
  have hbdd_g : BddAbove (Set.range fun s : ℝ => |rho.real (Set.Iic s) - nu.real (Set.Iic s)|) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨s, rfl⟩
    exact abs_sub_le_one _ _ (hrho s) (hnu s)
  have hstep : ∀ t : ℝ, |mu.real (Set.Iic t) - nu.real (Set.Iic t)|
      ≤ (⨆ s : ℝ, |mu.real (Set.Iic s) - rho.real (Set.Iic s)|)
        + (⨆ s : ℝ, |rho.real (Set.Iic s) - nu.real (Set.Iic s)|) := by
    intro t
    have h1 : |mu.real (Set.Iic t) - rho.real (Set.Iic t)|
        ≤ ⨆ s : ℝ, |mu.real (Set.Iic s) - rho.real (Set.Iic s)| := le_ciSup hbdd_f t
    have h2 : |rho.real (Set.Iic t) - nu.real (Set.Iic t)|
        ≤ ⨆ s : ℝ, |rho.real (Set.Iic s) - nu.real (Set.Iic s)| := le_ciSup hbdd_g t
    have htri : |mu.real (Set.Iic t) - nu.real (Set.Iic t)|
        ≤ |mu.real (Set.Iic t) - rho.real (Set.Iic t)|
          + |rho.real (Set.Iic t) - nu.real (Set.Iic t)| := by
      have h := abs_add_le (mu.real (Set.Iic t) - rho.real (Set.Iic t))
        (rho.real (Set.Iic t) - nu.real (Set.Iic t))
      have heq : (mu.real (Set.Iic t) - rho.real (Set.Iic t))
          + (rho.real (Set.Iic t) - nu.real (Set.Iic t))
          = mu.real (Set.Iic t) - nu.real (Set.Iic t) := by ring
      rwa [heq] at h
    linarith
  simpa only [dK] using ciSup_le hstep
  /- @proof-region region.target-node.session.f1c20c2311304d0f end -/

end Statlib.Imported
end

