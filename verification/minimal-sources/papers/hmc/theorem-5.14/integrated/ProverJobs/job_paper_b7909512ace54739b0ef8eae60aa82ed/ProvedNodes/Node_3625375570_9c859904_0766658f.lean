import ProverJobs.job_paper_b7909512ace54739b0ef8eae60aa82ed.Vocabulary
import ProverJobs.job_paper_b7909512ace54739b0ef8eae60aa82ed.Base

namespace PaperProofTasks.job_paper_b7909512ace54739b0ef8eae60aa82ed

open _root_.PaperProofTasks.job_paper_b7909512ace54739b0ef8eae60aa82ed.Statlib.Imported
open Filter Topology

namespace Statlib.Imported

open Filter Topology

set_option autoImplicit false in
theorem statopia_math_node_3625375570_9c859904 : ∀ (E : Type*) [NormedAddCommGroup E] [ProperSpace E]
    (P : E → Prop)
    (hP : ∀ᶠ x in Filter.cocompact E, P x),
    ∃ R : ℝ, ∀ x : E, R ≤ ‖x‖ → P x := by
  /- @proof-region region.target-node.session.c09553e6aa9e035a begin -/
  intro E _ _ P hP
  have hcomap : Filter.comap (fun x : E => ‖x‖) Filter.atTop = Filter.cocompact E := by
    have h := comap_dist_left_atTop_eq_cocompact (0 : E)
    simpa [dist_eq_norm] using h
  have hP' : ∀ᶠ x in Filter.comap (fun y : E => ‖y‖) Filter.atTop, P x := by
    rw [hcomap]
    exact hP
  have h2 : ∀ᶠ t : ℝ in Filter.atTop, ∀ x : E, ‖x‖ = t → P x :=
    Filter.eventually_comap.mp hP'
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp h2
  exact ⟨R, fun x hx => hR ‖x‖ hx x rfl⟩
  /- @proof-region region.target-node.session.c09553e6aa9e035a end -/

end Statlib.Imported

