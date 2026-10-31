import ProverJobs.real_main_theorem_3393c3b8aa74.Vocabulary
import ProverJobs.real_main_theorem_3393c3b8aa74.Base
import ProverJobs.real_main_theorem_3393c3b8aa74.ProvedNodes.Node_734679360_23af815d_b658a6ec
import ProverJobs.real_main_theorem_3393c3b8aa74.ProvedNodes.Node_944270810_55a7315b_a4d84f90
open TriangleGame

namespace TriangleGame

set_option autoImplicit false in
theorem statopia_math_node_1810606264_793af19a : ∀ (t : ℝ)
    (h180 : ¬ ∃ z : ℤ, (180 : ℝ) = (z : ℝ) * t) (s : Multiset ℝ)
    (hs : IsTriangle s) (hwin : MulanWins t s),
    ∃ y ∈ s, ∃ z : ℤ, y = (z : ℝ) * t := by
  /- @proof-region region.target-node.session.c470d4bd06a3aec9 begin -/
  classical
  intro t h180 s hs hwin
  refine MulanWins.rec
      (motive := fun s _ => IsTriangle s → ∃ y ∈ s, ∃ z : ℤ, y = (z : ℝ) * t)
      (fun {s} h _ => ⟨t, h, 1, by simp⟩)
      (fun {s L R} hcut hL hR IHL IHR htri => ?_) hwin hs
  by_contra hcon
  have hc : ∀ y ∈ s, ¬ ∃ z : ℤ, y = (z : ℝ) * t := by
    intro y hy hz
    exact hcon ⟨y, hy, hz⟩
  obtain ⟨hLtri, hRtri⟩ := statopia_math_node_734679360_23af815d s L R htri hcut
  rcases statopia_math_node_944270810_55a7315b t h180 s L R htri hcut hc with hLa | hRa
  · obtain ⟨y, hy, hz⟩ := IHL hLtri
    exact hLa y hy hz
  · obtain ⟨y, hy, hz⟩ := IHR hRtri
    exact hRa y hy hz
  /- @proof-region region.target-node.session.c470d4bd06a3aec9 end -/

end TriangleGame
