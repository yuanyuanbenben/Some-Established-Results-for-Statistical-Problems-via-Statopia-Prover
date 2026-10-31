import ProverJobs.real_main_theorem_3393c3b8aa74.Vocabulary
import ProverJobs.real_main_theorem_3393c3b8aa74.Base

open TriangleGame

namespace TriangleGame

set_option autoImplicit false in
theorem statopia_math_node_734679360_23af815d : ∀ (s L R : Multiset ℝ)
    (hs : IsTriangle s) (hcut : IsCut s L R),
    IsTriangle L ∧ IsTriangle R := by
  /- @proof-region region.target-node.session.6c3778dea890647a begin -/
  intro s L R hs hcut
  obtain ⟨α, β, γ, x, rfl, hγx, hxβ, rfl, rfl⟩ := hcut
  have hβ : 0 < β := hs.2.1 β (by simp)
  have hγ : 0 < γ := hs.2.1 γ (by simp)
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · simp [Multiset.card_cons]
    · intro y hy
      simp at hy
      rcases hy with h | h | h
      · rw [h]; exact hβ
      · rw [h]; linarith
      · rw [h]; linarith
    · simp [Multiset.sum_cons]
      try ring
  · refine ⟨?_, ?_, ?_⟩
    · simp [Multiset.card_cons]
    · intro y hy
      simp at hy
      rcases hy with h | h | h
      · rw [h]; exact hγ
      · rw [h]; linarith
      · rw [h]; linarith
    · simp [Multiset.sum_cons]
      try ring
  /- @proof-region region.target-node.session.6c3778dea890647a end -/

end TriangleGame
