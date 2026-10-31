import ProverJobs.real_main_theorem_3393c3b8aa74.Vocabulary
import ProverJobs.real_main_theorem_3393c3b8aa74.ProvedNodes
import ProverJobs.real_main_theorem_3393c3b8aa74.Base

namespace TriangleGame

theorem main_theorem (θ : ℝ) (hθ0 : 0 < θ) (hθ180 : θ < 180) :
    MulanCanGuarantee θ ↔ ∃ n : ℕ, 2 ≤ n ∧ θ = 180 / n
:= by
  /- @proof-region region.root.df4b85552bef begin -/
  constructor
  · intro h
    have hex : ∃ z : ℤ, (180 : ℝ) = (z : ℝ) * θ := by
      by_contra h180
      have he : IsTriangle ({60, 60, 60} : Multiset ℝ) := by
        refine ⟨?_, ?_, ?_⟩
        · simp
        · intro x hx
          simp at hx
          rw [hx]; norm_num
        · simp; norm_num
      have hw : MulanWins θ ({60, 60, 60} : Multiset ℝ) := h _ he
      obtain ⟨y, hy, z, hz⟩ := statopia_math_node_1810606264_793af19a θ h180 _ he hw
      simp at hy
      have h60 : (60 : ℝ) = (z : ℝ) * θ := by
        rw [← hy]
        exact hz
      apply h180
      refine ⟨3 * z, ?_⟩
      have hcast : ((3 * z : ℤ) : ℝ) = 3 * (z : ℝ) := by
        push_cast
        ring
      rw [hcast]
      calc (180 : ℝ) = 3 * 60 := by norm_num
        _ = 3 * ((z : ℝ) * θ) := by rw [← h60]
        _ = (3 * (z : ℝ)) * θ := by ring
    exact statopia_math_node_4212101893_b868743c θ hθ0 hθ180 hex
  · rintro ⟨n, hn, hθ⟩
    exact statopia_math_node_3665352230_eab14143 n hn θ hθ
  /- @proof-region region.root.df4b85552bef end -/

end TriangleGame
