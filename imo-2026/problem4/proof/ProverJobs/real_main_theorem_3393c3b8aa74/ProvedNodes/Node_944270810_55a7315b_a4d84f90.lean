import ProverJobs.real_main_theorem_3393c3b8aa74.Vocabulary
import ProverJobs.real_main_theorem_3393c3b8aa74.Base

open TriangleGame

namespace TriangleGame

set_option autoImplicit false in
theorem statopia_math_node_944270810_55a7315b : ∀ (t : ℝ)
    (h180 : ¬ ∃ z : ℤ, (180 : ℝ) = (z : ℝ) * t)
    (s L R : Multiset ℝ)
    (hs : IsTriangle s)
    (hcut : IsCut s L R)
    (hsavoid : ∀ y ∈ s, ¬ ∃ z : ℤ, y = (z : ℝ) * t),
    (∀ y ∈ L, ¬ ∃ z : ℤ, y = (z : ℝ) * t) ∨
      (∀ y ∈ R, ¬ ∃ z : ℤ, y = (z : ℝ) * t) := by
  /- @proof-region region.target-node.session.9078c91f27e42f1b begin -/
  classical
  intro t h180 s L R hs hcut hsavoid
  unfold IsCut at hcut
  obtain ⟨α, β, γ, x, hseq, hγx, hxβ, hL, hR⟩ := hcut
  have hsum : α + β + γ = 180 := by
    have h : s.sum = 180 := hs.2.2
    rw [hseq] at h
    simp at h
    linarith
  have hαmem : α ∈ s := by rw [hseq]; simp
  have hβmem : β ∈ s := by rw [hseq]; simp
  have hγmem : γ ∈ s := by rw [hseq]; simp
  have hα_avoid : ¬ ∃ z : ℤ, α = (z : ℝ) * t := hsavoid α hαmem
  have hβ_avoid : ¬ ∃ z : ℤ, β = (z : ℝ) * t := hsavoid β hβmem
  have hγ_avoid : ¬ ∃ z : ℤ, γ = (z : ℝ) * t := hsavoid γ hγmem
  have gadd : ∀ a b : ℝ, (∃ z : ℤ, a = (z : ℝ) * t) →
      (∃ z : ℤ, b = (z : ℝ) * t) → (∃ z : ℤ, a + b = (z : ℝ) * t) := by
    rintro a b ⟨za, hza⟩ ⟨zb, hzb⟩
    exact ⟨za + zb, by rw [hza, hzb]; push_cast; ring⟩
  have gsub : ∀ a b : ℝ, (∃ z : ℤ, a = (z : ℝ) * t) →
      (∃ z : ℤ, b = (z : ℝ) * t) → (∃ z : ℤ, a - b = (z : ℝ) * t) := by
    rintro a b ⟨za, hza⟩ ⟨zb, hzb⟩
    exact ⟨za - zb, by rw [hza, hzb]; push_cast; ring⟩
  have hnb : ¬ ((∃ y ∈ L, ∃ z : ℤ, y = (z : ℝ) * t) ∧
      (∃ y ∈ R, ∃ z : ℤ, y = (z : ℝ) * t)) := by
    rintro ⟨⟨yL, hyL, zL, hzL⟩, ⟨yR, hyR, zR, hzR⟩⟩
    have hLu : yL = β ∨ yL = x ∨ yL = 180 - β - x := by
      rw [hL] at hyL; simpa using hyL
    have hRv : yR = γ ∨ yR = 180 - x ∨ yR = x - γ := by
      rw [hR] at hyR; simpa using hyR
    rcases hLu with h | h | h
    · rw [h] at hzL; exact hβ_avoid ⟨zL, hzL⟩
    · rw [h] at hzL
      rcases hRv with h2 | h2 | h2
      · rw [h2] at hzR; exact hγ_avoid ⟨zR, hzR⟩
      · rw [h2] at hzR
        exact h180 (by
          have h1 := gadd x (180 - x) ⟨zL, hzL⟩ ⟨zR, hzR⟩
          have hx1 : x + (180 - x) = (180 : ℝ) := by ring
          rwa [hx1] at h1)
      · rw [h2] at hzR
        exact hγ_avoid (by
          have h1 := gsub x (x - γ) ⟨zL, hzL⟩ ⟨zR, hzR⟩
          have hx1 : x - (x - γ) = γ := by ring
          rwa [hx1] at h1)
    · rw [h] at hzL
      rcases hRv with h2 | h2 | h2
      · rw [h2] at hzR; exact hγ_avoid ⟨zR, hzR⟩
      · rw [h2] at hzR
        exact hβ_avoid (by
          have h1 := gsub (180 - x) (180 - β - x) ⟨zR, hzR⟩ ⟨zL, hzL⟩
          have hx1 : (180 - x) - (180 - β - x) = β := by ring
          rwa [hx1] at h1)
      · rw [h2] at hzR
        exact hα_avoid (by
          have h1 := gadd (180 - β - x) (x - γ) ⟨zL, hzL⟩ ⟨zR, hzR⟩
          have hx1 : (180 - β - x) + (x - γ) = α := by linarith [hsum]
          rwa [hx1] at h1)
  rcases not_and_or.mp hnb with hnL | hnR
  · left
    intro y hy hq
    exact hnL ⟨y, hy, hq⟩
  · right
    intro y hy hq
    exact hnR ⟨y, hy, hq⟩
  /- @proof-region region.target-node.session.9078c91f27e42f1b end -/

end TriangleGame
