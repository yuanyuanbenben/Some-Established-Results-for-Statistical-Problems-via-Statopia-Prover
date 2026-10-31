import ProverJobs.real_main_theorem_3393c3b8aa74.Vocabulary
import ProverJobs.real_main_theorem_3393c3b8aa74.Base
import ProverJobs.real_main_theorem_3393c3b8aa74.ProvedNodes.Node_734679360_23af815d_b658a6ec
open TriangleGame

namespace TriangleGame

set_option autoImplicit false in
theorem statopia_math_node_3609921484_532dba24 : ∀ (t : ℝ) (ht : 0 < t)
    (k : ℕ) (hk : 1 ≤ k) (s : Multiset ℝ) (hs : IsTriangle s)
    (hangle : HasAngle ((k : ℝ) * t) s), MulanWins t s := by
  /- @proof-region region.target-node.session.69026ecb365e43af begin -/
  intro t ht
  classical
  have hkey : ∀ k : ℕ, 1 ≤ k → ∀ s : Multiset ℝ, IsTriangle s → HasAngle ((k : ℝ) * t) s → MulanWins t s := by
    intro k hk
    refine Nat.le_induction (m := 1)
      (P := fun k _ => ∀ s : Multiset ℝ, IsTriangle s → HasAngle ((k : ℝ) * t) s → MulanWins t s) ?_ ?_ k hk
    · intro s hs hangle
      exact MulanWins.win (by simpa using hangle)
    · intro n hn ih s hs hangle
      obtain ⟨hcard, hpos, hsum⟩ := hs
      have hsmem : (((n + 1 : ℕ) : ℝ) * t) ∈ s := hangle
      have hcons : (((n + 1 : ℕ) : ℝ) * t) ::ₘ s.erase (((n + 1 : ℕ) : ℝ) * t) = s :=
        Multiset.cons_erase hsmem
      have hcard' : (s.erase (((n + 1 : ℕ) : ℝ) * t)).card = 2 := by
        have h2 : (((n + 1 : ℕ) : ℝ) * t ::ₘ s.erase (((n + 1 : ℕ) : ℝ) * t)).card = 3 := by
          rw [hcons]; exact hcard
        rw [Multiset.card_cons] at h2
        omega
      obtain ⟨b, c, hbc⟩ := Multiset.card_eq_two.mp hcard'
      have hs_eq : s = {((n + 1 : ℕ) : ℝ) * t, b, c} := by
        rw [← hcons, hbc]
        first | rfl | simp
      have hsum_eq : ((n : ℝ) + 1) * t + b + c = 180 := by
        have h1 : s.sum = ((n : ℝ) + 1) * t + b + c := by
          rw [hs_eq]
          simp
          try (push_cast; ring)
        exact h1.symm.trans hsum
      have hnt : (0 : ℝ) < (n : ℝ) * t := by
        have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        nlinarith [ht, hn1]
      have hcx : c < 180 - b - t := by nlinarith [hsum_eq, hnt, ht]
      have hxb : 180 - b - t < 180 - b := by linarith [ht]
      have hcut : IsCut s {b, 180 - b - t, 180 - b - (180 - b - t)}
          {c, 180 - (180 - b - t), (180 - b - t) - c} :=
        ⟨((n + 1 : ℕ) : ℝ) * t, b, c, 180 - b - t, hs_eq, hcx, hxb, rfl, rfl⟩
      obtain ⟨_, hRtri⟩ :=
        statopia_math_node_734679360_23af815d s {b, 180 - b - t, 180 - b - (180 - b - t)}
          {c, 180 - (180 - b - t), (180 - b - t) - c} ⟨hcard, hpos, hsum⟩ hcut
      have hLwin : MulanWins t {b, 180 - b - t, 180 - b - (180 - b - t)} := by
        refine MulanWins.win ?_
        show t ∈ ({b, 180 - b - t, 180 - b - (180 - b - t)} : Multiset ℝ)
        rw [show 180 - b - (180 - b - t) = t by ring]
        simp
      have hRwin : MulanWins t {c, 180 - (180 - b - t), (180 - b - t) - c} := by
        apply ih _ hRtri
        show (n : ℝ) * t ∈ ({c, 180 - (180 - b - t), (180 - b - t) - c} : Multiset ℝ)
        rw [show (180 - b - t) - c = (n : ℝ) * t by nlinarith [hsum_eq],
            show 180 - (180 - b - t) = b + t by ring]
        simp
      exact MulanWins.move hcut hLwin hRwin
  exact hkey
  /- @proof-region region.target-node.session.69026ecb365e43af end -/

end TriangleGame
