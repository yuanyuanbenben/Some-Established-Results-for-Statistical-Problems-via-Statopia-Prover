import ProverJobs.real_main_theorem_3393c3b8aa74.Vocabulary
import ProverJobs.real_main_theorem_3393c3b8aa74.Base
import ProverJobs.real_main_theorem_3393c3b8aa74.ProvedNodes.Node_3609921484_532dba24_77cffd73
import ProverJobs.real_main_theorem_3393c3b8aa74.ProvedNodes.Node_389705034_bebdf092_00c99d6f
import ProverJobs.real_main_theorem_3393c3b8aa74.ProvedNodes.Node_734679360_23af815d_b658a6ec
open TriangleGame

namespace TriangleGame

set_option autoImplicit false in
theorem statopia_math_node_3665352230_eab14143 : ∀ (n : ℕ) (hn : 2 ≤ n) (t : ℝ)
    (ht : t = 180 / n), MulanCanGuarantee t := by
  /- @proof-region region.target-node.session.754077fc8d1afa58 begin -/
  intro n hn t ht
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnt : (n : ℝ) * t = 180 := by rw [ht, mul_comm]; exact div_mul_cancel₀ 180 hn0
  have ht_pos : 0 < t := by rw [ht]; exact div_pos (by norm_num) hnR
  intro s hs
  have hcard : s.card = 3 := hs.1
  have hpos : ∀ x ∈ s, 0 < x := hs.2.1
  have hsum : s.sum = 180 := hs.2.2
  obtain ⟨a, b, c, hsabc⟩ := Multiset.card_eq_three.mp hcard
  have habc : a + b + c = 180 := by
    have h1 : s.sum = a + b + c := by
      rw [hsabc]; simp [Multiset.sum_cons]; ring
    linarith
  have ha_pos : 0 < a := hpos a (by rw [hsabc]; simp)
  have hb_pos : 0 < b := hpos b (by rw [hsabc]; simp)
  have hc_pos : 0 < c := hpos c (by rw [hsabc]; simp)
  by_cases hA : HasAngle t s
  · exact MulanWins.win hA
  · have hat : a ≠ t := by intro h; apply hA; rw [hsabc, h]; simp [HasAngle]
    have hbt : b ≠ t := by intro h; apply hA; rw [hsabc, h]; simp [HasAngle]
    have hct : c ≠ t := by intro h; apply hA; rw [hsabc, h]; simp [HasAngle]
    have cut_win : ∀ α β γ : ℝ, s = {α, β, γ} → 0 < β → 0 < γ → t < α →
        α + β + γ = 180 → MulanWins t s := by
      intro α β γ hseq hβ_pos hγ_pos hαt hsum
      have hlo : (0 : ℝ) ≤ γ := le_of_lt hγ_pos
      have hlen : (180 - β) - γ > t := by
        have h1 : (180 : ℝ) - β - γ = α := by linarith
        linarith
      obtain ⟨m, hm1, hmlo, hmhi⟩ :=
        statopia_math_node_389705034_bebdf092 t γ (180 - β) ht_pos hlo hlen
      have hmβ : (m : ℝ) * t < 180 := by linarith [hmhi, hβ_pos]
      have hmnlt : m < n := by
        by_contra h
        push_neg at h
        have h1 : (m : ℝ) * t < (n : ℝ) * t := by rw [hnt]; exact hmβ
        have h2 : (n : ℝ) * t ≤ (m : ℝ) * t :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast h) (le_of_lt ht_pos)
        linarith
      have hcut : IsCut s {β, (m : ℝ) * t, 180 - β - (m : ℝ) * t}
          {γ, 180 - (m : ℝ) * t, (m : ℝ) * t - γ} :=
        ⟨α, β, γ, (m : ℝ) * t, hseq, hmlo, hmhi, rfl, rfl⟩
      obtain ⟨hLtri, hRtri⟩ :=
        statopia_math_node_734679360_23af815d s {β, (m : ℝ) * t, 180 - β - (m : ℝ) * t}
          {γ, 180 - (m : ℝ) * t, (m : ℝ) * t - γ} hs hcut
      have hLangle : HasAngle ((m : ℝ) * t) {β, (m : ℝ) * t, 180 - β - (m : ℝ) * t} := by
        simp [HasAngle]
      have hLwin : MulanWins t {β, (m : ℝ) * t, 180 - β - (m : ℝ) * t} :=
        statopia_math_node_3609921484_532dba24 t ht_pos m hm1 _ hLtri hLangle
      have hnmcast : ((n - m : ℕ) : ℝ) = (n : ℝ) - (m : ℝ) := by
        rw [Nat.cast_sub (le_of_lt hmnlt)]
      have heq : ((n - m : ℕ) : ℝ) * t = 180 - (m : ℝ) * t := by
        rw [hnmcast, sub_mul, hnt]
      have hRangle : HasAngle (((n - m : ℕ) : ℝ) * t) {γ, 180 - (m : ℝ) * t, (m : ℝ) * t - γ} := by
        simp [HasAngle, heq]
      have hnm1 : 1 ≤ n - m := by omega
      have hRwin : MulanWins t {γ, 180 - (m : ℝ) * t, (m : ℝ) * t - γ} :=
        statopia_math_node_3609921484_532dba24 t ht_pos (n - m) hnm1 _ hRtri hRangle
      exact MulanWins.move hcut hLwin hRwin
    by_cases ha : t < a
    · exact cut_win a b c hsabc hb_pos hc_pos ha habc
    · by_cases hb : t < b
      · have hseq : s = {b, a, c} := by rw [hsabc]; exact Multiset.cons_swap a b (c ::ₘ 0)
        have hsum : b + a + c = 180 := by linarith
        exact cut_win b a c hseq ha_pos hc_pos hb hsum
      · by_cases hc : t < c
        · have hseq : s = {c, a, b} := by
            rw [hsabc]
            exact (congrArg (Multiset.cons a) (Multiset.cons_swap b c (0 : Multiset ℝ))).trans
              (Multiset.cons_swap a c (b ::ₘ 0))
          have hsum : c + a + b = 180 := by linarith
          exact cut_win c a b hseq ha_pos hb_pos hc hsum
        · have hlt_a : a < t := lt_of_le_of_ne (le_of_not_gt ha) hat
          have hlt_b : b < t := lt_of_le_of_ne (le_of_not_gt hb) hbt
          have hlt_c : c < t := lt_of_le_of_ne (le_of_not_gt hc) hct
          have hall : (180 : ℝ) < 3 * t := by linarith [habc, hlt_a, hlt_b, hlt_c]
          have hnR3 : (n : ℝ) < 3 := by
            have h1 : (n : ℝ) * t < 3 * t := by rw [hnt]; exact hall
            by_contra h
            push_neg at h
            have h2 : (3 : ℝ) * t ≤ (n : ℝ) * t :=
              mul_le_mul_of_nonneg_right h (le_of_lt ht_pos)
            linarith
          have hn3 : n < 3 := by exact_mod_cast hnR3
          have hn2 : n = 2 := by omega
          have ht90 : t = 90 := by rw [ht, hn2]; norm_num
          have ht180 : (180 : ℝ) - t = t := by linarith
          have hcut : IsCut s {b, t, 180 - b - t} {c, 180 - t, t - c} :=
            ⟨a, b, c, t, hsabc, hlt_c, by linarith, rfl, rfl⟩
          exact MulanWins.move hcut
            (MulanWins.win (by simp [HasAngle]))
            (MulanWins.win (by simp [HasAngle, ht180]))
  /- @proof-region region.target-node.session.754077fc8d1afa58 end -/

end TriangleGame
