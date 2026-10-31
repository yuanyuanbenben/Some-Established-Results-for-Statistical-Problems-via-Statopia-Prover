import ProverJobs.real_V_eq_15312944933b.Vocabulary
import ProverJobs.real_V_eq_15312944933b.Base
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_1642795503_352290b3_4ab74713
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_4092604145_3ac20b10_9427093c
open scoped BigOperators
open LiuBangXiangYu

open scoped BigOperators
namespace LiuBangXiangYu

set_option autoImplicit false in
theorem statopia_math_node_1733068511_28bb1d76 : ∀ (β : Type) [Fintype β] [DecidableEq β]
    (K : ℕ) (a b : Fin K → β) (fL fR : Fin K → ℝ)
    (W : β → ℝ) (lab : β → ℕ) (D : ℝ)
    (h1 : ∃ u : β, W u ≠ 0)
    (h2 : ∀ u : β, (∑ e ∈ Finset.univ.filter (fun e : Fin K => a e = u), fL e)
        + (∑ e ∈ Finset.univ.filter (fun e : Fin K => b e = u), fR e) = W u)
    (h3 : ∀ u : β, W u ≠ 0 → W u = (2 : ℝ) ^ (lab u))
    (h4 : ∀ u v : β, W u ≠ 0 → W v ≠ 0 → lab u = lab v → u = v)
    (h5 : ∀ u : β, ∃ e : Fin K, a e = u ∨ b e = u)
    (h6 : (Finset.univ.filter (fun u : β => W u = 0)).card ≤ 1)
    (h7 : K ≤ Fintype.card β - 1)
    (h8 : (∑ e : Fin K, |fL e - fR e|) ≤ D),
    1 ≤ D := by
  /- @proof-region region.target-node.session.16641457769e3142 begin -/
  intro β _ _ K a b fL fR W lab D h1 h2 h3 h4 h5 h6 h7 h8
  have hkey : ∃ S : Finset β, S.Nonempty ∧ (∃ u ∈ S, W u ≠ 0) ∧
      (∀ e : Fin K, (a e ∈ S ↔ b e ∈ S)) ∧
      ∃ ε : β → ℝ, (∀ u ∈ S, ε u = 1 ∨ ε u = -1) ∧ (∀ u ∉ S, ε u = 0) ∧
        (∀ e : Fin K, a e ∈ S → a e ≠ b e ∧ ε (a e) ≠ ε (b e)) := by
    exact statopia_math_node_1642795503_352290b3 β K a b W h1 h5 h6 h7
  obtain ⟨S, hSne, hSreal, hclosed, ε, hεS, hεout, hεprop⟩ := hkey
  have hflip : ∀ e : Fin K, ε (b e) = - ε (a e) := by
    intro e
    by_cases ha : a e ∈ S
    · obtain ⟨hne, hdiff⟩ := hεprop e ha
      have hb : b e ∈ S := (hclosed e).mp ha
      rcases hεS (a e) ha with h2 | h2 <;> rcases hεS (b e) hb with h1 | h1
      · exfalso; rw [h1, h2] at hdiff; exact hdiff rfl
      · rw [h1, h2] <;> norm_num
      · rw [h1, h2] <;> norm_num
      · exfalso; rw [h1, h2] at hdiff; exact hdiff rfl
    · have hb : b e ∉ S := fun h => ha ((hclosed e).mpr h)
      rw [hεout (b e) hb, hεout (a e) ha]; ring
  have hA : (∑ u ∈ S, ε u * W u) = ∑ e : Fin K, ε (a e) * (fL e - fR e) := by
    have hite : ∀ (s : Finset β) (p : β) (c : ℝ),
        (∑ x ∈ s, (if p = x then c else 0)) = (if p ∈ s then c else 0) := by
      intro s p c
      have hflip : (∑ x ∈ s, (if p = x then c else 0))
          = (∑ x ∈ s, (if x = p then c else 0)) := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases h : p = x
        · rw [if_pos h, if_pos h.symm]
        · rw [if_neg h, if_neg (fun hh => h hh.symm)]
      rw [hflip, Finset.sum_ite_eq']
    have hfib_a : (∑ u ∈ S, ∑ e with a e = u, ε u * fL e)
        = ∑ e : Fin K, if a e ∈ S then ε (a e) * fL e else 0 := by
      have hstep : ∀ u : β, (∑ e with a e = u, ε u * fL e)
          = ∑ e ∈ Finset.univ, if a e = u then ε (a e) * fL e else 0 := by
        intro u
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro e _
        by_cases h : a e = u
        · rw [if_pos h, if_pos h, ← h]
        · rw [if_neg h, if_neg h]
      simp_rw [hstep]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      rw [hite S (a e) (ε (a e) * fL e)]
    have hfib_b : (∑ u ∈ S, ∑ e with b e = u, ε u * fR e)
        = ∑ e : Fin K, if b e ∈ S then ε (b e) * fR e else 0 := by
      have hstep : ∀ u : β, (∑ e with b e = u, ε u * fR e)
          = ∑ e ∈ Finset.univ, if b e = u then ε (b e) * fR e else 0 := by
        intro u
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro e _
        by_cases h : b e = u
        · rw [if_pos h, if_pos h, ← h]
        · rw [if_neg h, if_neg h]
      simp_rw [hstep]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      rw [hite S (b e) (ε (b e) * fR e)]
    have h1' : (∑ u ∈ S, ε u * W u)
        = (∑ u ∈ S, ∑ e with a e = u, ε u * fL e)
          + (∑ u ∈ S, ∑ e with b e = u, ε u * fR e) := by
      have hterm : ∀ u : β, ε u * W u
          = (∑ e with a e = u, ε u * fL e) + (∑ e with b e = u, ε u * fR e) := by
        intro u
        rw [← h2 u, mul_add]
        simp only [Finset.mul_sum]
      simp_rw [hterm]
      rw [Finset.sum_add_distrib]
    rw [h1', hfib_a, hfib_b, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hae : a e ∈ S
    · have hbe : b e ∈ S := (hclosed e).mp hae
      rw [if_pos hae, if_pos hbe, hflip e]
      ring
    · have hbe : b e ∉ S := fun h => hae ((hclosed e).mpr h)
      rw [if_neg hae, if_neg hbe, hεout (a e) hae]
      ring
  have hub : |∑ u ∈ S, ε u * W u| ≤ ∑ e : Fin K, |fL e - fR e| := by
    rw [hA]
    calc |∑ e : Fin K, ε (a e) * (fL e - fR e)|
        ≤ ∑ e : Fin K, |ε (a e) * (fL e - fR e)| := by
          rw [abs_le]
          constructor
          · rw [← Finset.sum_neg_distrib]
            apply Finset.sum_le_sum
            intro e _
            exact neg_abs_le _
          · apply Finset.sum_le_sum
            intro e _
            exact le_abs_self _
      _ ≤ ∑ e : Fin K, |fL e - fR e| := by
          apply Finset.sum_le_sum
          intro e _
          rw [abs_mul]
          have h1 : |ε (a e)| ≤ 1 := by
            by_cases ha : a e ∈ S
            · rcases hεS (a e) ha with h | h <;> rw [h] <;> norm_num
            · rw [hεout (a e) ha]; norm_num
          calc |ε (a e)| * |fL e - fR e| ≤ 1 * |fL e - fR e| :=
                mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
            _ = |fL e - fR e| := one_mul _
  have hlow : 1 ≤ |∑ u ∈ S, ε u * W u| :=
    statopia_math_node_4092604145_3ac20b10 β W lab S ε hSreal h3 h4 hεS
  linarith [hub, h8, hlow]
  /- @proof-region region.target-node.session.16641457769e3142 end -/

end LiuBangXiangYu
