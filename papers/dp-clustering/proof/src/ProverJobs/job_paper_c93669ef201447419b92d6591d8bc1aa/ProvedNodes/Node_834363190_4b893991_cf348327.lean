import ProverJobs.job_paper_c93669ef201447419b92d6591d8bc1aa.Vocabulary
import ProverJobs.job_paper_c93669ef201447419b92d6591d8bc1aa.Base

open Statlib.Imported
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators

namespace Statlib.Imported
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators

set_option autoImplicit false in
theorem statopia_math_node_834363190_4b893991 : ∀ (t : ℕ) (ht : 1 ≤ t) (c : ℝ) (hc : 0 < c) (θstar : Fin t → ℝ)
    {Ω : Type} (X : ℕ → Ω → ℝ) (n : ℕ) (j : Fin t) (ω : Ω)
    (hnj : 1 ≤ windowCount X θstar c n j ω),
    (windowIdx X θstar c n j ω ⊆ Finset.range n) ∧
    (∀ i ∈ windowIdx X θstar c n j ω,
      θstar j - c ≤ X i ω ∧ X i ω ≤ θstar j + c ∧
        (X i ω - θstar j ∈ Set.Icc (-c) c)) ∧
    windowCount X θstar c n j ω ≤ n ∧
    (upperOrderStat X θstar c n j ω ≤ θstar j + c ∧
      θstar j - c ≤ lowerOrderStat X θstar c n j ω) ∧
    (0 ≤ c + θstar j - upperOrderStat X θstar c n j ω ∧
      0 ≤ min (c + θstar j - upperOrderStat X θstar c n j ω)
        (1 / ((windowCount X θstar c n j ω : ℕ) : ℝ)) ∧
      min (c + θstar j - upperOrderStat X θstar c n j ω)
          (1 / ((windowCount X θstar c n j ω : ℕ) : ℝ))
        ≤ c + θstar j - upperOrderStat X θstar c n j ω ∧
      min (c + θstar j - upperOrderStat X θstar c n j ω)
          (1 / ((windowCount X θstar c n j ω : ℕ) : ℝ))
        ≤ 1 / ((windowCount X θstar c n j ω : ℕ) : ℝ) ∧
      ((windowCount X θstar c n j ω : ℕ) : ℝ) *
          min (c + θstar j - upperOrderStat X θstar c n j ω)
            (1 / ((windowCount X θstar c n j ω : ℕ) : ℝ)) ≤ 1) := by
  /- @proof-region region.target-node.session.bd4ea4e834bfc03c begin -/
  intro t ht c hc θstar Ω X n j ω hnj
  classical
  have hmem : ∀ i : ℕ, i ∈ windowIdx X θstar c n j ω ↔
      i ∈ Finset.range n ∧ X i ω ∈ Set.Icc (θstar j - c) (θstar j + c) := by
    intro i
    unfold windowIdx
    exact Finset.mem_filter
  have hsub : windowIdx X θstar c n j ω ⊆ Finset.range n := by
    intro i hi
    exact ((hmem i).mp hi).1
  have hwin : ∀ i ∈ windowIdx X θstar c n j ω,
      θstar j - c ≤ X i ω ∧ X i ω ≤ θstar j + c ∧ X i ω - θstar j ∈ Set.Icc (-c) c := by
    intro i hi
    obtain ⟨hlo, hhi⟩ := Set.mem_Icc.mp (((hmem i).mp hi).2)
    refine ⟨hlo, hhi, ?_⟩
    simp only [Set.mem_Icc]
    exact ⟨by linarith, by linarith⟩
  have hWC : windowCount X θstar c n j ω = (windowIdx X θstar c n j ω).card := rfl
  have hcount : windowCount X θstar c n j ω ≤ n := by
    rw [hWC]
    calc (windowIdx X θstar c n j ω).card ≤ (Finset.range n).card := Finset.card_le_card hsub
      _ = n := Finset.card_range n
  have hne : (windowIdx X θstar c n j ω).Nonempty := by
    rw [← Finset.card_pos, ← hWC]
    exact lt_of_lt_of_le Nat.zero_lt_one hnj
  obtain ⟨i0, hi0⟩ := hne
  have hSne : Set.Nonempty ((fun i => X i ω) '' ((windowIdx X θstar c n j ω : Finset ℕ) : Set ℕ)) :=
    ⟨X i0 ω, i0, by simpa using hi0, rfl⟩
  have hupper : upperOrderStat X θstar c n j ω ≤ θstar j + c := by
    unfold upperOrderStat
    exact csSup_le hSne (by
      rintro y ⟨i, hi, rfl⟩
      obtain ⟨-, hhi⟩ := Set.mem_Icc.mp (((hmem i).mp (by simpa using hi)).2)
      exact hhi)
  have hlower : θstar j - c ≤ lowerOrderStat X θstar c n j ω := by
    unfold lowerOrderStat
    exact le_csInf hSne (by
      rintro y ⟨i, hi, rfl⟩
      obtain ⟨hlo, -⟩ := Set.mem_Icc.mp (((hmem i).mp (by simpa using hi)).2)
      exact hlo)
  have hA : 0 ≤ c + θstar j - upperOrderStat X θstar c n j ω := by linarith
  have hnjge : (1 : ℝ) ≤ ((windowCount X θstar c n j ω : ℕ) : ℝ) := by exact_mod_cast hnj
  have hpos : (0 : ℝ) < ((windowCount X θstar c n j ω : ℕ) : ℝ) := by linarith
  have hinv : 0 ≤ 1 / ((windowCount X θstar c n j ω : ℕ) : ℝ) :=
    div_nonneg (by norm_num) (le_of_lt hpos)
  refine ⟨hsub, hwin, hcount, ⟨hupper, hlower⟩, hA, le_min hA hinv,
    min_le_left _ _, min_le_right _ _, ?_⟩
  have hstep : ((windowCount X θstar c n j ω : ℕ) : ℝ) *
      min (c + θstar j - upperOrderStat X θstar c n j ω)
        (1 / ((windowCount X θstar c n j ω : ℕ) : ℝ))
      ≤ ((windowCount X θstar c n j ω : ℕ) : ℝ) *
        (1 / ((windowCount X θstar c n j ω : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_left (min_le_right _ _) (le_of_lt hpos)
  have hone : ((windowCount X θstar c n j ω : ℕ) : ℝ) *
      (1 / ((windowCount X θstar c n j ω : ℕ) : ℝ)) = 1 := by
    rw [mul_one_div, div_self (ne_of_gt hpos)]
  linarith
  /- @proof-region region.target-node.session.bd4ea4e834bfc03c end -/

end Statlib.Imported
