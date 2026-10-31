import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.Vocabulary
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.Base

open MeasureTheory
open Statlib.Imported
open scoped BigOperators

noncomputable section
open MeasureTheory
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_1445702134_3c8d3810 : (∀ (α : ℝ) (n : ℕ), 0 < α → 0 < risingFac α n) ∧
    (∀ (α : ℝ) (n : ℕ), 0 < α → α ^ n ≤ risingFac α n) ∧
    (∀ (α : ℝ) (n : ℕ), 0 < α → α ≤ 1 → 1 ≤ n →
      α * ((n - 1).factorial : ℝ) ≤ risingFac α n) ∧
    (∀ n : ℕ, MonotoneOn (fun α : ℝ => risingFac α n) (Set.Ioi (0 : ℝ))) ∧
    (∀ (n : ℕ) (α ε : ℝ), 0 < α → α ≤ ε → risingFac α n ≤ risingFac ε n) ∧
    (∀ (n : ℕ) (ε : ℝ), 0 < ε → 0 < risingFac ε n) ∧
    (∀ (n : ℕ), 1 ≤ n →
      (∀ α ∈ Set.Ioi (0 : ℝ), 0 < α / risingFac α n) ∧
        AntitoneOn (fun α : ℝ => α / risingFac α n) (Set.Ioi (0 : ℝ)) ∧
          (∀ α ∈ Set.Ioi (0 : ℝ),
            α / risingFac α n
              = 1 / Finset.prod (Finset.range (n - 1)) (fun j => α + ((j : ℝ) + 1)))) := by
  /- @proof-region region.target-node.session.08a9ff91bcaa653d begin -/
  have hpos : ∀ (α : ℝ) (n : ℕ), 0 < α → 0 < risingFac α n := by
    intro α n hα
    simp only [risingFac]
    exact Finset.prod_pos (fun k _ => by
      have hk : (0 : ℝ) ≤ (k : ℝ) := by positivity
      linarith)
  have hpow : ∀ (α : ℝ) (n : ℕ), 0 < α → α ^ n ≤ risingFac α n := by
    intro α n hα
    have h := Finset.prod_le_prod (s := Finset.range n) (f := fun _ : ℕ => α)
      (g := fun k : ℕ => α + (k : ℝ)) (fun _ _ => le_of_lt hα)
      (fun k _ => by
        have hk : (0 : ℝ) ≤ (k : ℝ) := by positivity
        linarith)
    simpa only [risingFac, Finset.prod_const, Finset.card_range] using h
  have hfac : ∀ m : ℕ, (∏ k ∈ Finset.range m, ((k : ℝ) + 1)) = (m.factorial : ℝ) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.prod_range_succ, ih, Nat.factorial_succ]
      push_cast
      ring
  have hsplit : ∀ (α : ℝ) (n : ℕ), 1 ≤ n →
      risingFac α n = α * ∏ j ∈ Finset.range (n - 1), (α + ((j : ℝ) + 1)) := by
    intro α n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    have h : risingFac α (m + 1) =
        (∏ k ∈ Finset.range m, (α + ((k : ℝ) + 1))) * α := by
      simp only [risingFac]
      rw [Finset.prod_range_succ']
      push_cast
      ring
    rw [h]
    ring
  have hfact : ∀ (α : ℝ) (n : ℕ), 0 < α → α ≤ 1 → 1 ≤ n →
      α * ((n - 1).factorial : ℝ) ≤ risingFac α n := by
    intro α n hα _ hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hrise : risingFac α (m + 1) =
        (∏ k ∈ Finset.range m, (α + ((k : ℝ) + 1))) * α := by
      simp only [risingFac]
      rw [Finset.prod_range_succ']
      push_cast
      ring
    have hle : (∏ k ∈ Finset.range m, ((k : ℝ) + 1))
        ≤ ∏ k ∈ Finset.range m, (α + ((k : ℝ) + 1)) :=
      Finset.prod_le_prod (fun k _ => by positivity) (fun k _ => by
        have hk : (0 : ℝ) ≤ (k : ℝ) := by positivity
        linarith)
    rw [Nat.add_sub_cancel, hrise, ← hfac m]
    calc α * (∏ k ∈ Finset.range m, ((k : ℝ) + 1))
        = (∏ k ∈ Finset.range m, ((k : ℝ) + 1)) * α := by ring
      _ ≤ (∏ k ∈ Finset.range m, (α + ((k : ℝ) + 1))) * α :=
          mul_le_mul_of_nonneg_right hle (le_of_lt hα)
  have hmono : ∀ (n : ℕ), MonotoneOn (fun α : ℝ => risingFac α n) (Set.Ioi (0 : ℝ)) := by
    intro n a ha b _ hab
    have ha0 : (0 : ℝ) < a := ha
    simp only [risingFac]
    exact Finset.prod_le_prod
      (fun k _ => by
        have hk : (0 : ℝ) ≤ (k : ℝ) := by positivity
        linarith)
      (fun k _ => by
        have hk : (0 : ℝ) ≤ (k : ℝ) := by positivity
        linarith)
  have hmono2 : ∀ (n : ℕ) (α ε : ℝ), 0 < α → α ≤ ε → risingFac α n ≤ risingFac ε n := by
    intro n α ε hα hαε
    exact hmono n hα (lt_of_lt_of_le hα hαε) hαε
  have hlast : ∀ (n : ℕ), 1 ≤ n →
      (∀ α ∈ Set.Ioi (0 : ℝ), 0 < α / risingFac α n) ∧
        AntitoneOn (fun α : ℝ => α / risingFac α n) (Set.Ioi (0 : ℝ)) ∧
          (∀ α ∈ Set.Ioi (0 : ℝ),
            α / risingFac α n
              = 1 / Finset.prod (Finset.range (n - 1)) (fun j => α + ((j : ℝ) + 1))) := by
    intro n hn
    have hPpos : ∀ α ∈ Set.Ioi (0 : ℝ),
        0 < ∏ j ∈ Finset.range (n - 1), (α + ((j : ℝ) + 1)) := by
      intro α hα
      have hα0 : (0 : ℝ) < α := hα
      exact Finset.prod_pos (fun j _ => by
        have hj : (0 : ℝ) ≤ (j : ℝ) := by positivity
        linarith)
    have hid : ∀ α ∈ Set.Ioi (0 : ℝ),
        α / risingFac α n = 1 / ∏ j ∈ Finset.range (n - 1), (α + ((j : ℝ) + 1)) := by
      intro α hα
      have hα0 : (0 : ℝ) < α := hα
      rw [hsplit α n hn]
      calc α / (α * ∏ j ∈ Finset.range (n - 1), (α + ((j : ℝ) + 1)))
          = (α / α) / ∏ j ∈ Finset.range (n - 1), (α + ((j : ℝ) + 1)) := by rw [div_div]
        _ = 1 / ∏ j ∈ Finset.range (n - 1), (α + ((j : ℝ) + 1)) := by
              rw [div_self (ne_of_gt hα0)]
    refine ⟨?_, ?_, hid⟩
    · intro α hα
      rw [hid α hα]
      exact div_pos one_pos (hPpos α hα)
    · intro a ha b hb hab
      have ha0 : (0 : ℝ) < a := ha
      have hPle : (∏ j ∈ Finset.range (n - 1), (a + ((j : ℝ) + 1)))
          ≤ ∏ j ∈ Finset.range (n - 1), (b + ((j : ℝ) + 1)) :=
        Finset.prod_le_prod (fun j _ => by
          have hj : (0 : ℝ) ≤ (j : ℝ) := by positivity
          linarith) (fun j _ => by
          have hj : (0 : ℝ) ≤ (j : ℝ) := by positivity
          linarith)
      change b / risingFac b n ≤ a / risingFac a n
      rw [hid a ha, hid b (lt_of_lt_of_le ha0 hab)]
      simp only [one_div]
      exact inv_anti₀ (hPpos a ha) hPle
  refine ⟨hpos, hpow, hfact, hmono, hmono2, fun n eps heps => hpos eps n heps, hlast⟩
  /- @proof-region region.target-node.session.08a9ff91bcaa653d end -/

end Statlib.Imported
end
