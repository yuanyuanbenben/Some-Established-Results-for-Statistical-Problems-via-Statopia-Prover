import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q19.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q19.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q19.ProvedNodes.Node_3007476390_3adea497_6be005ff

open Msc62GroundTruth

namespace Msc62GroundTruth

set_option autoImplicit false in
theorem statopia_math_node_3936285520_6207c28e : ∀ (n k : ℕ) (p : Fin k → ℝ) (hp_sum : (∑ c : Fin k, p c) = 1)
    (a b : Fin k) (hab : a ≠ b),
    (∑ x : Fin n → Fin k,
      (∏ t : Fin n, p (x t)) *
        (((∑ t : Fin n, if x t = a then (1 : ℕ) else 0) : ℕ) : ℝ) *
        (((∑ t : Fin n, if x t = b then (1 : ℕ) else 0) : ℕ) : ℝ))
      = ((n : ℝ) ^ 2 - (n : ℝ)) * p a * p b := by
  /- @proof-region region.target-node.session.ee9206968f94caa2 begin -/
  intro n k p hp_sum a b hab
  set c : ℝ := p a * p b with hc
  have hcastA : ∀ x : Fin n → Fin k,
      (((∑ t : Fin n, if x t = a then (1 : ℕ) else 0) : ℕ) : ℝ)
        = ∑ t : Fin n, (if x t = a then (1 : ℝ) else 0) := by
    intro x
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases h : x t = a <;> simp [h]
  have hcastB : ∀ x : Fin n → Fin k,
      (((∑ t : Fin n, if x t = b then (1 : ℕ) else 0) : ℕ) : ℝ)
        = ∑ t : Fin n, (if x t = b then (1 : ℝ) else 0) := by
    intro x
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases h : x t = b <;> simp [h]
  have hdiag : ∀ s : Fin n,
      (∑ x : Fin n → Fin k, (∏ u : Fin n, p (x u)) * (if x s = a then (1 : ℝ) else 0) *
        (if x s = b then (1 : ℝ) else 0)) = 0 := by
    intro s
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases hxa : x s = a
    · rw [hxa]
      simp [hab]
    · rw [if_neg hxa, mul_zero, zero_mul]
  have hoff : ∀ s t : Fin n, s ≠ t →
      (∑ x : Fin n → Fin k, (∏ u : Fin n, p (x u)) * (if x s = a then (1 : ℝ) else 0) *
        (if x t = b then (1 : ℝ) else 0)) = c := by
    intro s t hst
    rw [hc]
    exact statopia_math_node_3007476390_3adea497 n k p hp_sum s t hst a b
  have hinner : ∀ s : Fin n,
      (∑ t : Fin n, ∑ x : Fin n → Fin k, (∏ u : Fin n, p (x u)) *
        (if x s = a then (1 : ℝ) else 0) * (if x t = b then (1 : ℝ) else 0))
        = (n : ℝ) * c - c := by
    intro s
    have hpt : ∀ t : Fin n,
        (∑ x : Fin n → Fin k, (∏ u : Fin n, p (x u)) * (if x s = a then (1 : ℝ) else 0) *
          (if x t = b then (1 : ℝ) else 0)) = if s = t then (0 : ℝ) else c := by
      intro t
      by_cases h : s = t
      · simpa [h] using hdiag s
      · rw [if_neg h]
        exact hoff s t h
    have h1 : (∑ t : Fin n, (if s = t then (-c) else 0)) = -c := by
      rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ s)]
    have h2 : (∑ t : Fin n, c) = (n : ℝ) * c := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc
      (∑ t : Fin n, ∑ x : Fin n → Fin k, (∏ u : Fin n, p (x u)) *
          (if x s = a then (1 : ℝ) else 0) * (if x t = b then (1 : ℝ) else 0))
          = ∑ t : Fin n, (if s = t then (0 : ℝ) else c) :=
            Finset.sum_congr rfl fun t _ => hpt t
      _ = ∑ t : Fin n, ((if s = t then (-c) else 0) + c) := by
            refine Finset.sum_congr rfl fun t _ => ?_
            by_cases h : s = t <;> simp [h]
      _ = (-c) + (n : ℝ) * c := by
            rw [Finset.sum_add_distrib, h1, h2]
      _ = (n : ℝ) * c - c := by ring
  have houter : (∑ s : Fin n, ∑ t : Fin n, ∑ x : Fin n → Fin k, (∏ u : Fin n, p (x u)) *
      (if x s = a then (1 : ℝ) else 0) * (if x t = b then (1 : ℝ) else 0))
      = ((n : ℝ) ^ 2 - (n : ℝ)) * c := by
    calc
      (∑ s : Fin n, ∑ t : Fin n, ∑ x : Fin n → Fin k, (∏ u : Fin n, p (x u)) *
          (if x s = a then (1 : ℝ) else 0) * (if x t = b then (1 : ℝ) else 0))
          = ∑ s : Fin n, ((n : ℝ) * c - c) :=
            Finset.sum_congr rfl fun s _ => hinner s
      _ = ((n : ℝ) ^ 2 - (n : ℝ)) * c := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
  have hstep1 : ∀ x : Fin n → Fin k,
      (∏ u : Fin n, p (x u)) * (∑ s : Fin n, (if x s = a then (1 : ℝ) else 0))
        = ∑ s : Fin n, (∏ u : Fin n, p (x u)) * (if x s = a then (1 : ℝ) else 0) :=
    fun x => Finset.mul_sum Finset.univ (fun s : Fin n => (if x s = a then (1 : ℝ) else 0))
      (∏ u : Fin n, p (x u))
  have hstep2 : ∀ x : Fin n → Fin k,
      (∑ s : Fin n, (∏ u : Fin n, p (x u)) * (if x s = a then (1 : ℝ) else 0)) *
        (∑ t : Fin n, (if x t = b then (1 : ℝ) else 0))
        = ∑ s : Fin n, ((∏ u : Fin n, p (x u)) * (if x s = a then (1 : ℝ) else 0)) *
          (∑ t : Fin n, (if x t = b then (1 : ℝ) else 0)) :=
    fun x => Finset.sum_mul Finset.univ
      (fun s : Fin n => (∏ u : Fin n, p (x u)) * (if x s = a then (1 : ℝ) else 0))
      (∑ t : Fin n, (if x t = b then (1 : ℝ) else 0))
  have hstep3 : ∀ x : Fin n → Fin k, ∀ s : Fin n,
      ((∏ u : Fin n, p (x u)) * (if x s = a then (1 : ℝ) else 0)) *
        (∑ t : Fin n, (if x t = b then (1 : ℝ) else 0))
        = ∑ t : Fin n, (∏ u : Fin n, p (x u)) * (if x s = a then (1 : ℝ) else 0) *
          (if x t = b then (1 : ℝ) else 0) :=
    fun x s => Finset.mul_sum Finset.univ (fun t : Fin n => (if x t = b then (1 : ℝ) else 0))
      ((∏ u : Fin n, p (x u)) * (if x s = a then (1 : ℝ) else 0))
  calc
    (∑ x : Fin n → Fin k,
      (∏ t : Fin n, p (x t)) *
        (((∑ t : Fin n, if x t = a then (1 : ℕ) else 0) : ℕ) : ℝ) *
        (((∑ t : Fin n, if x t = b then (1 : ℕ) else 0) : ℕ) : ℝ))
        = ∑ x : Fin n → Fin k, (∏ u : Fin n, p (x u)) *
            (∑ s : Fin n, (if x s = a then (1 : ℝ) else 0)) *
            (∑ t : Fin n, (if x t = b then (1 : ℝ) else 0)) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [hcastA x, hcastB x]
    _ = ∑ x : Fin n → Fin k, ∑ s : Fin n, ∑ t : Fin n, (∏ u : Fin n, p (x u)) *
          (if x s = a then (1 : ℝ) else 0) * (if x t = b then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [hstep1 x, hstep2 x]
          exact Finset.sum_congr rfl fun s _ => hstep3 x s
    _ = ∑ s : Fin n, ∑ x : Fin n → Fin k, ∑ t : Fin n, (∏ u : Fin n, p (x u)) *
          (if x s = a then (1 : ℝ) else 0) * (if x t = b then (1 : ℝ) else 0) :=
          Finset.sum_comm
    _ = ∑ s : Fin n, ∑ t : Fin n, ∑ x : Fin n → Fin k, (∏ u : Fin n, p (x u)) *
          (if x s = a then (1 : ℝ) else 0) * (if x t = b then (1 : ℝ) else 0) :=
          Finset.sum_congr rfl fun s _ => Finset.sum_comm
    _ = ((n : ℝ) ^ 2 - (n : ℝ)) * c := houter
    _ = ((n : ℝ) ^ 2 - (n : ℝ)) * p a * p b := by
          rw [hc]
          ring
  /- @proof-region region.target-node.session.ee9206968f94caa2 end -/

end Msc62GroundTruth
