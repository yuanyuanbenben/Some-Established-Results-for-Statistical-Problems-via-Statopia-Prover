import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q19.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q19.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q19.ProvedNodes.Node_1004106233_18e3d102_94116a57
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q19.ProvedNodes.Node_3007476390_3adea497_6be005ff


open Msc62GroundTruth

namespace Msc62GroundTruth

set_option autoImplicit false in
theorem statopia_math_node_1473221386_3b189d61 : ∀ (n k : ℕ) (p : Fin k → ℝ)
    (hp_sum : (∑ c : Fin k, p c) = 1) (a : Fin k),
    (∑ x : Fin n → Fin k,
        (∏ t : Fin n, p (x t)) *
          (((∑ t : Fin n, if x t = a then (1 : ℕ) else 0) : ℕ) : ℝ) ^ 2) =
      (n : ℝ) * p a + ((n : ℝ) ^ 2 - (n : ℝ)) * (p a) ^ 2 := by
  /- @proof-region region.target-node.session.6a0dda4580f247d9 begin -/
  intro n k p hp_sum a
  have hcast : ∀ x : Fin n → Fin k,
      (((∑ t : Fin n, if x t = a then (1 : ℕ) else 0) : ℕ) : ℝ)
        = ∑ t : Fin n, (if x t = a then (1 : ℝ) else 0) := by
    intro x
    simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  have hexpand : ∀ x : Fin n → Fin k,
      (∏ u : Fin n, p (x u)) * (∑ t : Fin n, (if x t = a then (1 : ℝ) else 0)) ^ 2
        = ∑ s : Fin n, ∑ t : Fin n, (∏ u : Fin n, p (x u)) *
            (if x s = a then (1 : ℝ) else 0) * (if x t = a then (1 : ℝ) else 0) := by
    intro x
    calc (∏ u : Fin n, p (x u)) * (∑ t : Fin n, (if x t = a then (1 : ℝ) else 0)) ^ 2
        = (∏ u : Fin n, p (x u)) * ((∑ t : Fin n, (if x t = a then (1 : ℝ) else 0)) *
            (∑ t : Fin n, (if x t = a then (1 : ℝ) else 0))) := by rw [pow_two]
      _ = (∏ u : Fin n, p (x u)) * (∑ s : Fin n, ∑ t : Fin n,
            (if x s = a then (1 : ℝ) else 0) * (if x t = a then (1 : ℝ) else 0)) := by
            rw [Fintype.sum_mul_sum]
      _ = ∑ s : Fin n, (∏ u : Fin n, p (x u)) * (∑ t : Fin n,
            (if x s = a then (1 : ℝ) else 0) * (if x t = a then (1 : ℝ) else 0)) := by
            conv_lhs => rw [Finset.mul_sum]
      _ = ∑ s : Fin n, ∑ t : Fin n, (∏ u : Fin n, p (x u)) *
            (if x s = a then (1 : ℝ) else 0) * (if x t = a then (1 : ℝ) else 0) := by
            refine Finset.sum_congr rfl fun s _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun t _ => ?_
            rw [← mul_assoc]
  have hGdiag : ∀ s : Fin n,
      (∑ x : Fin n → Fin k, (∏ u : Fin n, p (x u)) *
        (if x s = a then (1 : ℝ) else 0) * (if x s = a then (1 : ℝ) else 0)) = p a := by
    intro s
    have hsq : (∑ x : Fin n → Fin k, (∏ u : Fin n, p (x u)) *
        (if x s = a then (1 : ℝ) else 0) * (if x s = a then (1 : ℝ) else 0))
        = ∑ x : Fin n → Fin k, (∏ u : Fin n, p (x u)) * (if x s = a then (1 : ℝ) else 0) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases h : x s = a
      · simp [h]
      · simp [h]
    rw [hsq]
    exact statopia_math_node_1004106233_18e3d102 n k p hp_sum s a
  have hGoff : ∀ s t : Fin n, s ≠ t →
      (∑ x : Fin n → Fin k, (∏ u : Fin n, p (x u)) *
        (if x s = a then (1 : ℝ) else 0) * (if x t = a then (1 : ℝ) else 0)) = p a * p a := by
    intro s t hst
    exact statopia_math_node_3007476390_3adea497 n k p hp_sum s t hst a a
  have hrow : ∀ s : Fin n,
      (∑ t : Fin n, ∑ x : Fin n → Fin k, (∏ u : Fin n, p (x u)) *
        (if x s = a then (1 : ℝ) else 0) * (if x t = a then (1 : ℝ) else 0))
        = (n : ℝ) * (p a * p a) + (p a - p a * p a) := by
    intro s
    have hpt : ∀ t : Fin n,
        (∑ x : Fin n → Fin k, (∏ u : Fin n, p (x u)) *
          (if x s = a then (1 : ℝ) else 0) * (if x t = a then (1 : ℝ) else 0))
          = p a * p a + (if s = t then (p a - p a * p a) else 0) := by
      intro t
      by_cases h : s = t
      · rw [if_pos h, h, hGdiag t]
        ring
      · rw [if_neg h, hGoff s t h]
        ring
    calc (∑ t : Fin n, ∑ x : Fin n → Fin k, (∏ u : Fin n, p (x u)) *
            (if x s = a then (1 : ℝ) else 0) * (if x t = a then (1 : ℝ) else 0))
        = ∑ t : Fin n, (p a * p a + (if s = t then (p a - p a * p a) else 0)) :=
            Finset.sum_congr rfl fun t _ => hpt t
      _ = ∑ t : Fin n, (p a * p a) + ∑ t : Fin n, (if s = t then (p a - p a * p a) else 0) :=
            Finset.sum_add_distrib
      _ = (n : ℝ) * (p a * p a) + (p a - p a * p a) := by
            have h1 : (∑ t : Fin n, (if s = t then (p a - p a * p a) else 0))
                = p a - p a * p a := by
              rw [Finset.sum_ite_eq]
              simp
            have h2 : (∑ t : Fin n, (p a * p a)) = (n : ℝ) * (p a * p a) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            rw [h2, h1]
  have hmain : (∑ x : Fin n → Fin k, (∏ t : Fin n, p (x t)) *
        (((∑ t : Fin n, if x t = a then (1 : ℕ) else 0) : ℕ) : ℝ) ^ 2)
      = ∑ s : Fin n, ∑ t : Fin n, ∑ x : Fin n → Fin k, (∏ u : Fin n, p (x u)) *
          (if x s = a then (1 : ℝ) else 0) * (if x t = a then (1 : ℝ) else 0) := by
    calc (∑ x : Fin n → Fin k, (∏ t : Fin n, p (x t)) *
          (((∑ t : Fin n, if x t = a then (1 : ℕ) else 0) : ℕ) : ℝ) ^ 2)
        = ∑ x : Fin n → Fin k, (∏ t : Fin n, p (x t)) *
            (∑ t : Fin n, (if x t = a then (1 : ℝ) else 0)) ^ 2 := by
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [hcast x]
      _ = ∑ x : Fin n → Fin k, ∑ s : Fin n, ∑ t : Fin n, (∏ u : Fin n, p (x u)) *
            (if x s = a then (1 : ℝ) else 0) * (if x t = a then (1 : ℝ) else 0) := by
            refine Finset.sum_congr rfl fun x _ => ?_
            exact hexpand x
      _ = ∑ s : Fin n, ∑ x : Fin n → Fin k, ∑ t : Fin n, (∏ u : Fin n, p (x u)) *
            (if x s = a then (1 : ℝ) else 0) * (if x t = a then (1 : ℝ) else 0) :=
            Finset.sum_comm
      _ = ∑ s : Fin n, ∑ t : Fin n, ∑ x : Fin n → Fin k, (∏ u : Fin n, p (x u)) *
            (if x s = a then (1 : ℝ) else 0) * (if x t = a then (1 : ℝ) else 0) := by
            refine Finset.sum_congr rfl fun s _ => ?_
            exact Finset.sum_comm
  have hconstSum : (∑ s : Fin n, ((n : ℝ) * (p a * p a) + (p a - p a * p a)))
      = (n : ℝ) * ((n : ℝ) * (p a * p a) + (p a - p a * p a)) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hfinal : (∑ s : Fin n, ∑ t : Fin n, ∑ x : Fin n → Fin k, (∏ u : Fin n, p (x u)) *
        (if x s = a then (1 : ℝ) else 0) * (if x t = a then (1 : ℝ) else 0))
      = (n : ℝ) * p a + ((n : ℝ) ^ 2 - (n : ℝ)) * (p a) ^ 2 := by
    calc (∑ s : Fin n, ∑ t : Fin n, ∑ x : Fin n → Fin k, (∏ u : Fin n, p (x u)) *
            (if x s = a then (1 : ℝ) else 0) * (if x t = a then (1 : ℝ) else 0))
        = ∑ s : Fin n, ((n : ℝ) * (p a * p a) + (p a - p a * p a)) :=
            Finset.sum_congr rfl fun s _ => hrow s
      _ = (n : ℝ) * ((n : ℝ) * (p a * p a) + (p a - p a * p a)) := hconstSum
      _ = (n : ℝ) * p a + ((n : ℝ) ^ 2 - (n : ℝ)) * (p a) ^ 2 := by ring
  rw [hmain]
  exact hfinal

  /- @proof-region region.target-node.session.6a0dda4580f247d9 end -/

end Msc62GroundTruth
