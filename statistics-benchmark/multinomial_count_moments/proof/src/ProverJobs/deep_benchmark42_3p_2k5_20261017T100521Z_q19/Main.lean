import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q19.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q19.ProvedNodes
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q19.Base

namespace Msc62GroundTruth

theorem multinomial_count_moments
    (n k : ℕ) (hk : 1 ≤ k)
    (p : Fin k → ℝ)
    (hp_nonneg : ∀ a, 0 ≤ p a)
    (hp_sum : (∑ a : Fin k, p a) = 1) :
    let count : Fin k → (Fin n → Fin k) → ℕ :=
      fun c x => ∑ t : Fin n, if x t = c then (1 : ℕ) else 0
    let mass : (Fin n → Fin k) → ℝ :=
      fun x => ∏ t : Fin n, p (x t)
    (∀ a : Fin k,
      (∑ x : Fin n → Fin k, mass x * (count a x : ℝ)) =
          (n : ℝ) * p a ∧
      (∑ x : Fin n → Fin k,
        mass x * ((count a x : ℝ) - (n : ℝ) * p a) ^ 2) =
          (n : ℝ) * p a * (1 - p a)) ∧
    (∀ a b : Fin k, a ≠ b →
      (∑ x : Fin n → Fin k,
        mass x *
          (((count a x : ℝ) - (n : ℝ) * p a) *
            ((count b x : ℝ) - (n : ℝ) * p b))) =
          -((n : ℝ) * p a * p b))
:= by
  /- @proof-region region.root.7d65a92462e1 begin -/
  dsimp only
  have hcast : ∀ (c : Fin k) (x : Fin n → Fin k),
      (((∑ t : Fin n, if x t = c then (1 : ℕ) else 0) : ℕ) : ℝ) =
        ∑ t : Fin n, if x t = c then (1 : ℝ) else 0 := by
    intro c x
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [Nat.cast_ite]
    by_cases h : x t = c <;> simp [h]
  have hmass : (∑ x : Fin n → Fin k, ∏ t : Fin n, p (x t)) = 1 := by
    have h := statopia_math_node_887293322_4a71d68e n k (fun (_ : Fin n) (c : Fin k) => p c)
    simpa [hp_sum] using h
  constructor
  · intro a
    refine ⟨?_, ?_⟩
    · simpa [hcast] using statopia_math_node_1296899899_966815e7 n k p hp_sum a
    · have h1 : (∑ x : Fin n → Fin k,
          (∏ t : Fin n, p (x t)) *
            (((∑ t : Fin n, if x t = a then (1 : ℕ) else 0) : ℕ) : ℝ)) =
          (n : ℝ) * p a := by
        simpa [hcast] using statopia_math_node_1296899899_966815e7 n k p hp_sum a
      have h2 : (∑ x : Fin n → Fin k,
          (∏ t : Fin n, p (x t)) *
            (((∑ t : Fin n, if x t = a then (1 : ℕ) else 0) : ℕ) : ℝ) ^ 2) =
          (n : ℝ) * p a + ((n : ℝ) ^ 2 - (n : ℝ)) * (p a) ^ 2 :=
        statopia_math_node_1473221386_3b189d61 n k p hp_sum a
      have key : (∑ x : Fin n → Fin k,
          (∏ t : Fin n, p (x t)) *
            (((((∑ t : Fin n, if x t = a then (1 : ℕ) else 0) : ℕ) : ℝ) - (n : ℝ) * p a) ^ 2)) =
          (∑ x : Fin n → Fin k,
            (∏ t : Fin n, p (x t)) *
              (((∑ t : Fin n, if x t = a then (1 : ℕ) else 0) : ℕ) : ℝ) ^ 2) +
          (-(2 * ((n : ℝ) * p a))) *
            (∑ x : Fin n → Fin k,
              (∏ t : Fin n, p (x t)) *
                (((∑ t : Fin n, if x t = a then (1 : ℕ) else 0) : ℕ) : ℝ)) +
          ((n : ℝ) * p a) ^ 2 * (∑ x : Fin n → Fin k, ∏ t : Fin n, p (x t)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x _
        ring
      rw [key, h2, h1, hmass]
      ring
  · intro a b hab
    have h1a : (∑ x : Fin n → Fin k,
          (∏ t : Fin n, p (x t)) *
            (((∑ t : Fin n, if x t = a then (1 : ℕ) else 0) : ℕ) : ℝ)) =
          (n : ℝ) * p a := by
        simpa [hcast] using statopia_math_node_1296899899_966815e7 n k p hp_sum a
    have h1b : (∑ x : Fin n → Fin k,
          (∏ t : Fin n, p (x t)) *
            (((∑ t : Fin n, if x t = b then (1 : ℕ) else 0) : ℕ) : ℝ)) =
          (n : ℝ) * p b := by
        simpa [hcast] using statopia_math_node_1296899899_966815e7 n k p hp_sum b
    have h2 : (∑ x : Fin n → Fin k,
          (∏ t : Fin n, p (x t)) *
            (((∑ t : Fin n, if x t = a then (1 : ℕ) else 0) : ℕ) : ℝ) *
            (((∑ t : Fin n, if x t = b then (1 : ℕ) else 0) : ℕ) : ℝ)) =
          ((n : ℝ) ^ 2 - (n : ℝ)) * p a * p b :=
        statopia_math_node_3936285520_6207c28e n k p hp_sum a b hab
    have key : (∑ x : Fin n → Fin k,
          (∏ t : Fin n, p (x t)) *
            (((((∑ t : Fin n, if x t = a then (1 : ℕ) else 0) : ℕ) : ℝ) - (n : ℝ) * p a) *
              ((((∑ t : Fin n, if x t = b then (1 : ℕ) else 0) : ℕ) : ℝ) - (n : ℝ) * p b))) =
          (∑ x : Fin n → Fin k,
            (∏ t : Fin n, p (x t)) *
              (((∑ t : Fin n, if x t = a then (1 : ℕ) else 0) : ℕ) : ℝ) *
              (((∑ t : Fin n, if x t = b then (1 : ℕ) else 0) : ℕ) : ℝ)) -
          ((n : ℝ) * p b) *
            (∑ x : Fin n → Fin k,
              (∏ t : Fin n, p (x t)) *
                (((∑ t : Fin n, if x t = a then (1 : ℕ) else 0) : ℕ) : ℝ)) -
          ((n : ℝ) * p a) *
            (∑ x : Fin n → Fin k,
              (∏ t : Fin n, p (x t)) *
                (((∑ t : Fin n, if x t = b then (1 : ℕ) else 0) : ℕ) : ℝ)) +
          (((n : ℝ) * p a) * ((n : ℝ) * p b)) *
            (∑ x : Fin n → Fin k, ∏ t : Fin n, p (x t)) := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x _
        ring
    rw [key, h2, h1a, h1b, hmass]
    ring
  /- @proof-region region.root.7d65a92462e1 end -/

end Msc62GroundTruth
