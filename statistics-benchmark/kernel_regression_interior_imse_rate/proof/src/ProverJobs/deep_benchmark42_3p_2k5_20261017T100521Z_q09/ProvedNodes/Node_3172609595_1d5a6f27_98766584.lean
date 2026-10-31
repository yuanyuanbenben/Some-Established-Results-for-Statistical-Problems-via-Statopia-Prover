import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q09.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q09.Base

open MeasureTheory ProbabilityTheory
open Msc62GroundTruth

open MeasureTheory ProbabilityTheory
namespace Msc62GroundTruth

set_option autoImplicit false in
theorem statopia_math_node_3172609595_1d5a6f27 : ∀ (d : ℕ) (alpha : ℝ) (halpha : 0 < alpha) (n : ℕ) (hn : 1 ≤ n),
    let h : ℝ := Real.rpow (n : ℝ) (-1 / (2 * alpha + (d : ℝ)))
    1 / ((n : ℝ) * h ^ d) = Real.rpow h (2 * alpha) ∧
      1 / ((n : ℝ) * h ^ d) =
        Real.rpow (n : ℝ) (-2 * alpha / (2 * alpha + (d : ℝ))) ∧
      Real.rpow h (2 * alpha) =
        Real.rpow (n : ℝ) (-2 * alpha / (2 * alpha + (d : ℝ))) := by
  /- @proof-region region.target-node.session.109a114e78d8ddca begin -/
  intro d alpha halpha n hn
  dsimp only
  have hpow : ∀ (x y : ℝ), Real.rpow x y = x ^ y := fun x y => rfl
  rw [hpow]
  set A : ℝ := 2 * alpha + (d : ℝ) with hA
  have hApos : 0 < A := by
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    rw [hA]
    linarith
  have hAne : A ≠ 0 := ne_of_gt hApos
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  set h : ℝ := (n : ℝ) ^ (-1 / A) with hh
  have hd : h ^ d = (n : ℝ) ^ ((-1 / A) * (d : ℝ)) := by
    rw [← Real.rpow_natCast h d, hh, ← Real.rpow_mul (le_of_lt hnpos)]
  have hA2 : 1 + (-1 / A) * (d : ℝ) = 2 * alpha / A := by
    have hsub : 2 * alpha = A - (d : ℝ) := by linarith
    rw [hsub, sub_div, div_self hAne]
    ring
  have hexp1 : -(2 * alpha / A) = -2 * alpha / A := by ring
  have hexp2 : (-1 / A) * (2 * alpha) = -2 * alpha / A := by ring
  have hmul : (n : ℝ) * h ^ d = (n : ℝ) ^ (2 * alpha / A) := by
    have hstep : (n : ℝ) ^ (1 + (-1 / A) * (d : ℝ)) =
        (n : ℝ) * (n : ℝ) ^ ((-1 / A) * (d : ℝ)) := by
      have h' := Real.rpow_add hnpos 1 ((-1 / A) * (d : ℝ))
      rw [Real.rpow_one] at h'
      exact h'
    rw [hA2] at hstep
    rw [hd, ← hstep]
  have h1 : 1 / ((n : ℝ) * h ^ d) = (n : ℝ) ^ (-2 * alpha / A) := by
    rw [one_div, hmul, ← Real.rpow_neg (le_of_lt hnpos), hexp1]
  have h3 : h ^ (2 * alpha) = (n : ℝ) ^ (-2 * alpha / A) := by
    rw [hh, ← Real.rpow_mul (le_of_lt hnpos), hexp2]
  exact ⟨h1.trans h3.symm, h1, h3⟩
  /- @proof-region region.target-node.session.109a114e78d8ddca end -/

end Msc62GroundTruth
