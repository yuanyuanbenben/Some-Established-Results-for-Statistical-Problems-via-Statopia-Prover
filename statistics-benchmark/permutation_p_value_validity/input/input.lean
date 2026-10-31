import Mathlib

namespace Msc62GroundTruth

/--
For a finite permutation orbit, the upper-tail permutation p-value is
superuniform on the grid. The statement includes both the finite count form and
the equivalent uniform-probability form from the LaTeX input.
-/
theorem permutation_p_value_validity
    (N : ℕ) (hN : 1 ≤ N) (T : Fin N → ℝ) :
    let tailCount : Fin N → ℕ :=
      fun i => (Finset.univ.filter (fun j : Fin N => T i ≤ T j)).card
    let pValue : Fin N → ℝ := fun i => (tailCount i : ℝ) / (N : ℝ)
    (∀ k : ℕ, k ≤ N →
      (Finset.univ.filter (fun i : Fin N => tailCount i ≤ k)).card ≤ k) ∧
    (∀ k : ℕ, k ≤ N →
      (1 / (N : ℝ)) *
        ((Finset.univ.filter
          (fun i : Fin N => pValue i ≤ (k : ℝ) / (N : ℝ))).card : ℝ) ≤
        (k : ℝ) / (N : ℝ)) := by
  sorry

end Msc62GroundTruth
