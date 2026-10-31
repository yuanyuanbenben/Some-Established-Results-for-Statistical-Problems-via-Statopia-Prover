import Mathlib

namespace Msc62GroundTruth

/--
Any real median, defined by the two half-sample counting inequalities, minimizes
the sum of absolute deviations.
-/
theorem median_minimizes_absolute_deviation
    (n : ℕ) (hn : 1 ≤ n) (x : Fin n → ℝ) (m : ℝ)
    (h_left : n ≤
      2 * (Finset.univ.filter (fun i : Fin n => x i ≤ m)).card)
    (h_right : n ≤
      2 * (Finset.univ.filter (fun i : Fin n => m ≤ x i)).card) :
    let L : ℝ → ℝ := fun a => ∑ i : Fin n, |x i - a|
    ∀ a : ℝ, L m ≤ L a := by
  sorry

end Msc62GroundTruth
