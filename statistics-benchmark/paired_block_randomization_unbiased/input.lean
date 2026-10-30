import Mathlib

namespace Msc62GroundTruth

/--
In paired block randomization, the average treated-minus-control contrast is
unbiased for the average of the two unit-level treatment effects in each block.
-/
theorem paired_block_randomization_unbiased
    (b : ℕ) (hb : 1 ≤ b)
    (Y1 Y0 : Fin b → Fin 2 → ℝ) :
    let blockDiff : (Fin b → Bool) → Fin b → ℝ :=
      fun assign j =>
        if assign j then
          Y1 j (0 : Fin 2) - Y0 j (1 : Fin 2)
        else
          Y1 j (1 : Fin 2) - Y0 j (0 : Fin 2)
    let dbar : (Fin b → Bool) → ℝ :=
      fun assign => (1 / (b : ℝ)) * ∑ j : Fin b, blockDiff assign j
    let target : ℝ :=
      (1 / (b : ℝ)) *
        ∑ j : Fin b,
          ((Y1 j (0 : Fin 2) - Y0 j (0 : Fin 2)) +
            (Y1 j (1 : Fin 2) - Y0 j (1 : Fin 2))) / 2
    (1 / (Fintype.card (Fin b → Bool) : ℝ)) *
        ∑ assign : Fin b → Bool, dbar assign =
      target := by
  sorry

end Msc62GroundTruth
