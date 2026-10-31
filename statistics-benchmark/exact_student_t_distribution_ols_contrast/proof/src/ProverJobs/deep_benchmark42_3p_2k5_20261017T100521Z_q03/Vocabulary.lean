import Mathlib

-- Shared append-only definitions for the root theorem and every Math node.
-- Node Formalize may add def/abbrev/structure/class/inductive declarations here.

/-- The Gamma / chi-square density kernel `G_a` of the convolution identity
`∫_0^s G_a(u) * G_b(s - u) du = G_{a+b}(s)`:
for `s > 0` it equals `s ^ (a - 1) * exp (-(s / 2)) / (2 ^ a * Gamma a)`,
and it is `0` for `s ≤ 0`. -/
noncomputable def gammaConvDensity (a s : ℝ) : ℝ :=
  if 0 < s then
    Real.rpow s (a - 1) * Real.exp (-(s / 2)) / (Real.rpow 2 a * Real.Gamma a)
  else 0
