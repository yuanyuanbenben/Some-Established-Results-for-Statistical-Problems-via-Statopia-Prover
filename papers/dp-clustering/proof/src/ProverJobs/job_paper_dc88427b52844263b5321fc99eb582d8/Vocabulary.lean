import Mathlib

-- Shared append-only definitions for the root theorem and every Math node.
-- Node Formalize may add def/abbrev/structure/class/inductive declarations here.

/-- The per-class block-count factor of the single-block estimate:
`dpPhi a = if a = 0 then 1 else a! / a ^ 2`, i.e. `dpPhi a = (a.factorial : ℝ) / (a : ℝ)^2`
for `a ≥ 1` and `dpPhi 0 = 1`. -/
noncomputable def dpPhi (a : ℕ) : ℝ :=
  if a = 0 then (1 : ℝ) else (a.factorial : ℝ) / ((a : ℝ) ^ 2)
