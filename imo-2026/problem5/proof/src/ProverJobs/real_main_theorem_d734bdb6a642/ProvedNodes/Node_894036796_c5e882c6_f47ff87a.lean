import ProverJobs.real_main_theorem_d734bdb6a642.Vocabulary
import ProverJobs.real_main_theorem_d734bdb6a642.Base


set_option autoImplicit false in
theorem statopia_math_node_894036796_c5e882c6 : ∀ (f : PositiveReal → PositiveReal) (hf : IsAdmissible f) (t : PositiveReal),
    (f (f t) : ℝ) = 2 * (f t : ℝ) - (t : ℝ) := by
  /- @proof-region region.target-node.session.3b448004ebcabb08 begin -/
  intro f hf t
  have hq : 0 < (f t : ℝ) := (f t).property
  have h := hf (f t) t
  have hupper : (f t : ℝ) ≥ ((f (f t) : ℝ) + (t : ℝ)) / 2 := by
    have hsqrt : Real.sqrt ((f t : ℝ) ^ 2) = (f t : ℝ) := Real.sqrt_sq (le_of_lt hq)
    simpa [hsqrt] using h.1
  have hlower : ((f (f t) : ℝ) + (t : ℝ)) / 2 ≥ (f t : ℝ) := by
    have hsqrt : Real.sqrt ((f t : ℝ) * (f t : ℝ)) = (f t : ℝ) := by
      have hmul : (f t : ℝ) * (f t : ℝ) = (f t : ℝ) ^ 2 := by ring
      rw [hmul, Real.sqrt_sq (le_of_lt hq)]
    simpa [hsqrt] using h.2
  have hmid : ((f (f t) : ℝ) + (t : ℝ)) / 2 = (f t : ℝ) := le_antisymm hupper hlower
  linarith
  /- @proof-region region.target-node.session.3b448004ebcabb08 end -/
