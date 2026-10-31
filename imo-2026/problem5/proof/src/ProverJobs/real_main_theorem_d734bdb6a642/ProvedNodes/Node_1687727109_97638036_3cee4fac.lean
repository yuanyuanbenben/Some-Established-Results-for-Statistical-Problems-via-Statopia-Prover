import ProverJobs.real_main_theorem_d734bdb6a642.Vocabulary
import ProverJobs.real_main_theorem_d734bdb6a642.Base
import ProverJobs.real_main_theorem_d734bdb6a642.ProvedNodes.Node_894036796_c5e882c6_f47ff87a

set_option autoImplicit false in
theorem statopia_math_node_1687727109_97638036 : ∀ (f : PositiveReal → PositiveReal)
    (hf : IsAdmissible f) (u v : PositiveReal),
    4 * (f u : ℝ) * (((f v : ℝ) - (v : ℝ)) - ((f u : ℝ) - (u : ℝ))) ≤
      ((v : ℝ) - (u : ℝ)) ^ 2 := by
  /- @proof-region region.target-node.session.12a98fd4ec06f470 begin -/
  intro f hf u v
  have hcontact : (f (f u) : ℝ) = 2 * (f u : ℝ) - (u : ℝ) :=
    statopia_math_node_894036796_c5e882c6 f hf u
  have hs : Real.sqrt ((f u : ℝ) * (f v : ℝ)) ≤
      (2 * (f u : ℝ) - (u : ℝ) + (v : ℝ)) / 2 := by
    have h := (hf (f u) v).2
    rw [hcontact] at h
    exact h
  have hsq : (f u : ℝ) * (f v : ℝ) ≤
      ((2 * (f u : ℝ) - (u : ℝ) + (v : ℝ)) / 2) ^ 2 :=
    (Real.sqrt_le_iff.mp hs).2
  nlinarith [hsq]
  /- @proof-region region.target-node.session.12a98fd4ec06f470 end -/
