import ProverJobs.real_main_theorem_d734bdb6a642.Vocabulary
import ProverJobs.real_main_theorem_d734bdb6a642.Base


set_option autoImplicit false in
theorem statopia_math_node_93132176_513605de : ∀ (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B),
    Real.sqrt (A * B) ≤ (A + B) / 2 ∧
      (A + B) / 2 ≤ Real.sqrt ((A ^ 2 + B ^ 2) / 2) := by
  /- @proof-region region.target-node.session.4452b1b1b5563735 begin -/
  intro A B hA hB
  have hy : 0 ≤ (A + B) / 2 := by linarith
  constructor
  · have h1 : A * B ≤ ((A + B) / 2) ^ 2 := by nlinarith [sq_nonneg (A - B)]
    have h2 : Real.sqrt (A * B) ≤ Real.sqrt (((A + B) / 2) ^ 2) := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq hy] at h2
  · have h3 : ((A + B) / 2) ^ 2 ≤ (A ^ 2 + B ^ 2) / 2 := by
      nlinarith [sq_nonneg (A - B)]
    have h4 : Real.sqrt (((A + B) / 2) ^ 2) ≤ Real.sqrt ((A ^ 2 + B ^ 2) / 2) :=
      Real.sqrt_le_sqrt h3
    rwa [Real.sqrt_sq hy] at h4
  /- @proof-region region.target-node.session.4452b1b1b5563735 end -/
