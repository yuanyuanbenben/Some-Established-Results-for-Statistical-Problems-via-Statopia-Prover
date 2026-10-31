import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q40.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q40.Base

open Matrix

open Matrix

set_option autoImplicit false in
theorem statopia_math_node_2474807198_d38bf418 : ∀ (d : ℕ) (a q : Fin d → ℝ)
    (hq : dotProduct q q = 1),
    dotProduct a q ≤ Real.sqrt (dotProduct a a) := by
  /- @proof-region region.target-node.session.07e9711dca6a5af1 begin -/
  intro d a q hq
  have hq2 : (∑ i, q i ^ 2) = 1 := by simpa [dotProduct, pow_two] using hq
  have ha : (∑ i, a i ^ 2) = dotProduct a a := by
    simp [dotProduct, pow_two]
  have hcs : (dotProduct a q) ^ 2 ≤ dotProduct a a := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin d)) a q
    rw [hq2, mul_one, ha] at h
    simpa [dotProduct] using h
  calc dotProduct a q ≤ |dotProduct a q| := le_abs_self _
    _ = Real.sqrt ((dotProduct a q) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (dotProduct a a) := Real.sqrt_le_sqrt hcs
  /- @proof-region region.target-node.session.07e9711dca6a5af1 end -/
