import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q37.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q37.Base

open Matrix

open Matrix

set_option autoImplicit false in
theorem statopia_math_node_3849316766_249c6d5e : ∀ (ell : ℕ) (x h : ℝ) (Q : Polynomial ℝ) (hQ : Q.natDegree ≤ ell)
    (P : Polynomial ℝ)
    (hP : P = Q.comp (Polynomial.C x + Polynomial.C h * Polynomial.X)),
    P.natDegree ≤ ell ∧
      (∀ t : ℝ, P.eval t = Q.eval (x + h * t)) ∧
      P.eval 0 = Q.eval x := by
  /- @proof-region region.target-node.session.becee3f6f6fdae3a begin -/
  intro ell x h Q hQ P hP
  subst hP
  refine ⟨?_, ?_, ?_⟩
  · have hc : (Polynomial.C x + Polynomial.C h * Polynomial.X : Polynomial ℝ).natDegree ≤ 1 := by
      refine le_trans (Polynomial.natDegree_add_le _ _) (max_le (by simp) ?_)
      refine le_trans Polynomial.natDegree_mul_le ?_
      simp
    calc (Q.comp (Polynomial.C x + Polynomial.C h * Polynomial.X)).natDegree
        ≤ Q.natDegree * (Polynomial.C x + Polynomial.C h * Polynomial.X).natDegree :=
          Polynomial.natDegree_comp_le
      _ ≤ ell * 1 := Nat.mul_le_mul hQ hc
      _ = ell := Nat.mul_one ell
  · intro t
    rw [Polynomial.eval_comp]
    simp
  · simp

  /- @proof-region region.target-node.session.becee3f6f6fdae3a end -/
