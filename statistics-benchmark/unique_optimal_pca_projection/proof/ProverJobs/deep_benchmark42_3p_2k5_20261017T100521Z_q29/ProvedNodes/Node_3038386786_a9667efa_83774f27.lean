import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q29.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q29.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q29.ProvedNodes.Node_231152612_c7bdfebf_9dc2168f
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q29.ProvedNodes.Node_2617968406_fa05324d_304836a0


open Matrix

open Matrix

set_option autoImplicit false in
theorem statopia_math_node_3038386786_a9667efa : ∀ (d : ℕ) (v : Fin d → Fin d → ℝ) (lambda : Fin d → ℝ)
    (S : Matrix (Fin d) (Fin d) ℝ) (r : ℕ)
    (P : Matrix (Fin d) (Fin d) ℝ)
    (horth : ∀ j k : Fin d, dotProduct (v j) (v k) = if j = k then 1 else 0)
    (hspan : Submodule.span ℝ (Set.range v) = ⊤)
    (heig : ∀ j : Fin d, S *ᵥ v j = lambda j • v j)
    (hPsymm : P.transpose = P) (hPidem : P * P = P)
    (hPtrace : P.trace = (r : ℝ)),
    (∀ j : Fin d, 0 ≤ dotProduct (v j) (P *ᵥ v j)) ∧
    (∀ j : Fin d, dotProduct (v j) (P *ᵥ v j) ≤ 1) ∧
    (∑ j : Fin d, dotProduct (v j) (P *ᵥ v j) = (r : ℝ)) ∧
    ((P * S).trace = ∑ j : Fin d, lambda j * dotProduct (v j) (P *ᵥ v j)) := by
  /- @proof-region region.target-node.session.28abe0e303a0255f begin -/
  intro d v lambda S r P horth hspan heig hPsymm hPidem hPtrace
  have hpyth := statopia_math_node_231152612_c7bdfebf d P hPsymm hPidem
  have htr := statopia_math_node_2617968406_fa05324d d v horth hspan
  have hsq : ∀ x : Fin d → ℝ, 0 ≤ dotProduct x x := by
    intro x
    simp only [dotProduct]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    rw [← (hpyth (v j)).1]
    exact hsq _
  · intro j
    have h2 := (hpyth (v j)).2
    have hjj : dotProduct (v j) (v j) = 1 := by simpa using horth j j
    have hnn : 0 ≤ dotProduct (v j - P *ᵥ v j) (v j - P *ᵥ v j) := hsq _
    linarith
  · rw [htr P, hPtrace]
  · rw [← htr (P * S)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Matrix.mulVec_mulVec, heig j, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  /- @proof-region region.target-node.session.28abe0e303a0255f end -/
