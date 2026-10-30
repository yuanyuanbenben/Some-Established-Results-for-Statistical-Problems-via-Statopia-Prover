import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q41.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q41.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q41.ProvedNodes.Node_2077427745_aa6b8923_89279595
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q41.ProvedNodes.Node_2870924675_739d774f_df01e636
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q41.ProvedNodes.Node_4083791463_de762566_119155e9



open Matrix

open Matrix

set_option autoImplicit false in
theorem statopia_math_node_3287348555_0ab2c998 : ∀ (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (x : Fin n → Fin d → ℝ)
    (v : Fin d → Fin d → ℝ)
    (lambda : Fin d → ℝ)
    (first : Fin d) (hfirst : (first : ℕ) = 0)
    (horth : ∀ j k : Fin d, dotProduct (v j) (v k) = if j = k then (1 : ℝ) else 0)
    (hspan : Submodule.span ℝ (Set.range v) = ⊤)
    (S : Matrix (Fin d) (Fin d) ℝ)
    (hS : S = (n : ℝ)⁻¹ • ∑ i, vecMulVec (x i) (x i))
    (heig : ∀ j : Fin d, S *ᵥ v j = lambda j • v j)
    (u : Fin d → ℝ),
    ((n : ℝ)⁻¹ * (∑ i : Fin n, (dotProduct u (x i)) ^ 2)
        = ∑ j : Fin d, lambda j * (dotProduct u (v j)) ^ 2) ∧
      (lambda first * dotProduct u u - (n : ℝ)⁻¹ * (∑ i : Fin n, (dotProduct u (x i)) ^ 2)
        = ∑ j : Fin d, (lambda first - lambda j) * (dotProduct u (v j)) ^ 2) := by
  /- @proof-region region.target-node.session.feb6f0dcc24675b0 begin -/
  intro n d hn hd x v lambda first hfirst horth hspan S hS heig u
  have hexp : u = ∑ j : Fin d, (dotProduct u (v j)) • v j :=
    (statopia_math_node_2870924675_739d774f d hd v horth hspan).1 u
  have hobj : (n : ℝ)⁻¹ * (∑ i : Fin n, (dotProduct u (x i)) ^ 2) = dotProduct u (S *ᵥ u) :=
    statopia_math_node_2077427745_aa6b8923 n d hn x S hS u
  have hdp : ∀ (w : Fin d → ℝ) (s : Finset (Fin d)) (c : Fin d → ℝ),
      dotProduct w (∑ j ∈ s, c j • v j) = ∑ j ∈ s, c j * dotProduct w (v j) := by
    intro w s
    induction s using Finset.induction with
    | empty =>
        intro c
        simp [dotProduct]
    | insert a s ha ih =>
        intro c
        rw [Finset.sum_insert ha, Finset.sum_insert ha, dotProduct_add, ih c,
          dotProduct_smul, smul_eq_mul]
  have hA : dotProduct (Matrix.vecMul u S) u
      = dotProduct (Matrix.vecMul u S) (∑ j : Fin d, (dotProduct u (v j)) • v j) :=
    congrArg (fun w : Fin d → ℝ => dotProduct (Matrix.vecMul u S) w) hexp
  have hB : dotProduct (Matrix.vecMul u S) (∑ j : Fin d, (dotProduct u (v j)) • v j)
      = ∑ j : Fin d, (dotProduct u (v j)) * dotProduct (Matrix.vecMul u S) (v j) :=
    hdp (Matrix.vecMul u S) Finset.univ (fun j : Fin d => dotProduct u (v j))
  have hC : ∑ j : Fin d, (dotProduct u (v j)) * dotProduct (Matrix.vecMul u S) (v j)
      = ∑ j : Fin d, lambda j * (dotProduct u (v j)) ^ 2 := by
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 : dotProduct (Matrix.vecMul u S) (v j) = dotProduct u (S *ᵥ v j) :=
      (Matrix.dotProduct_mulVec u S (v j)).symm
    rw [h1, heig j, dotProduct_smul, smul_eq_mul]
    ring
  have hmain : dotProduct u (S *ᵥ u) = ∑ j : Fin d, lambda j * (dotProduct u (v j)) ^ 2 :=
    (Matrix.dotProduct_mulVec u S u).trans (hA.trans (hB.trans hC))
  have hpart1 : (n : ℝ)⁻¹ * (∑ i : Fin n, (dotProduct u (x i)) ^ 2)
      = ∑ j : Fin d, lambda j * (dotProduct u (v j)) ^ 2 := by
    rw [hobj, hmain]
  have hparseval : ∑ j : Fin d, (dotProduct u (v j)) ^ 2 = dotProduct u u :=
    (statopia_math_node_4083791463_de762566 d hd v horth hspan u).1
  refine ⟨hpart1, ?_⟩
  calc lambda first * dotProduct u u - (n : ℝ)⁻¹ * (∑ i : Fin n, (dotProduct u (x i)) ^ 2)
      = lambda first * (∑ j : Fin d, (dotProduct u (v j)) ^ 2)
          - ∑ j : Fin d, lambda j * (dotProduct u (v j)) ^ 2 := by
        rw [← hparseval, hpart1]
    _ = ∑ j : Fin d, (lambda first - lambda j) * (dotProduct u (v j)) ^ 2 := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
  /- @proof-region region.target-node.session.feb6f0dcc24675b0 end -/
