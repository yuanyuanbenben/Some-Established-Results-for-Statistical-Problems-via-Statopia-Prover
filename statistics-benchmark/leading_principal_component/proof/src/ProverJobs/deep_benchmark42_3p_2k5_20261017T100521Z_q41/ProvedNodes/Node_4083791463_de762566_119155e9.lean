import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q41.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q41.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q41.ProvedNodes.Node_2870924675_739d774f_df01e636

open Matrix

open Matrix

set_option autoImplicit false in
theorem statopia_math_node_4083791463_de762566 : ∀ (d : ℕ) (hd : 1 ≤ d)
    (v : Fin d → Fin d → ℝ)
    (horth : ∀ j k : Fin d, dotProduct (v j) (v k) = if j = k then (1 : ℝ) else 0)
    (hspan : Submodule.span ℝ (Set.range v) = ⊤)
    (u : Fin d → ℝ),
    (∑ j : Fin d, (dotProduct u (v j)) ^ 2 = dotProduct u u) ∧
      (0 ≤ ∑ j : Fin d, (dotProduct u (v j)) ^ 2) ∧
      (∑ j : Fin d, (dotProduct u (v j)) ^ 2 = 0 → u = 0) := by
  /- @proof-region region.target-node.session.3f609b137f5349ef begin -/
  intro d hd v horth hspan u
  have hu : u = ∑ j : Fin d, (dotProduct u (v j)) • v j :=
    (statopia_math_node_2870924675_739d774f d hd v horth hspan).1 u
  have hcoord : ∀ i : Fin d, u i = ∑ j : Fin d, (dotProduct u (v j)) * v j i := by
    intro i
    conv_lhs => rw [hu]
    simp [Finset.sum_apply, smul_eq_mul]
  have hmain : dotProduct u u = ∑ j : Fin d, (dotProduct u (v j)) ^ 2 := by
    calc dotProduct u u
        = ∑ i : Fin d, u i * u i := rfl
      _ = ∑ i : Fin d, (∑ j : Fin d, (dotProduct u (v j)) * v j i)
              * (∑ k : Fin d, (dotProduct u (v k)) * v k i) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [hcoord i]
      _ = ∑ i : Fin d, ∑ j : Fin d, ∑ k : Fin d,
              ((dotProduct u (v j)) * v j i) * ((dotProduct u (v k)) * v k i) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [Finset.sum_mul_sum]
      _ = ∑ j : Fin d, ∑ i : Fin d, ∑ k : Fin d,
              ((dotProduct u (v j)) * v j i) * ((dotProduct u (v k)) * v k i) :=
          Finset.sum_comm
      _ = ∑ j : Fin d, ∑ k : Fin d, ∑ i : Fin d,
              ((dotProduct u (v j)) * v j i) * ((dotProduct u (v k)) * v k i) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          exact Finset.sum_comm
      _ = ∑ j : Fin d, ∑ k : Fin d,
              (dotProduct u (v j) * dotProduct u (v k)) * dotProduct (v j) (v k) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [show dotProduct (v j) (v k) = ∑ i : Fin d, v j i * v k i from rfl]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro i _
          ring
      _ = ∑ j : Fin d, (dotProduct u (v j)) ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro j _
          have hcollapse : ∑ k : Fin d,
              (dotProduct u (v j) * dotProduct u (v k)) * dotProduct (v j) (v k)
              = (dotProduct u (v j) * dotProduct u (v j)) * dotProduct (v j) (v j) := by
            refine Finset.sum_eq_single j ?_ ?_
            · intro k _ hkj
              rw [horth j k, if_neg (fun h => hkj h.symm)]
              ring
            · intro hj
              exact absurd (Finset.mem_univ j) hj
          rw [hcollapse, horth j j, if_pos rfl]
          ring
  refine ⟨hmain.symm, ?_, ?_⟩
  · exact Finset.sum_nonneg (fun j _ => sq_nonneg _)
  · intro hzero
    have hall : ∀ j : Fin d, dotProduct u (v j) = 0 := by
      intro j
      have hsum : ∑ k : Fin d, (dotProduct u (v k)) * (dotProduct u (v k)) = 0 := by
        simpa [pow_two] using hzero
      exact (Finset.sum_mul_self_eq_zero_iff Finset.univ
        (fun k => dotProduct u (v k))).mp hsum j (Finset.mem_univ j)
    rw [hu]
    simp [hall]
  /- @proof-region region.target-node.session.3f609b137f5349ef end -/
