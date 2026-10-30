import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q29.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q29.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q29.ProvedNodes.Node_231152612_c7bdfebf_9dc2168f
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q29.ProvedNodes.Node_3178897791_ea4b1220_26234e39


open Matrix

open Matrix

set_option autoImplicit false in
theorem statopia_math_node_4070169760_207a1beb : ∀ (d r : ℕ) (hr0 : 1 ≤ r) (hrd : r < d)
    (v : Fin d → Fin d → ℝ)
    (horth : ∀ j k : Fin d, dotProduct (v j) (v k) = if j = k then 1 else 0)
    (hspan : Submodule.span ℝ (Set.range v) = ⊤)
    (S : Matrix (Fin d) (Fin d) ℝ)
    (lambda : Fin d → ℝ)
    (hS : ∀ j : Fin d, S *ᵥ v j = lambda j • v j)
    (P : Matrix (Fin d) (Fin d) ℝ)
    (hPsymm : P.transpose = P) (hPidem : P * P = P)
    (hweight_one : ∀ j : Fin d, j.val < r → dotProduct (v j) (P *ᵥ v j) = 1)
    (hweight_zero : ∀ j : Fin d, r ≤ j.val → dotProduct (v j) (P *ᵥ v j) = 0),
    P = ∑ j with j.val < r, vecMulVec (v j) (v j) := by
  /- @proof-region region.target-node.session.f2711bb33b5da7ef begin -/
  intro d r hr0 hrd v horth hspan S lambda hS P hPsymm hPidem hweight_one hweight_zero
  classical
  have hPyth := statopia_math_node_231152612_c7bdfebf d P hPsymm hPidem
  have hPr := statopia_math_node_3178897791_ea4b1220 d r hr0 hrd v lambda horth S hS
  dsimp only at hPr
  obtain ⟨-, -, -, hPr_one, hPr_zero, -⟩ := hPr
  have hact : ∀ j : Fin d,
      P *ᵥ v j = (∑ j with j.val < r, vecMulVec (v j) (v j)) *ᵥ v j := by
    intro j
    by_cases hj : j.val < r
    · rw [hPr_one j hj]
      have h2 := (hPyth (v j)).2
      have h3 : dotProduct (v j) (v j) = 1 := by simpa using horth j j
      have h4 : dotProduct (v j) (P *ᵥ v j) = 1 := hweight_one j hj
      have h5 : dotProduct (v j - P *ᵥ v j) (v j - P *ᵥ v j) = 0 := by
        rw [h2, h3, h4]
        norm_num
      exact (sub_eq_zero.mp (dotProduct_self_eq_zero.mp h5)).symm
    · push_neg at hj
      rw [hPr_zero j hj]
      have h2 := (hPyth (v j)).1
      have h4 : dotProduct (v j) (P *ᵥ v j) = 0 := hweight_zero j hj
      have h5 : dotProduct (P *ᵥ v j) (P *ᵥ v j) = 0 := by
        rw [h2, h4]
      exact dotProduct_self_eq_zero.mp h5
  have hmulVec_zero : ∀ A : Matrix (Fin d) (Fin d) ℝ, A *ᵥ (0 : Fin d → ℝ) = 0 := by
    intro A
    have h := Matrix.mulVec_smul A (0 : ℝ) (0 : Fin d → ℝ)
    simpa using h
  have hlin : ∀ x : Fin d → ℝ,
      (P - ∑ j with j.val < r, vecMulVec (v j) (v j)) *ᵥ x = 0 := by
    intro x
    have hx : x ∈ Submodule.span ℝ (Set.range v) := by
      rw [hspan]
      exact Submodule.mem_top
    refine Submodule.span_induction (s := Set.range v)
      (p := fun y _ => (P - ∑ j with j.val < r, vecMulVec (v j) (v j)) *ᵥ y = 0)
      ?_ ?_ ?_ ?_ hx
    · rintro y ⟨j, rfl⟩
      rw [Matrix.sub_mulVec, hact j, sub_self]
    · exact hmulVec_zero _
    · intro a b ha hb ha' hb'
      rw [Matrix.mulVec_add, ha', hb', add_zero]
    · intro c a ha ha'
      rw [Matrix.mulVec_smul, ha', smul_zero]
  have hPsub : P - ∑ j with j.val < r, vecMulVec (v j) (v j) = 0 := by
    ext i l
    have h := congrFun (hlin (fun k => if l = k then (1 : ℝ) else 0)) i
    simpa [Matrix.mulVec, dotProduct, Finset.sum_mul_boole] using h
  exact sub_eq_zero.mp hPsub
  /- @proof-region region.target-node.session.f2711bb33b5da7ef end -/
