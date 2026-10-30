import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q40.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q40.Base

open Matrix

open Matrix

set_option autoImplicit false in
theorem statopia_math_node_3852170914_d7d89bd9 : ∀ (d : ℕ) (a : Fin d → ℝ) (ha : a ≠ 0),
    let s : ℝ := dotProduct a a
    let v : Fin d → ℝ := (Real.sqrt s)⁻¹ • a
    0 < s ∧ dotProduct v v = 1 ∧ dotProduct a v = Real.sqrt s := by
  /- @proof-region region.target-node.session.60c180fa766f5dce begin -/
  intro d a ha
  dsimp only
  set s : ℝ := dotProduct a a with hs
  have hnn : 0 ≤ s := by
    rw [hs]
    unfold dotProduct
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg (a i)
  have hne : s ≠ 0 := by
    rw [hs]
    exact fun h => ha (dotProduct_self_eq_zero.mp h)
  have hpos : 0 < s := lt_of_le_of_ne hnn (Ne.symm hne)
  have hsqrtpos : 0 < Real.sqrt s := by positivity
  have hsq : Real.sqrt s ^ 2 = s := Real.sq_sqrt hpos.le
  set c : ℝ := (Real.sqrt s)⁻¹ with hc
  set v : Fin d → ℝ := c • a with hv
  have hvveq : dotProduct v v = c ^ 2 * s := by
    rw [hv, dotProduct_smul, dotProduct_comm, dotProduct_smul, ← hs]
    simp only [smul_eq_mul]
    ring
  have hcc : c ^ 2 * s = 1 := by
    have ht0 : Real.sqrt s ≠ 0 := hsqrtpos.ne'
    rw [hc]
    field_simp
    nlinarith [hsq]
  have hav : dotProduct a v = Real.sqrt s := by
    rw [hv, dotProduct_smul, ← hs]
    simp only [smul_eq_mul]
    rw [hc]
    field_simp
    nlinarith [hsq]
  exact ⟨hpos, hvveq.trans hcc, hav⟩
  /- @proof-region region.target-node.session.60c180fa766f5dce end -/
