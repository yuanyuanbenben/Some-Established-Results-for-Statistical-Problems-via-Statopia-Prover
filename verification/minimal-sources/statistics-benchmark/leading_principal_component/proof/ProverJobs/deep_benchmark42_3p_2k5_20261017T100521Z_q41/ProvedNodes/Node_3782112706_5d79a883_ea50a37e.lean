import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q41.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q41.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q41.ProvedNodes.Node_3287348555_0ab2c998_b668baa5

open Matrix

open Matrix

set_option autoImplicit false in
theorem statopia_math_node_3782112706_5d79a883 : ∀ (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (x : Fin n → Fin d → ℝ)
    (v : Fin d → Fin d → ℝ)
    (lambda : Fin d → ℝ)
    (first : Fin d) (hfirst : (first : ℕ) = 0)
    (horth : ∀ j k : Fin d, dotProduct (v j) (v k) = if j = k then (1 : ℝ) else 0)
    (hspan : Submodule.span ℝ (Set.range v) = ⊤)
    (S : Matrix (Fin d) (Fin d) ℝ)
    (hS : S = (n : ℝ)⁻¹ • ∑ i, vecMulVec (x i) (x i))
    (heig : ∀ j : Fin d, S *ᵥ v j = lambda j • v j)
    (hne : ∀ j : Fin d, j ≠ first → lambda first > lambda j)
    (u : Fin d → ℝ),
    ((n : ℝ)⁻¹ * (∑ i : Fin n, (dotProduct u (x i)) ^ 2)
        ≤ lambda first * dotProduct u u) ∧
      ((n : ℝ)⁻¹ * (∑ i : Fin n, (dotProduct u (x i)) ^ 2)
          = lambda first * dotProduct u u ↔
        ∀ j : Fin d, j ≠ first → dotProduct u (v j) = 0) := by
  /- @proof-region region.target-node.session.d950b0b84fbd959c begin -/
  intro n d hn hd x v lambda first hfirst horth hspan S hS heig hne u
  obtain ⟨hident, hdeficit⟩ :=
    statopia_math_node_3287348555_0ab2c998 n d hn hd x v lambda first hfirst horth hspan S hS heig u
  have hnonneg : ∀ j ∈ (Finset.univ : Finset (Fin d)),
      0 ≤ (lambda first - lambda j) * (dotProduct u (v j)) ^ 2 := by
    intro j _
    by_cases hj : j = first
    · simp [hj]
    · have h2 : 0 ≤ lambda first - lambda j := by
        have hlt := hne j hj
        linarith
      exact mul_nonneg h2 (sq_nonneg _)
  have hsum : 0 ≤ ∑ j : Fin d, (lambda first - lambda j) * (dotProduct u (v j)) ^ 2 :=
    Finset.sum_nonneg hnonneg
  constructor
  · linarith
  · constructor
    · intro heq
      have hzero : ∑ j : Fin d, (lambda first - lambda j) * (dotProduct u (v j)) ^ 2 = 0 := by
        rw [← hdeficit, heq]
        ring
      intro j hj
      have hterm : (lambda first - lambda j) * (dotProduct u (v j)) ^ 2 = 0 := by
        have hle := Finset.single_le_sum hnonneg (Finset.mem_univ j)
        rw [hzero] at hle
        exact le_antisymm hle (hnonneg j (Finset.mem_univ j))
      have hfac : lambda first - lambda j ≠ 0 := by
        have hlt := hne j hj
        intro h0
        linarith
      rcases mul_eq_zero.mp hterm with h | h
      · exact absurd h hfac
      · rw [pow_two] at h
        exact mul_self_eq_zero.mp h
    · intro hall
      have hzero : ∑ j : Fin d, (lambda first - lambda j) * (dotProduct u (v j)) ^ 2 = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        by_cases hj : j = first
        · rw [hj]; ring
        · rw [hall j hj]; ring
      have hdiff : lambda first * dotProduct u u
          - (n : ℝ)⁻¹ * (∑ i : Fin n, (dotProduct u (x i)) ^ 2) = 0 := by
        rw [hdeficit, hzero]
      linarith

  /- @proof-region region.target-node.session.d950b0b84fbd959c end -/
