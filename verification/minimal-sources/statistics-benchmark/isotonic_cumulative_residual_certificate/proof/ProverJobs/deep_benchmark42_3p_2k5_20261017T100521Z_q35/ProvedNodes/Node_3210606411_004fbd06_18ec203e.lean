import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q35.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q35.Base


set_option autoImplicit false in
theorem statopia_math_node_3210606411_004fbd06 : ∀ (n : ℕ) (y thetaHat : Fin n → ℝ),
    let R : ℕ → ℝ := fun k => ∑ j : Fin n, if (j : ℕ) < k then y j - thetaHat j else 0
    let P : ℕ → ℝ :=
      fun k => ∑ j ∈ Finset.range k, (if h : j < n then y ⟨j, h⟩ - thetaHat ⟨j, h⟩ else 0)
    (∀ k : ℕ, R k = P k) ∧ R 0 = 0 ∧ P 0 = 0 := by
  /- @proof-region region.target-node.session.bb132a595ec31d95 begin -/
  intro n y thetaHat
  dsimp only
  refine ⟨?_, by simp, by simp⟩
  intro k
  let g : ℕ → ℝ := fun t => if h : t < n then y ⟨t, h⟩ - thetaHat ⟨t, h⟩ else 0
  have hg : ∀ (t : ℕ) (ht : t < n), g t = y ⟨t, ht⟩ - thetaHat ⟨t, ht⟩ := by
    intro t ht
    exact dif_pos ht
  have hR : (∑ j : Fin n, if (j : ℕ) < k then y j - thetaHat j else 0)
      = ∑ t ∈ Finset.range (min k n), g t := by
    have h1 : (∑ j : Fin n, if (j : ℕ) < k then y j - thetaHat j else 0)
        = ∑ j : Fin n, (if (j : ℕ) < k then g (j : ℕ) else 0) := by
      refine Finset.sum_congr rfl ?_
      intro j _
      by_cases hj : (j : ℕ) < k
      · rw [if_pos hj, if_pos hj]
        exact (hg (j : ℕ) j.isLt).symm
      · rw [if_neg hj, if_neg hj]
    have h2 : (∑ j : Fin n, (if (j : ℕ) < k then g (j : ℕ) else 0))
        = ∑ t ∈ Finset.range n, (if t < k then g t else 0) :=
      Fin.sum_univ_eq_sum_range (fun t : ℕ => if t < k then g t else 0) n
    have step1 : (∑ t ∈ Finset.range (min k n), (if t < k then g t else 0))
        = ∑ t ∈ Finset.range n, (if t < k then g t else 0) := by
      refine Finset.sum_subset ?_ ?_
      · intro x hx
        rw [Finset.mem_range] at hx ⊢
        exact (lt_min_iff.mp hx).2
      · intro x hx hxnot
        rw [Finset.mem_range] at hx hxnot
        have hk : ¬ x < k := fun hlt => hxnot (lt_min hlt hx)
        rw [if_neg hk]
    have step2 : (∑ t ∈ Finset.range (min k n), g t)
        = ∑ t ∈ Finset.range (min k n), (if t < k then g t else 0) := by
      refine Finset.sum_congr rfl ?_
      intro t ht
      rw [Finset.mem_range] at ht
      rw [if_pos (lt_min_iff.mp ht).1]
    rw [h1, h2, ← step1, step2]
  have hP : (∑ j ∈ Finset.range k, (if h : j < n then y ⟨j, h⟩ - thetaHat ⟨j, h⟩ else 0))
      = ∑ t ∈ Finset.range (min k n), g t := by
    have h1 : (∑ j ∈ Finset.range k, g j)
        = ∑ j ∈ Finset.range k, (if h : j < n then y ⟨j, h⟩ - thetaHat ⟨j, h⟩ else 0) := by
      refine Finset.sum_congr rfl ?_
      intro j _
      rfl
    have step : (∑ t ∈ Finset.range (min k n), g t) = ∑ t ∈ Finset.range k, g t := by
      refine Finset.sum_subset ?_ ?_
      · intro x hx
        rw [Finset.mem_range] at hx ⊢
        exact (lt_min_iff.mp hx).1
      · intro x hx hxnot
        rw [Finset.mem_range] at hx hxnot
        have hn : ¬ x < n := fun hlt => hxnot (lt_min hx hlt)
        exact dif_neg hn
    rw [← h1, step]
  rw [hR, hP]
  /- @proof-region region.target-node.session.bb132a595ec31d95 end -/
