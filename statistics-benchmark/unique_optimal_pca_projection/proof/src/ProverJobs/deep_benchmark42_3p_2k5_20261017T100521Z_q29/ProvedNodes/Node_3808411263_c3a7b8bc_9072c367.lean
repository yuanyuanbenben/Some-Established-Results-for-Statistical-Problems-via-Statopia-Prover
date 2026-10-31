import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q29.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q29.Base

open Matrix

open Matrix

set_option autoImplicit false in
theorem statopia_math_node_3808411263_c3a7b8bc : ∀ (d r : ℕ) (hr0 : 1 ≤ r) (hrd : r < d)
    (lambda : Fin d → ℝ) (w : Fin d → ℝ)
    (hmono : Antitone lambda)
    (hsep : ∀ i j : Fin d, i.val < r → r ≤ j.val → lambda i > lambda j)
    (hw_nonneg : ∀ j : Fin d, 0 ≤ w j)
    (hw_le_one : ∀ j : Fin d, w j ≤ 1)
    (hsum : ∑ j, w j = (r : ℝ)),
    (∑ j, lambda j * w j ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin d => j.val < r), lambda j) ∧
      ((∑ j, lambda j * w j = ∑ j ∈ Finset.univ.filter (fun j : Fin d => j.val < r), lambda j) →
        (∀ j : Fin d, j.val < r → w j = 1) ∧ (∀ j : Fin d, r ≤ j.val → w j = 0)) := by
  /- @proof-region region.target-node.session.08a4bd05b44922f1 begin -/
  intro d r hr0 hrd lambda w hmono hsep hw_nonneg hw_le_one hsum
  have hr1 : r - 1 < d := by omega
  let i1 : Fin d := ⟨r - 1, hr1⟩
  let i2 : Fin d := ⟨r, hrd⟩
  have hgap : lambda i1 > lambda i2 := by
    apply hsep
    · dsimp only [i1]; omega
    · dsimp only [i2]; omega
  let c : ℝ := (lambda i1 + lambda i2) / 2
  have hc1 : c < lambda i1 := by dsimp only [c]; linarith
  have hc2 : lambda i2 < c := by dsimp only [c]; linarith
  let A : Finset (Fin d) := Finset.univ.filter (fun j : Fin d => j.val < r)
  let B : Finset (Fin d) := Finset.univ.filter (fun j : Fin d => ¬ j.val < r)
  have hcardA : A.card = r := by
    have hIio : A = Finset.Iio i2 := by
      ext j
      simp [A, i2, Fin.lt_def, Finset.mem_Iio]
    rw [hIio, Fin.card_Iio]
  have hpart_lam : ∑ j ∈ A, lambda j * w j + ∑ j ∈ B, lambda j * w j = ∑ j, lambda j * w j :=
    Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin d => j.val < r) (fun j => lambda j * w j)
  have hpart_w : ∑ j ∈ A, w j + ∑ j ∈ B, w j = ∑ j, w j :=
    Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin d => j.val < r) (fun j => w j)
  have hzero : ∑ j ∈ A, (1 - w j) = ∑ j ∈ B, w j := by
    have h1 : ∑ j ∈ A, (1 - w j) = ∑ j ∈ A, (1:ℝ) - ∑ j ∈ A, w j := by
      rw [Finset.sum_sub_distrib]
    have h2 : ∑ j ∈ A, (1:ℝ) = (A.card : ℝ) := by rw [Finset.sum_const]; simp
    have h3 : (A.card : ℝ) = (r : ℝ) := by rw [hcardA]
    linarith [h1, h2, h3, hpart_w, hsum]
  have hAcoef : ∀ j ∈ A, (0:ℝ) < lambda j - c := by
    intro j hj
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    have hjle : j ≤ i1 := by rw [Fin.le_def]; dsimp only [i1]; omega
    linarith [hmono hjle, hc1]
  have hBcoef : ∀ j ∈ B, (0:ℝ) < c - lambda j := by
    intro j hj
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    have hjle : i2 ≤ j := by rw [Fin.le_def]; dsimp only [i2]; omega
    linarith [hmono hjle, hc2]
  have hAnonneg : ∀ j ∈ A, 0 ≤ (lambda j - c) * (1 - w j) := by
    intro j hj
    exact mul_nonneg (le_of_lt (hAcoef j hj)) (by linarith [hw_le_one j])
  have hBnonneg : ∀ j ∈ B, 0 ≤ (c - lambda j) * w j := by
    intro j hj
    exact mul_nonneg (le_of_lt (hBcoef j hj)) (hw_nonneg j)
  have hsumAnonneg : 0 ≤ ∑ j ∈ A, (lambda j - c) * (1 - w j) := Finset.sum_nonneg hAnonneg
  have hsumBnonneg : 0 ≤ ∑ j ∈ B, (c - lambda j) * w j := Finset.sum_nonneg hBnonneg
  have hdecomp : ∑ j ∈ A, lambda j - ∑ j, lambda j * w j
      = ∑ j ∈ A, (lambda j - c) * (1 - w j) + ∑ j ∈ B, (c - lambda j) * w j := by
    have e1 : ∑ j ∈ A, lambda j - ∑ j ∈ A, lambda j * w j = ∑ j ∈ A, lambda j * (1 - w j) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j hj; ring
    have e2 : ∑ j, lambda j * w j = ∑ j ∈ A, lambda j * w j + ∑ j ∈ B, lambda j * w j :=
      hpart_lam.symm
    have e3 : ∑ j ∈ A, lambda j * (1 - w j)
        = ∑ j ∈ A, (lambda j - c) * (1 - w j) + c * ∑ j ∈ A, (1 - w j) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj; ring
    have e3' : ∑ j ∈ A, lambda j * (1 - w j)
        = ∑ j ∈ A, (lambda j - c) * (1 - w j) + c * ∑ j ∈ B, w j := by
      rw [e3, hzero]
    have e5 : ∑ j ∈ B, (c - lambda j) * w j = - ∑ j ∈ B, (lambda j - c) * w j := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j hj; ring
    have e6 : ∑ j ∈ B, lambda j * w j
        = ∑ j ∈ B, (lambda j - c) * w j + c * ∑ j ∈ B, w j := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj; ring
    linarith [e1, e2, e3', e5, e6]
  have hineq : ∑ j, lambda j * w j ≤ ∑ j ∈ A, lambda j := by
    linarith [hdecomp, hsumAnonneg, hsumBnonneg]
  have heqimp : (∑ j, lambda j * w j = ∑ j ∈ A, lambda j) →
      (∀ j : Fin d, j.val < r → w j = 1) ∧ (∀ j : Fin d, r ≤ j.val → w j = 0) := by
    intro heq
    have hD0 : ∑ j ∈ A, lambda j - ∑ j, lambda j * w j = 0 := by linarith [heq]
    have hRHS0 : ∑ j ∈ A, (lambda j - c) * (1 - w j) + ∑ j ∈ B, (c - lambda j) * w j = 0 := by
      linarith [hdecomp, hD0]
    have hA0 : ∑ j ∈ A, (lambda j - c) * (1 - w j) = 0 := by
      linarith [hsumAnonneg, hsumBnonneg, hRHS0]
    have hB0 : ∑ j ∈ B, (c - lambda j) * w j = 0 := by
      linarith [hsumAnonneg, hsumBnonneg, hRHS0]
    have hAterms : ∀ j ∈ A, (lambda j - c) * (1 - w j) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hAnonneg).mp hA0
    have hBterms : ∀ j ∈ B, (c - lambda j) * w j = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hBnonneg).mp hB0
    constructor
    · intro j hjval
      have hjA : j ∈ A := by
        simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]; exact hjval
      have hterm : (lambda j - c) * (1 - w j) = 0 := hAterms j hjA
      have h1w : 1 - w j = 0 := by
        rcases mul_eq_zero.mp hterm with h | h
        · exact absurd h (ne_of_gt (hAcoef j hjA))
        · exact h
      linarith
    · intro j hjval
      have hjB : j ∈ B := by
        simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]; omega
      have hterm : (c - lambda j) * w j = 0 := hBterms j hjB
      rcases mul_eq_zero.mp hterm with h | h
      · exact absurd h (ne_of_gt (hBcoef j hjB))
      · exact h
  exact ⟨hineq, heqimp⟩
  /- @proof-region region.target-node.session.08a4bd05b44922f1 end -/
