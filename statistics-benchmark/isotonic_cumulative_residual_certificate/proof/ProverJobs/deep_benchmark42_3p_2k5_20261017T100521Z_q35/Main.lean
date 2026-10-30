import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q35.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q35.ProvedNodes
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q35.Base

theorem isotonic_cumulative_residual_certificate
    (n : ℕ) (hn : 1 ≤ n)
    (y thetaHat : Fin n → ℝ) :
    let R : ℕ → ℝ := fun k ↦
      ∑ j : Fin n, if j.1 < k then y j - thetaHat j else 0
    (∀ i : ℕ, (hi : i + 1 < n) →
      thetaHat ⟨i, lt_trans (Nat.lt_succ_self i) hi⟩ ≤
        thetaHat ⟨i + 1, hi⟩) →
    (∀ i : ℕ, (hi : i + 1 < n) → 0 ≤ R (i + 1)) →
    R n = 0 →
    (∀ i : ℕ, (hi : i + 1 < n) →
      R (i + 1) *
        (thetaHat ⟨i + 1, hi⟩ -
          thetaHat ⟨i, lt_trans (Nat.lt_succ_self i) hi⟩) = 0) →
    ∀ theta : Fin n → ℝ,
      (∀ i : ℕ, (hi : i + 1 < n) →
        theta ⟨i, lt_trans (Nat.lt_succ_self i) hi⟩ ≤
          theta ⟨i + 1, hi⟩) →
      ∑ i, (y i - theta i) ^ 2 ≥
        ∑ i, (y i - thetaHat i) ^ 2 +
          ∑ i, (theta i - thetaHat i) ^ 2
:= by
  /- @proof-region region.root.c09b5ea2b377 begin -/
  intro R hthetaMono hpos hzero hcs theta hmono
  set rho : ℕ → ℝ := fun j => if h : j < n then y ⟨j, h⟩ - thetaHat ⟨j, h⟩ else 0 with hrho
  set alpha : ℕ → ℝ := fun j => if h : j < n then theta ⟨j, h⟩ - thetaHat ⟨j, h⟩ else 0 with halpha
  have hrho_apply : ∀ (j : ℕ) (h : j < n), rho j = y ⟨j, h⟩ - thetaHat ⟨j, h⟩ := fun j h => dif_pos h
  have halpha_apply : ∀ (j : ℕ) (h : j < n), alpha j = theta ⟨j, h⟩ - thetaHat ⟨j, h⟩ := fun j h => dif_pos h
  have hR_eq : ∀ k ≤ n, R k = ∑ j ∈ Finset.range k, rho j := by
    intro k hk
    have hA : R k = ∑ j : Fin n, (if (j : ℕ) < k then rho (j : ℕ) else 0) := by
      have hRk : R k = ∑ j : Fin n, (if (j : ℕ) < k then y j - thetaHat j else 0) := rfl
      rw [hRk]
      refine Finset.sum_congr rfl ?_
      intro j _
      by_cases h : (j : ℕ) < k
      · rw [if_pos h, if_pos h, hrho_apply (j : ℕ) j.isLt]
      · rw [if_neg h, if_neg h]
    have hB : (∑ j : Fin n, (if (j : ℕ) < k then rho (j : ℕ) else 0))
        = ∑ j ∈ Finset.range n, (if j < k then rho j else 0) :=
      Fin.sum_univ_eq_sum_range (fun j => if j < k then rho j else 0) n
    have hC : (∑ j ∈ Finset.range n, (if j < k then rho j else 0)) = ∑ j ∈ Finset.range k, rho j := by
      have hsub : Finset.range k ⊆ Finset.range n := by
        intro x hx
        simp only [Finset.mem_range] at hx ⊢
        omega
      have hvan : ∀ x ∈ Finset.range n, x ∉ Finset.range k → (if x < k then rho x else 0) = 0 := by
        intro x _ hx
        exact if_neg (by simpa using hx)
      have hsame : (∑ j ∈ Finset.range k, (if j < k then rho j else 0)) = ∑ j ∈ Finset.range k, rho j := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        rw [if_pos (Finset.mem_range.mp hx)]
      rw [← hsame, ← Finset.sum_subset hsub hvan]
    exact hA.trans (hB.trans hC)
  have hsum_zero : (∑ i ∈ Finset.range n, rho i) = 0 := by
    rw [← hR_eq n le_rfl]
    exact hzero
  have habel : (∑ i ∈ Finset.range n, alpha i * rho i)
      = ∑ i ∈ Finset.range (n - 1), (alpha i - alpha (i + 1)) * R (i + 1) := by
    have hbp := Finset.sum_range_by_parts (R := ℝ) (M := ℝ) alpha rho n
    simp only [smul_eq_mul] at hbp
    have hinner : (∑ i ∈ Finset.range (n - 1), (alpha (i + 1) - alpha i) * (∑ j ∈ Finset.range (i + 1), rho j))
        = - ∑ i ∈ Finset.range (n - 1), (alpha i - alpha (i + 1)) * R (i + 1) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hi' : i + 1 ≤ n := by
        simp only [Finset.mem_range] at hi
        omega
      rw [← hR_eq (i + 1) hi']
      ring
    rw [hsum_zero, hinner] at hbp
    rw [hbp]
    ring
  have hle : (∑ i ∈ Finset.range n, alpha i * rho i) ≤ 0 :=
    statopia_math_node_467254402_5ac6457a n hn y thetaHat theta hpos hzero hcs hmono habel
  have hcross_eq : (∑ i : Fin n, (y i - thetaHat i) * (theta i - thetaHat i))
      = ∑ i ∈ Finset.range n, alpha i * rho i := by
    have h1 : (∑ i : Fin n, (y i - thetaHat i) * (theta i - thetaHat i))
        = ∑ i : Fin n, rho (i : ℕ) * alpha (i : ℕ) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [hrho_apply (i : ℕ) i.isLt, halpha_apply (i : ℕ) i.isLt]
    have h2 : (∑ i : Fin n, rho (i : ℕ) * alpha (i : ℕ))
        = ∑ j ∈ Finset.range n, rho j * alpha j :=
      Fin.sum_univ_eq_sum_range (fun j => rho j * alpha j) n
    have h3 : (∑ j ∈ Finset.range n, rho j * alpha j) = ∑ j ∈ Finset.range n, alpha j * rho j := by
      refine Finset.sum_congr rfl ?_
      intro j _
      exact mul_comm (rho j) (alpha j)
    exact h1.trans (h2.trans h3)
  have hcross : (∑ i : Fin n, (y i - thetaHat i) * (theta i - thetaHat i)) ≤ 0 := by
    rw [hcross_eq]
    exact hle
  have hsq : (∑ i : Fin n, (y i - theta i) ^ 2)
      = (∑ i : Fin n, (y i - thetaHat i) ^ 2) + (∑ i : Fin n, (theta i - thetaHat i) ^ 2)
        - 2 * ∑ i : Fin n, (y i - thetaHat i) * (theta i - thetaHat i) := by
    calc (∑ i : Fin n, (y i - theta i) ^ 2)
        = ∑ i : Fin n, ((y i - thetaHat i) ^ 2 + (theta i - thetaHat i) ^ 2 -
            2 * ((y i - thetaHat i) * (theta i - thetaHat i))) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          ring
      _ = (∑ i : Fin n, (y i - thetaHat i) ^ 2) + (∑ i : Fin n, (theta i - thetaHat i) ^ 2) -
            2 * ∑ i : Fin n, (y i - thetaHat i) * (theta i - thetaHat i) := by
          rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  nlinarith [hsq, hcross]
  /- @proof-region region.root.c09b5ea2b377 end -/
