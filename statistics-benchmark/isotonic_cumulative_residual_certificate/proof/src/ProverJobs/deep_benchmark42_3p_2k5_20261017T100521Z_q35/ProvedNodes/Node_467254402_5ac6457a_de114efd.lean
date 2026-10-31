import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q35.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q35.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q35.ProvedNodes.Node_2952203734_ccad5d1e_f8c2441e


set_option autoImplicit false in
theorem statopia_math_node_467254402_5ac6457a : ∀ (n : ℕ) (hn : 1 ≤ n)
    (y thetaHat theta : Fin n → ℝ),
    let rho : ℕ → ℝ := fun j => if h : j < n then y ⟨j, h⟩ - thetaHat ⟨j, h⟩ else 0
    let alpha : ℕ → ℝ := fun j => if h : j < n then theta ⟨j, h⟩ - thetaHat ⟨j, h⟩ else 0
    let R : ℕ → ℝ := fun k => ∑ j : Fin n, if (j : ℕ) < k then y j - thetaHat j else 0
    (∀ i : ℕ, (hi : i + 1 < n) → 0 ≤ R (i + 1)) →
    R n = 0 →
    (∀ i : ℕ, (hi : i + 1 < n) →
      R (i + 1) *
        (thetaHat ⟨i + 1, hi⟩ -
          thetaHat ⟨i, lt_trans (Nat.lt_succ_self i) hi⟩) = 0) →
    (∀ i : ℕ, (hi : i + 1 < n) →
      theta ⟨i, lt_trans (Nat.lt_succ_self i) hi⟩ ≤ theta ⟨i + 1, hi⟩) →
    (∑ i ∈ Finset.range n, alpha i * rho i)
      = ∑ i ∈ Finset.range (n - 1), (alpha i - alpha (i + 1)) * R (i + 1) →
    (∑ i ∈ Finset.range n, alpha i * rho i) ≤ 0 := by
  /- @proof-region region.target-node.session.67a3f0a37f94282f begin -/
  intro n hn y thetaHat theta
  let rho : ℕ → ℝ := fun j => if h : j < n then y ⟨j, h⟩ - thetaHat ⟨j, h⟩ else 0
  let alpha : ℕ → ℝ := fun j => if h : j < n then theta ⟨j, h⟩ - thetaHat ⟨j, h⟩ else 0
  let R : ℕ → ℝ := fun k => ∑ j : Fin n, if (j : ℕ) < k then y j - thetaHat j else 0
  change (∀ i : ℕ, (hi : i + 1 < n) → 0 ≤ R (i + 1)) →
    R n = 0 →
    (∀ i : ℕ, (hi : i + 1 < n) →
      R (i + 1) *
        (thetaHat ⟨i + 1, hi⟩ -
          thetaHat ⟨i, lt_trans (Nat.lt_succ_self i) hi⟩) = 0) →
    (∀ i : ℕ, (hi : i + 1 < n) →
      theta ⟨i, lt_trans (Nat.lt_succ_self i) hi⟩ ≤ theta ⟨i + 1, hi⟩) →
    (∑ i ∈ Finset.range n, alpha i * rho i)
      = ∑ i ∈ Finset.range (n - 1), (alpha i - alpha (i + 1)) * R (i + 1) →
    (∑ i ∈ Finset.range n, alpha i * rho i) ≤ 0
  intro hR_nonneg hnR hcomp hmono hsum
  rw [hsum]
  apply Finset.sum_nonpos
  intro i hi
  rw [Finset.mem_range] at hi
  have hi1 : i + 1 < n := by
    have h1 : i + 1 ≤ n - 1 := Nat.succ_le_of_lt hi
    have h2 : n - 1 < n :=
      Nat.sub_lt (Nat.lt_of_lt_of_le Nat.zero_lt_one hn) Nat.zero_lt_one
    exact Nat.lt_of_le_of_lt h1 h2
  have hin : i < n := lt_trans (Nat.lt_succ_self i) hi1
  have hαi : alpha i = theta ⟨i, hin⟩ - thetaHat ⟨i, hin⟩ := by
    have h1 : alpha i = (if h : i < n then theta ⟨i, h⟩ - thetaHat ⟨i, h⟩ else 0) := rfl
    rw [h1, dif_pos hin]
  have hαs : alpha (i + 1) = theta ⟨i + 1, hi1⟩ - thetaHat ⟨i + 1, hi1⟩ := by
    have h1 : alpha (i + 1) =
        (if h : i + 1 < n then theta ⟨i + 1, h⟩ - thetaHat ⟨i + 1, h⟩ else 0) := rfl
    rw [h1, dif_pos hi1]
  have hkill : R (i + 1) * (thetaHat ⟨i + 1, hi1⟩ - thetaHat ⟨i, hin⟩) = 0 := hcomp i hi1
  have hAr : (thetaHat ⟨i + 1, hi1⟩ - thetaHat ⟨i, hin⟩) * R (i + 1) = 0 := by
    rw [mul_comm]
    exact hkill
  have hθ : theta ⟨i, hin⟩ ≤ theta ⟨i + 1, hi1⟩ := hmono i hi1
  have hprod : 0 ≤ (theta ⟨i + 1, hi1⟩ - theta ⟨i, hin⟩) * R (i + 1) :=
    mul_nonneg (sub_nonneg.mpr hθ) (hR_nonneg i hi1)
  have key : (alpha i - alpha (i + 1)) * R (i + 1)
      = -((theta ⟨i + 1, hi1⟩ - theta ⟨i, hin⟩) * R (i + 1)) := by
    rw [hαi, hαs]
    rw [show theta ⟨i, hin⟩ - thetaHat ⟨i, hin⟩ - (theta ⟨i + 1, hi1⟩ - thetaHat ⟨i + 1, hi1⟩)
        = (thetaHat ⟨i + 1, hi1⟩ - thetaHat ⟨i, hin⟩) -
          (theta ⟨i + 1, hi1⟩ - theta ⟨i, hin⟩) by ring]
    rw [sub_mul, hAr]
    ring
  rw [key]
  exact neg_nonpos.mpr hprod
  /- @proof-region region.target-node.session.67a3f0a37f94282f end -/
