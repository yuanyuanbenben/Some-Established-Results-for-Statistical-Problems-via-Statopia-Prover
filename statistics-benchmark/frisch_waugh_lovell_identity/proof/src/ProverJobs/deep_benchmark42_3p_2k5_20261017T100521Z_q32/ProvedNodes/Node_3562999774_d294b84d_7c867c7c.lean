import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q32.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q32.Base

open Matrix

open Matrix

set_option autoImplicit false in
theorem statopia_math_node_3562999774_d294b84d : ∀ (n p q : ℕ)
    (X1 : Matrix (Fin n) (Fin p) ℝ)
    (X2 : Matrix (Fin n) (Fin q) ℝ)
    (y : Fin n → ℝ)
    (betaHat : Fin p → ℝ)
    (gammaHat : Fin q → ℝ)
    (hmin : ∀ beta : Fin p → ℝ, ∀ gamma : Fin q → ℝ,
      dotProduct (y - X1 *ᵥ betaHat - X2 *ᵥ gammaHat)
          (y - X1 *ᵥ betaHat - X2 *ᵥ gammaHat) ≤
        dotProduct (y - X1 *ᵥ beta - X2 *ᵥ gamma)
          (y - X1 *ᵥ beta - X2 *ᵥ gamma)),
    X1.transpose *ᵥ (y - X1 *ᵥ betaHat - X2 *ᵥ gammaHat) = 0 ∧
      X2.transpose *ᵥ (y - X1 *ᵥ betaHat - X2 *ᵥ gammaHat) = 0 := by
  /- @proof-region region.target-node.session.6808a63cb20a6280 begin -/
  intro n p q X1 X2 y betaHat gammaHat hmin
  have expand : ∀ (a b : Fin n → ℝ) (t : ℝ),
      dotProduct (a + t • b) (a + t • b)
        = dotProduct a a + 2 * t * dotProduct a b + t ^ 2 * dotProduct b b := by
    intro a b t
    simp only [dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have key : ∀ (a c : ℝ), 0 ≤ c → (∀ t : ℝ, 0 ≤ 2 * t * a + t ^ 2 * c) → a = 0 := by
    intro a c hc H
    have h1 := H (-a / (c + 1))
    have hs : (0:ℝ) < c + 1 := by linarith
    have hne1 : c + 1 ≠ 0 := by linarith
    have e : 2 * (-a / (c + 1)) * a + (-a / (c + 1)) ^ 2 * c
        = -a ^ 2 * (c + 2) / (c + 1) ^ 2 := by
      have hne2 : (c + 1) ^ 2 ≠ 0 := pow_ne_zero 2 hne1
      field_simp
      ring
    have h2 : (0:ℝ) ≤ -a ^ 2 * (c + 2) / (c + 1) ^ 2 := by rw [← e]; exact h1
    have h3 : (0:ℝ) ≤ -a ^ 2 * (c + 2) := by
      have hd : (0:ℝ) < (c + 1) ^ 2 := pow_pos hs 2
      rcases (div_nonneg_iff.mp h2) with ⟨hN, _⟩ | ⟨_, hD⟩
      · exact hN
      · linarith
    have hc2 : (0:ℝ) < c + 2 := by linarith
    have h4 : a ^ 2 * (c + 2) ≤ 0 := by linarith
    have ha2 : a ^ 2 = 0 := by
      by_contra haz
      have hpos : (0:ℝ) < a ^ 2 := lt_of_le_of_ne (sq_nonneg a) (Ne.symm haz)
      have hprod : (0:ℝ) < a ^ 2 * (c + 2) := mul_pos hpos hc2
      linarith
    have haa : a * a = 0 := by rwa [pow_two] at ha2
    exact mul_self_eq_zero.mp haa
  have fam1 : ∀ u : Fin p → ℝ,
      dotProduct (y - X1 *ᵥ betaHat - X2 *ᵥ gammaHat) (X1 *ᵥ u) = 0 := by
    intro u
    have hrv : ∀ t : ℝ, y - X1 *ᵥ (betaHat - t • u) - X2 *ᵥ gammaHat
        = (y - X1 *ᵥ betaHat - X2 *ᵥ gammaHat) + t • (X1 *ᵥ u) := by
      intro t
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul]
      abel
    have hquad : ∀ t : ℝ,
        0 ≤ 2 * t * dotProduct (y - X1 *ᵥ betaHat - X2 *ᵥ gammaHat) (X1 *ᵥ u)
          + t ^ 2 * dotProduct (X1 *ᵥ u) (X1 *ᵥ u) := by
      intro t
      have h := hmin (betaHat - t • u) gammaHat
      rw [hrv t] at h
      rw [expand (y - X1 *ᵥ betaHat - X2 *ᵥ gammaHat) (X1 *ᵥ u) t] at h
      linarith
    have hc : 0 ≤ dotProduct (X1 *ᵥ u) (X1 *ᵥ u) := by
      simp only [dotProduct]
      exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
    exact key _ _ hc hquad
  have fam2 : ∀ w : Fin q → ℝ,
      dotProduct (y - X1 *ᵥ betaHat - X2 *ᵥ gammaHat) (X2 *ᵥ w) = 0 := by
    intro w
    have hrv : ∀ t : ℝ, y - X1 *ᵥ betaHat - X2 *ᵥ (gammaHat - t • w)
        = (y - X1 *ᵥ betaHat - X2 *ᵥ gammaHat) + t • (X2 *ᵥ w) := by
      intro t
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul]
      abel
    have hquad : ∀ t : ℝ,
        0 ≤ 2 * t * dotProduct (y - X1 *ᵥ betaHat - X2 *ᵥ gammaHat) (X2 *ᵥ w)
          + t ^ 2 * dotProduct (X2 *ᵥ w) (X2 *ᵥ w) := by
      intro t
      have h := hmin betaHat (gammaHat - t • w)
      rw [hrv t] at h
      rw [expand (y - X1 *ᵥ betaHat - X2 *ᵥ gammaHat) (X2 *ᵥ w) t] at h
      linarith
    have hc : 0 ≤ dotProduct (X2 *ᵥ w) (X2 *ᵥ w) := by
      simp only [dotProduct]
      exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
    exact key _ _ hc hquad
  have hcoord1 : ∀ j : Fin p,
      (X1.transpose *ᵥ (y - X1 *ᵥ betaHat - X2 *ᵥ gammaHat)) j = 0 := by
    intro j
    have hb := fam1 (fun k => if k = j then (1:ℝ) else 0)
    have heq : (X1.transpose *ᵥ (y - X1 *ᵥ betaHat - X2 *ᵥ gammaHat)) j
        = dotProduct (y - X1 *ᵥ betaHat - X2 *ᵥ gammaHat)
            (X1 *ᵥ (fun k => if k = j then (1:ℝ) else 0)) := by
      simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply]
      apply Finset.sum_congr rfl
      intro i _
      have hinner : (∑ k, X1 i k * (if k = j then (1:ℝ) else 0)) = X1 i j := by
        rw [Finset.sum_eq_single j (fun b _ hb => by simp [hb])
          (fun hj => absurd (Finset.mem_univ j) hj)]
        simp
      rw [hinner]
      ring
    rw [heq, hb]
  have hcoord2 : ∀ j : Fin q,
      (X2.transpose *ᵥ (y - X1 *ᵥ betaHat - X2 *ᵥ gammaHat)) j = 0 := by
    intro j
    have hb := fam2 (fun k => if k = j then (1:ℝ) else 0)
    have heq : (X2.transpose *ᵥ (y - X1 *ᵥ betaHat - X2 *ᵥ gammaHat)) j
        = dotProduct (y - X1 *ᵥ betaHat - X2 *ᵥ gammaHat)
            (X2 *ᵥ (fun k => if k = j then (1:ℝ) else 0)) := by
      simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply]
      apply Finset.sum_congr rfl
      intro i _
      have hinner : (∑ k, X2 i k * (if k = j then (1:ℝ) else 0)) = X2 i j := by
        rw [Finset.sum_eq_single j (fun b _ hb => by simp [hb])
          (fun hj => absurd (Finset.mem_univ j) hj)]
        simp
      rw [hinner]
      ring
    rw [heq, hb]
  refine ⟨?_, ?_⟩
  · funext j
    exact hcoord1 j
  · funext j
    exact hcoord2 j
  /- @proof-region region.target-node.session.6808a63cb20a6280 end -/
