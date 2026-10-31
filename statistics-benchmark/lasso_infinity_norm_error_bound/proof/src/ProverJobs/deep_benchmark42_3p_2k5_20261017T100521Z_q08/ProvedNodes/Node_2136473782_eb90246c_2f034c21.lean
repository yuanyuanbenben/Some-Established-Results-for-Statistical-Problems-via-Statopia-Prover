import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q08.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q08.Base

open MeasureTheory Matrix ProbabilityTheory

open MeasureTheory Matrix ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_2136473782_eb90246c : ∀ (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (X : Matrix (Fin n) (Fin d) ℝ)
    (S : Finset (Fin d))
    (thetaStar : Fin d → ℝ)
    (hsupport : ∀ j : Fin d, j ∉ S → thetaStar j = 0)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (w : Fin n → ℝ)
    (thetaHat : Fin d → ℝ)
    (hmin : ∀ eta : Fin d → ℝ,
      dotProduct (X *ᵥ thetaStar + w - X *ᵥ thetaHat)
          (X *ᵥ thetaStar + w - X *ᵥ thetaHat) / (2 * (n : ℝ))
        + lambda * ∑ j, |thetaHat j|
      ≤ dotProduct (X *ᵥ thetaStar + w - X *ᵥ eta)
          (X *ᵥ thetaStar + w - X *ᵥ eta) / (2 * (n : ℝ))
        + lambda * ∑ j, |eta j|)
    (hnoise : ∀ j : Fin d, |((Xᵀ *ᵥ w) j) / (n : ℝ)| ≤ lambda / 2),
    (∑ j : Fin d, if j ∈ S then (0 : ℝ) else |(thetaHat - thetaStar) j|)
      ≤ 3 * (∑ j : Fin d, if j ∈ S then |(thetaHat - thetaStar) j| else (0 : ℝ)) := by
  /- @proof-region region.target-node.session.2f0bad29612e20cd begin -/
  intro n d hn hd X S thetaStar hsupport lambda hlambda w thetaHat hmin hnoise
  have hnpos : (0:ℝ) < (n:ℝ) := by
    have h1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    linarith
  have h2npos : (0:ℝ) < 2 * (n:ℝ) := by linarith
  have hnne : (n:ℝ) ≠ 0 := ne_of_gt hnpos
  have h2nne : 2 * (n:ℝ) ≠ 0 := ne_of_gt h2npos
  set Delta : Fin d → ℝ := thetaHat - thetaStar with hDelta
  set A : ℝ := ∑ j : Fin d, if j ∈ S then (0:ℝ) else |Delta j| with hA
  set B : ℝ := ∑ j : Fin d, if j ∈ S then |Delta j| else (0:ℝ) with hB
  obtain ⟨r, hr⟩ : ∃ x : Fin n → ℝ, x = X *ᵥ Delta := ⟨X *ᵥ Delta, rfl⟩
  have hth : ∀ j, thetaStar j + Delta j = thetaHat j := by
    intro j
    rw [hDelta]
    simp only [Pi.sub_apply]
    ring
  have hvecmul : Matrix.vecMul w X = Xᵀ *ᵥ w := by
    ext j
    simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hresL : X *ᵥ thetaStar + w - X *ᵥ thetaHat = w - r := by
    rw [hr, hDelta, Matrix.mulVec_sub]
    abel
  have hresR : X *ᵥ thetaStar + w - X *ᵥ thetaStar = w := by abel
  have hdpexp : (w - r) ⬝ᵥ (w - r) = w ⬝ᵥ w - 2 * (w ⬝ᵥ r) + r ⬝ᵥ r := by
    simp only [dotProduct, Pi.sub_apply]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hAB : A + B = ∑ j : Fin d, |Delta j| := by
    rw [hA, hB, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j ∈ S
    · have h1 : (if j ∈ S then (0:ℝ) else |Delta j|) = 0 := if_pos hj
      have h2 : (if j ∈ S then |Delta j| else (0:ℝ)) = |Delta j| := if_pos hj
      rw [h1, h2]; ring
    · have h1 : (if j ∈ S then (0:ℝ) else |Delta j|) = |Delta j| := if_neg hj
      have h2 : (if j ∈ S then |Delta j| else (0:ℝ)) = 0 := if_neg hj
      rw [h1, h2]; ring
  have hmin0 := hmin thetaStar
  rw [hresL, hresR] at hmin0
  rw [hdpexp] at hmin0
  have hkey : (r ⬝ᵥ r) / (2 * (n:ℝ)) ≤ (w ⬝ᵥ r) / (n:ℝ) + lambda * ((∑ j, |thetaStar j|) - (∑ j, |thetaHat j|)) := by
    have e1 : (r ⬝ᵥ r - 2 * (w ⬝ᵥ r)) / (2 * (n:ℝ)) = (r ⬝ᵥ r) / (2 * (n:ℝ)) - (w ⬝ᵥ r) / (n:ℝ) := by
      field_simp
    have e2 : (w ⬝ᵥ w - 2 * (w ⬝ᵥ r) + r ⬝ᵥ r) / (2 * (n:ℝ)) - (w ⬝ᵥ w) / (2 * (n:ℝ)) = (r ⬝ᵥ r - 2 * (w ⬝ᵥ r)) / (2 * (n:ℝ)) := by
      field_simp
      ring
    linarith [hmin0, e1, e2]
  have hRRnn : 0 ≤ (r ⬝ᵥ r) / (2 * (n:ℝ)) := by
    have h1 : 0 ≤ r ⬝ᵥ r := by
      simp only [dotProduct]
      exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (r i))
    exact div_nonneg h1 (le_of_lt h2npos)
  have hWRb : (w ⬝ᵥ r) / (n:ℝ) ≤ (lambda / 2) * (A + B) := by
    have hsplit : w ⬝ᵥ r = ∑ j, (Xᵀ *ᵥ w) j * Delta j := by
      rw [hr, Matrix.dotProduct_mulVec, hvecmul]
      simp only [dotProduct]
    have hdiv : (w ⬝ᵥ r) / (n:ℝ) = ∑ j, ((Xᵀ *ᵥ w) j / (n:ℝ)) * Delta j := by
      rw [hsplit, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hdiv]
    calc ∑ j, ((Xᵀ *ᵥ w) j / (n:ℝ)) * Delta j
        ≤ ∑ j, |((Xᵀ *ᵥ w) j / (n:ℝ)) * Delta j| := Finset.sum_le_sum (fun j _ => le_abs_self _)
      _ = ∑ j, |(Xᵀ *ᵥ w) j / (n:ℝ)| * |Delta j| := by
          apply Finset.sum_congr rfl
          intro j _
          rw [abs_mul]
      _ ≤ ∑ j, (lambda / 2) * |Delta j| :=
          Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hnoise j) (abs_nonneg _))
      _ = (lambda / 2) * (A + B) := by rw [← Finset.mul_sum, ← hAB]
  have hSigBA : (∑ j : Fin d, |thetaStar j|) - (∑ j : Fin d, |thetaHat j|) ≤ B - A := by
    rw [← Finset.sum_sub_distrib]
    rw [hB, hA, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : j ∈ S
    · have h1 : (if j ∈ S then |Delta j| else (0:ℝ)) = |Delta j| := if_pos hj
      have h2 : (if j ∈ S then (0:ℝ) else |Delta j|) = 0 := if_pos hj
      rw [h1, h2]
      have hle : |thetaStar j| ≤ |thetaHat j| + |Delta j| := by
        have h := abs_add_le (thetaHat j) (-(Delta j))
        rw [abs_neg] at h
        have hrw : thetaHat j + -(Delta j) = thetaStar j := by
          rw [hDelta]
          simp only [Pi.sub_apply]
          ring
        rw [hrw] at h
        exact h
      linarith
    · have h1 : (if j ∈ S then |Delta j| else (0:ℝ)) = 0 := if_neg hj
      have h2 : (if j ∈ S then (0:ℝ) else |Delta j|) = |Delta j| := if_neg hj
      rw [h1, h2]
      have hS : thetaStar j = 0 := hsupport j hj
      have htj : thetaHat j = Delta j := by rw [← hth j, hS]; ring
      rw [hS, htj]
      simp only [abs_zero]
      exact le_refl _
  have hSHb : lambda * ((∑ j, |thetaStar j|) - (∑ j, |thetaHat j|)) ≤ lambda * (B - A) :=
    mul_le_mul_of_nonneg_left hSigBA (le_of_lt hlambda)
  have hchain : (0:ℝ) ≤ (lambda / 2) * (A + B) + lambda * (B - A) := by
    nlinarith [hRRnn, hkey, hWRb, hSHb]
  nlinarith [hchain, hlambda]
  /- @proof-region region.target-node.session.2f0bad29612e20cd end -/
