import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q04.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q04.Base

open MeasureTheory ProbabilityTheory
open Msc62GroundTruth

open MeasureTheory ProbabilityTheory
namespace Msc62GroundTruth

set_option autoImplicit false in
theorem statopia_math_node_4187378725_a4837b16 : ∀ (m n : ℕ) (hm : 1 ≤ m)
    (X : Fin m → Fin n → ℝ)
    (S : Finset (Fin n))
    (betaStar : Fin n → ℝ)
    (h_support : ∀ j, j ∉ S → betaStar j = 0)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (eps : Fin m → ℝ)
    (hscore : ∀ j : Fin n,
      |(1 / (m : ℝ)) * ∑ i : Fin m, X i j * eps i| ≤ lambda / 2)
    (betaHat : Fin n → ℝ)
    (hmin : ∀ gamma : Fin n → ℝ,
      (1 / (2 * (m : ℝ))) *
          ∑ i : Fin m, (eps i + ∑ j : Fin n, X i j * (betaStar j - betaHat j)) ^ 2 +
        lambda * ∑ j : Fin n, |betaHat j|
      ≤
      (1 / (2 * (m : ℝ))) *
          ∑ i : Fin m, (eps i + ∑ j : Fin n, X i j * (betaStar j - gamma j)) ^ 2 +
        lambda * ∑ j : Fin n, |gamma j|),
    (1 / (m : ℝ)) *
        ∑ i : Fin m, (∑ j : Fin n, X i j * (betaHat j - betaStar j)) ^ 2
      ≤ 3 * lambda * (∑ j ∈ S, |betaHat j - betaStar j|) -
          lambda * (∑ j ∈ Finset.univ.filter (fun j => j ∉ S),
            |betaHat j - betaStar j|) ∧
    (∑ j ∈ Finset.univ.filter (fun j => j ∉ S), |betaHat j - betaStar j|)
      ≤ 3 * (∑ j ∈ S, |betaHat j - betaStar j|) := by
  /- @proof-region region.target-node.session.fdc3c2f09207cfdc begin -/
  intro m n hm X S betaStar h_support lambda hlambda eps hscore betaHat hmin
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    have h : (0 : ℕ) < m := by omega
    exact_mod_cast h
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt hmpos
  set u : Fin n → ℝ := fun j => (1 / (m : ℝ)) * ∑ i : Fin m, X i j * eps i with hu
  set r : Fin m → ℝ := fun i => ∑ j : Fin n, X i j * (betaHat j - betaStar j) with hr
  set Q : ℝ := (1 / (m : ℝ)) * ∑ i : Fin m, (r i) ^ 2 with hQ
  set A : ℝ := ∑ j ∈ S, |betaHat j - betaStar j| with hA
  set B : ℝ := ∑ j ∈ Finset.univ.filter (fun j => j ∉ S), |betaHat j - betaStar j| with hB
  have hri : ∀ i : Fin m, r i = ∑ j : Fin n, X i j * (betaHat j - betaStar j) := by
    intro i
    rw [hr]
  have huj : ∀ j : Fin n, u j = (1 / (m : ℝ)) * ∑ i : Fin m, X i j * eps i := by
    intro j
    rw [hu]
  have hscore' : ∀ j : Fin n, |u j| ≤ lambda / 2 := by
    intro j
    rw [huj j]
    exact hscore j
  have hm1 : (1 / (m : ℝ)) * (m : ℝ) = 1 := by
    field_simp
  have hmm : (m : ℝ) * (1 / (m : ℝ)) = 1 := by
    rw [mul_comm, hm1]
  have hmul : ∀ j : Fin n, (m : ℝ) * u j = ∑ i : Fin m, X i j * eps i := by
    intro j
    rw [huj j, ← mul_assoc, hmm, one_mul]
  have hstep1 : (1 / (2 * (m : ℝ))) * ∑ i : Fin m, (eps i - r i) ^ 2
        + lambda * ∑ j : Fin n, |betaHat j|
      ≤ (1 / (2 * (m : ℝ))) * ∑ i : Fin m, (eps i) ^ 2
        + lambda * ∑ j : Fin n, |betaStar j| := by
    have h := hmin betaStar
    have key1 : ∀ i : Fin m, (eps i + ∑ j : Fin n, X i j * (betaStar j - betaHat j)) = eps i - r i := by
      intro i
      have hinner : (∑ j : Fin n, X i j * (betaStar j - betaHat j)) = - r i := by
        have h1 : (∑ j : Fin n, X i j * (betaStar j - betaHat j))
            = ∑ j : Fin n, -(X i j * (betaHat j - betaStar j)) := by
          apply Finset.sum_congr rfl
          intro j _
          ring
        rw [h1, Finset.sum_neg_distrib, hri i]
      rw [hinner, sub_eq_add_neg]
    have key2 : ∀ i : Fin m, (eps i + ∑ j : Fin n, X i j * (betaStar j - betaStar j)) = eps i := by
      intro i
      simp
    have e1 : (∑ i : Fin m, (eps i + ∑ j : Fin n, X i j * (betaStar j - betaHat j)) ^ 2)
        = ∑ i : Fin m, (eps i - r i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [key1 i]
    have e2 : (∑ i : Fin m, (eps i + ∑ j : Fin n, X i j * (betaStar j - betaStar j)) ^ 2)
        = ∑ i : Fin m, (eps i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [key2 i]
    rw [e1, e2] at h
    exact h
  have hcross : (∑ i : Fin m, eps i * r i)
      = ∑ j : Fin n, (∑ i : Fin m, X i j * eps i) * (betaHat j - betaStar j) := by
    have expand : ∀ i : Fin m,
        eps i * r i = ∑ j : Fin n, (X i j * eps i) * (betaHat j - betaStar j) := by
      intro i
      rw [hri i, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    calc (∑ i : Fin m, eps i * r i)
        = ∑ i : Fin m, ∑ j : Fin n, (X i j * eps i) * (betaHat j - betaStar j) :=
          Finset.sum_congr rfl (fun i _ => expand i)
      _ = ∑ j : Fin n, ∑ i : Fin m, (X i j * eps i) * (betaHat j - betaStar j) :=
          Finset.sum_comm
      _ = ∑ j : Fin n, (∑ i : Fin m, X i j * eps i) * (betaHat j - betaStar j) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_mul]
  have hbig : (∑ i : Fin m, eps i * r i)
      = (m : ℝ) * ∑ j : Fin n, u j * (betaHat j - betaStar j) := by
    rw [hcross, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [← mul_assoc, hmul j]
  have hP : (1 / (m : ℝ)) * ∑ i : Fin m, eps i * r i
      = ∑ j : Fin n, u j * (betaHat j - betaStar j) := by
    rw [hbig, ← mul_assoc, hm1, one_mul]
  have hexp : (1 / (2 * (m : ℝ))) * ∑ i : Fin m, (eps i - r i) ^ 2
        - (1 / (2 * (m : ℝ))) * ∑ i : Fin m, (eps i) ^ 2
      = Q / 2 - (1 / (m : ℝ)) * ∑ i : Fin m, eps i * r i := by
    rw [hQ]
    have hbracket : (∑ i : Fin m, (eps i - r i) ^ 2) - (∑ i : Fin m, (eps i) ^ 2)
        = -2 * (∑ i : Fin m, eps i * r i) + ∑ i : Fin m, (r i) ^ 2 := by
      have h1 : (∑ i : Fin m, (eps i - r i) ^ 2) - (∑ i : Fin m, (eps i) ^ 2)
          = ∑ i : Fin m, ((eps i - r i) ^ 2 - (eps i) ^ 2) := by
        rw [Finset.sum_sub_distrib]
      rw [h1]
      have h2 : (∑ i : Fin m, ((eps i - r i) ^ 2 - (eps i) ^ 2))
          = ∑ i : Fin m, (-2 * (eps i * r i) + (r i) ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [h2, Finset.sum_add_distrib]
      rw [show (∑ i : Fin m, -2 * (eps i * r i)) = -2 * ∑ i : Fin m, eps i * r i from by
        rw [Finset.mul_sum]]
    have h2m : (1 : ℝ) / (2 * (m : ℝ)) = (1 / 2) * (1 / (m : ℝ)) := by
      field_simp
    calc (1 / (2 * (m : ℝ))) * ∑ i : Fin m, (eps i - r i) ^ 2
          - (1 / (2 * (m : ℝ))) * ∑ i : Fin m, (eps i) ^ 2
        = (1 / (2 * (m : ℝ))) *
            ((∑ i : Fin m, (eps i - r i) ^ 2) - (∑ i : Fin m, (eps i) ^ 2)) := by
          ring
      _ = (1 / (2 * (m : ℝ))) *
            (-2 * (∑ i : Fin m, eps i * r i) + ∑ i : Fin m, (r i) ^ 2) := by
          rw [hbracket]
      _ = ((1 / (m : ℝ)) * ∑ i : Fin m, (r i) ^ 2) / 2
            - (1 / (m : ℝ)) * ∑ i : Fin m, eps i * r i := by
          rw [h2m]
          ring
  have hmemS : (Finset.univ.filter (fun j : Fin n => j ∈ S)) = S := by
    ext j
    simp
  have hAB : (∑ j : Fin n, |betaHat j - betaStar j|) = A + B := by
    rw [hA, hB]
    have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin n))
      (fun j : Fin n => j ∈ S) (fun j : Fin n => |betaHat j - betaStar j|)
    rw [← hsplit, hmemS]
  have hC : (∑ j : Fin n, u j * (betaHat j - betaStar j))
      ≤ (1 / 2) * (lambda * A + lambda * B) := by
    have h1 : (∑ j : Fin n, u j * (betaHat j - betaStar j))
        ≤ ∑ j : Fin n, |u j| * |betaHat j - betaStar j| := by
      apply Finset.sum_le_sum
      intro j _
      calc u j * (betaHat j - betaStar j) ≤ |u j * (betaHat j - betaStar j)| := le_abs_self _
        _ = |u j| * |betaHat j - betaStar j| := abs_mul _ _
    have h2 : (∑ j : Fin n, |u j| * |betaHat j - betaStar j|)
        ≤ ∑ j : Fin n, (lambda / 2) * |betaHat j - betaStar j| := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right (hscore' j) (abs_nonneg _)
    have h3 : (∑ j : Fin n, (lambda / 2) * |betaHat j - betaStar j|)
        = (lambda / 2) * (A + B) := by
      rw [← hAB, Finset.mul_sum]
    have hmid : (∑ j : Fin n, u j * (betaHat j - betaStar j)) ≤ (lambda / 2) * (A + B) := by
      linarith [h1, h2, h3]
    calc (∑ j : Fin n, u j * (betaHat j - betaStar j)) ≤ (lambda / 2) * (A + B) := hmid
      _ = (1 / 2) * (lambda * A + lambda * B) := by ring
  have hD : (∑ j : Fin n, |betaStar j|) - (∑ j : Fin n, |betaHat j|) ≤ A - B := by
    have hSstar : (∑ j : Fin n, |betaStar j|) = ∑ j ∈ S, |betaStar j| :=
      (Finset.sum_subset (Finset.subset_univ S)
        (fun x _ hx => by simp [h_support x hx])).symm
    have hB' : B = ∑ j ∈ Finset.univ.filter (fun j : Fin n => j ∉ S), |betaHat j| := by
      rw [hB]
      apply Finset.sum_congr rfl
      intro j hj
      have hjs : j ∉ S := (Finset.mem_filter.mp hj).2
      rw [h_support j hjs]
      simp
    have hShat : (∑ j : Fin n, |betaHat j|)
        = (∑ j ∈ S, |betaHat j|) + ∑ j ∈ Finset.univ.filter (fun j : Fin n => j ∉ S), |betaHat j| := by
      have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin n))
        (fun j : Fin n => j ∈ S) (fun j : Fin n => |betaHat j|)
      rw [← hsplit, hmemS]
    have hsub : (∑ j ∈ S, |betaStar j|) - (∑ j ∈ S, |betaHat j|) ≤ A := by
      rw [hA, ← Finset.sum_sub_distrib]
      apply Finset.sum_le_sum
      intro j _
      have h1 : |betaStar j| ≤ |betaStar j - betaHat j| + |betaHat j| := by
        have hh := abs_add_le (betaStar j - betaHat j) (betaHat j)
        rwa [sub_add_cancel] at hh
      have h2 : |betaStar j - betaHat j| = |betaHat j - betaStar j| := abs_sub_comm _ _
      linarith
    rw [hSstar, hShat, ← hB']
    linarith
  have hQnn : 0 ≤ Q := by
    rw [hQ]
    exact mul_nonneg (le_of_lt (div_pos one_pos hmpos))
      (Finset.sum_nonneg (fun i _ => sq_nonneg (r i)))
  have hA1 : (1 / (2 * (m : ℝ))) * ∑ i : Fin m, (eps i - r i) ^ 2
        - (1 / (2 * (m : ℝ))) * ∑ i : Fin m, (eps i) ^ 2
      ≤ lambda * ((∑ j : Fin n, |betaStar j|) - ∑ j : Fin n, |betaHat j|) := by
    linarith [hstep1]
  have hD' : lambda * ((∑ j : Fin n, |betaStar j|) - ∑ j : Fin n, |betaHat j|)
      ≤ lambda * (A - B) :=
    mul_le_mul_of_nonneg_left hD (le_of_lt hlambda)
  have hQle : Q ≤ 3 * lambda * A - lambda * B := by
    nlinarith [hA1, hexp, hP, hD', hC]
  constructor
  · exact hQle
  · have h : lambda * B ≤ lambda * (3 * A) := by nlinarith [hQle, hQnn]
    by_contra hlt
    exact absurd h (not_le.mpr (mul_lt_mul_of_pos_left (not_le.mp hlt) hlambda))
  /- @proof-region region.target-node.session.fdc3c2f09207cfdc end -/

end Msc62GroundTruth
