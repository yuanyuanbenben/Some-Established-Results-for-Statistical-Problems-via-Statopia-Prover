import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q04.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q04.Base

open MeasureTheory ProbabilityTheory
open Msc62GroundTruth

open MeasureTheory ProbabilityTheory
namespace Msc62GroundTruth

set_option autoImplicit false in
theorem statopia_math_node_1762459067_67761fda : ∀ (n : ℕ) (S : Finset (Fin n)) (h : Fin n → ℝ) (kappa lambda Q : ℝ)
    (hkappa : 0 < kappa) (hlambda : 0 < lambda) (hQ : 0 ≤ Q)
    (hMain :
      Q ≤ 3 * lambda * (∑ j ∈ S, |h j|) -
        lambda * (∑ j ∈ Finset.univ.filter (fun j => j ∉ S), |h j|))
    (hCone : kappa ^ 2 * (∑ j : Fin n, (h j) ^ 2) ≤ Q),
    Q ≤ 16 * lambda ^ 2 * (S.card : ℝ) / kappa ^ 2 ∧
      (∑ j : Fin n, |h j|) ≤ 8 * lambda * (S.card : ℝ) / kappa ^ 2 ∧
        (∑ j : Fin n, (h j) ^ 2) ≤ 16 * lambda ^ 2 * (S.card : ℝ) / kappa ^ 4 := by
  /- @proof-region region.target-node.session.4d87f36cbaf88d38 begin -/
  intro n S h kappa lambda Q hkappa hlambda hQ hMain hCone
  set A : ℝ := ∑ j ∈ S, |h j| with hAdef
  set B : ℝ := ∑ j ∈ Finset.univ.filter (fun j => j ∉ S), |h j| with hBdef
  set W : ℝ := ∑ j : Fin n, (h j) ^ 2 with hWdef
  have hA : 0 ≤ A := by
    rw [hAdef]
    exact Finset.sum_nonneg fun j _ => abs_nonneg _
  have hB : 0 ≤ B := by
    rw [hBdef]
    exact Finset.sum_nonneg fun j _ => abs_nonneg _
  have hW : 0 ≤ W := by
    rw [hWdef]
    exact Finset.sum_nonneg fun j _ => sq_nonneg _
  have hs : 0 ≤ (S.card : ℝ) := by positivity
  have hk2 : 0 < kappa ^ 2 := by positivity
  have hfil : (Finset.univ : Finset (Fin n)).filter (fun j => j ∈ S) = S := by
    ext j
    simp
  have hsplit_abs : (∑ j : Fin n, |h j|) = A + B := by
    rw [hAdef, hBdef]
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin n))
      (fun j => j ∈ S) (fun j => |h j|), hfil]
  have hsplit_sq : W =
      (∑ j ∈ S, (h j) ^ 2) + ∑ j ∈ Finset.univ.filter (fun j => j ∉ S), (h j) ^ 2 := by
    rw [hWdef]
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin n))
      (fun j => j ∈ S) (fun j => (h j) ^ 2), hfil]
  have hoff : 0 ≤ ∑ j ∈ Finset.univ.filter (fun j => j ∉ S), (h j) ^ 2 :=
    Finset.sum_nonneg fun j _ => sq_nonneg (h j)
  have hSsq : (∑ j ∈ S, (h j) ^ 2) ≤ W := by
    rw [hsplit_sq]
    linarith [hoff]
  have hCS : A ^ 2 ≤ (S.card : ℝ) * W := by
    have habs : (∑ j ∈ S, |h j| ^ 2) = ∑ j ∈ S, (h j) ^ 2 := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      exact sq_abs (h j)
    have hsq : (∑ j ∈ S, |h j|) ^ 2 ≤ (S.card : ℝ) * ∑ j ∈ S, (h j) ^ 2 := by
      have h := sq_sum_le_card_mul_sum_sq (s := S) (f := fun j => |h j|)
      rw [habs] at h
      exact h
    rw [hAdef]
    calc (∑ j ∈ S, |h j|) ^ 2 ≤ (S.card : ℝ) * ∑ j ∈ S, (h j) ^ 2 := hsq
      _ ≤ (S.card : ℝ) * W := mul_le_mul_of_nonneg_left hSsq hs
  have hMain' : Q ≤ 3 * lambda * A - lambda * B := by linarith [hMain, hAdef, hBdef]
  have hCone' : kappa ^ 2 * W ≤ Q := by linarith [hCone, hWdef]
  have hB3A : B ≤ 3 * A := by
    have h1 : lambda * B ≤ 3 * lambda * A := by linarith [hMain', hQ]
    by_contra hcon
    rw [not_le] at hcon
    have h2 : lambda * (3 * A) < lambda * B := mul_lt_mul_of_pos_left hcon hlambda
    linarith [h1]
  have hAQ : Q ≤ 3 * lambda * A := by
    linarith [hMain', mul_nonneg hlambda.le hB]
  have hkA : kappa ^ 2 * A ^ 2 ≤ (S.card : ℝ) * Q := by
    have h1 : kappa ^ 2 * A ^ 2 ≤ kappa ^ 2 * ((S.card : ℝ) * W) :=
      mul_le_mul_of_nonneg_left hCS hk2.le
    have h2 : (S.card : ℝ) * (kappa ^ 2 * W) ≤ (S.card : ℝ) * Q :=
      mul_le_mul_of_nonneg_left hCone' hs
    linarith [h1, h2]
  have hcubic : kappa ^ 2 * A ^ 2 + lambda * (S.card : ℝ) * B ≤
      3 * lambda * (S.card : ℝ) * A := by
    have h1 : (S.card : ℝ) * Q ≤ (S.card : ℝ) * (3 * lambda * A - lambda * B) :=
      mul_le_mul_of_nonneg_left hMain' hs
    linarith [hkA, h1]
  have hnonneg16 : 0 ≤ 16 * lambda ^ 2 * (S.card : ℝ) := by
    have h1 : 0 ≤ lambda ^ 2 * (S.card : ℝ) := mul_nonneg (sq_nonneg lambda) hs
    linarith [h1]
  have hQpoly : Q * kappa ^ 2 ≤ 16 * lambda ^ 2 * (S.card : ℝ) := by
    by_cases hA0 : A = 0
    · rw [hA0] at hMain'
      have hQle : Q ≤ 0 := by linarith [hMain', mul_nonneg hlambda.le hB]
      have hQ0 : Q = 0 := le_antisymm hQle hQ
      rw [hQ0]
      simpa using hnonneg16
    · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
      have hAle : kappa ^ 2 * A ≤ 3 * lambda * (S.card : ℝ) := by
        have hsq : kappa ^ 2 * A ^ 2 ≤ 3 * lambda * (S.card : ℝ) * A := by
          have hb : 0 ≤ lambda * (S.card : ℝ) * B :=
            mul_nonneg (mul_nonneg hlambda.le hs) hB
          linarith [hcubic, hb]
        by_contra hcon
        rw [not_le] at hcon
        have h2 : (3 * lambda * (S.card : ℝ)) * A < (kappa ^ 2 * A) * A :=
          mul_lt_mul_of_pos_right hcon hApos
        linarith [hsq]
      have h1 : kappa ^ 2 * Q ≤ kappa ^ 2 * (3 * lambda * A) :=
        mul_le_mul_of_nonneg_left hAQ hk2.le
      have h2 : 3 * lambda * (kappa ^ 2 * A) ≤ 3 * lambda * (3 * lambda * (S.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hAle (by positivity)
      have h3 : kappa ^ 2 * Q ≤ 9 * lambda ^ 2 * (S.card : ℝ) := by nlinarith [h1, h2]
      have h4 : 0 ≤ lambda ^ 2 * (S.card : ℝ) := mul_nonneg (sq_nonneg lambda) hs
      nlinarith [h3, h4]
  have hgoal1 : Q ≤ 16 * lambda ^ 2 * (S.card : ℝ) / kappa ^ 2 := by
    rw [le_div_iff₀ hk2]
    exact hQpoly
  have hgoal3 : (∑ j : Fin n, (h j) ^ 2) ≤ 16 * lambda ^ 2 * (S.card : ℝ) / kappa ^ 4 := by
    have hk4 : 0 < kappa ^ 4 := by positivity
    have h1 : kappa ^ 2 * (kappa ^ 2 * W) ≤ kappa ^ 2 * Q :=
      mul_le_mul_of_nonneg_left hCone' hk2.le
    have h3 : W * kappa ^ 4 ≤ 16 * lambda ^ 2 * (S.card : ℝ) := by nlinarith [h1, hQpoly]
    rw [le_div_iff₀ hk4, ← hWdef]
    exact h3
  have hgoal2 : (∑ j : Fin n, |h j|) ≤ 8 * lambda * (S.card : ℝ) / kappa ^ 2 := by
    rw [hsplit_abs, le_div_iff₀ hk2]
    by_cases hs0 : (S.card : ℝ) = 0
    · have hsW : (S.card : ℝ) * W = 0 := by rw [hs0]; ring
      have hA2 : A ^ 2 = 0 := by
        have h1 : A ^ 2 ≤ 0 := by linarith [hCS, hsW]
        have h2 : 0 ≤ A ^ 2 := sq_nonneg A
        linarith
      have hA0 : A = 0 := sq_eq_zero_iff.mp hA2
      have hB0 : B = 0 := by linarith [hB3A, hA0, hB]
      rw [hA0, hB0, hs0]
      simp
    · have hs0' : 0 < (S.card : ℝ) := lt_of_le_of_ne hs (Ne.symm hs0)
      have hL : 0 < lambda * (S.card : ℝ) := mul_pos hlambda hs0'
      have hmul : lambda * (S.card : ℝ) * (kappa ^ 2 * (A + B)) ≤
          lambda * (S.card : ℝ) * (4 * (lambda * (S.card : ℝ))) := by
        linarith [mul_le_mul_of_nonneg_left hcubic hk2.le,
          sq_nonneg (kappa ^ 2 * A - 2 * (lambda * (S.card : ℝ)))]
      have hbrace : kappa ^ 2 * (A + B) ≤ 4 * (lambda * (S.card : ℝ)) := by
        by_contra hcon
        rw [not_le] at hcon
        have h2 : lambda * (S.card : ℝ) * (4 * (lambda * (S.card : ℝ))) <
            lambda * (S.card : ℝ) * (kappa ^ 2 * (A + B)) :=
          mul_lt_mul_of_pos_left hcon hL
        linarith [hmul]
      linarith [hbrace, mul_nonneg hlambda.le hs]
  exact ⟨hgoal1, hgoal2, hgoal3⟩
  /- @proof-region region.target-node.session.4d87f36cbaf88d38 end -/

end Msc62GroundTruth
