import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OfflineDPRoot

/-- Exact finite label expansion of iid sampling from a finite mixture. -/
theorem mixture_product_law {X J : Type*} [MeasurableSpace X] [Fintype J]
    (P : Measure X) [IsProbabilityMeasure P] (R : J → Measure X)
    [∀ j, IsProbabilityMeasure (R j)] (p : J → ℝ≥0∞)
    (hP : P = ∑ j, p j • R j) (n : ℕ) :
    Measure.pi (fun _ : Fin n => P) =
      ∑ lab : Fin n → J, (∏ i, p (lab i)) • Measure.pi (fun i => R (lab i)) := by
  classical
  apply Measure.pi_eq
  intro A hA
  simp only [Measure.finset_sum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.pi_pi]
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : Fin n) (j : J) => p j * R j (A i))]
  apply Finset.prod_congr rfl
  intro i _
  rw [hP, Measure.finset_sum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]

/-- Exact finite-product integral expansion; useful for likelihood ratios and
indicators, without changing the density representative or true sample law. -/
theorem mixture_product_lintegral {X J : Type*} [MeasurableSpace X] [Fintype J]
    (P : Measure X) [IsProbabilityMeasure P] (R : J → Measure X)
    [∀ j, IsProbabilityMeasure (R j)] (p : J → ℝ≥0∞)
    (hP : P = ∑ j, p j • R j) (n : ℕ) (F : (Fin n → X) → ℝ≥0∞) :
    ∫⁻ x, F x ∂Measure.pi (fun _ : Fin n => P) =
      ∑ lab : Fin n → J, (∏ i, p (lab i)) *
        ∫⁻ x, F x ∂Measure.pi (fun i => R (lab i)) := by
  rw [mixture_product_law P R p hP n, lintegral_finset_sum_measure]
  simp only [lintegral_smul_measure, smul_eq_mul]

theorem label_weights_sum_one {J : Type*} [Fintype J]
    (p : J → ℝ≥0∞) (hp : ∑ j, p j = 1) (n : ℕ) :
    (∑ lab : Fin n → J, ∏ i, p (lab i)) = 1 := by
  classical
  rw [← Fintype.sum_pow, hp, one_pow]

#print axioms mixture_product_law
#print axioms mixture_product_lintegral
#print axioms label_weights_sum_one
end OfflineDPRoot
