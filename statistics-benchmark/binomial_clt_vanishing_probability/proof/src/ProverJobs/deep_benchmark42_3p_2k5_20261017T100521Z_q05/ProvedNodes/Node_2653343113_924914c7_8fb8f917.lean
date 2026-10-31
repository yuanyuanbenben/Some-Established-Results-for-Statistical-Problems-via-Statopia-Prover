import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q05.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q05.Base

open MeasureTheory ProbabilityTheory Filter
open Msc62GroundTruth

open MeasureTheory ProbabilityTheory Filter
namespace Msc62GroundTruth

set_option autoImplicit false in
theorem statopia_math_node_2653343113_924914c7 : ∀ (n : ℕ) (q : NNReal) (hq : q ≤ 1) (s : ℝ),
    charFun (Measure.map (fun k : ℕ => (k : ℝ)) (binomialMeasure n q hq)) s
      = ((((1 : ℝ) - (q : ℝ) : ℝ) : ℂ)
          + ((q : ℝ) : ℂ) * Complex.exp (Complex.I * (s : ℂ))) ^ n := by
  /- @proof-region region.target-node.session.3a1894502064ebdc begin -/
  intro n q hq s
  rw [charFun_apply_real]
  rw [show ∫ y : ℝ, Complex.exp (↑s * ↑y * Complex.I) ∂
        Measure.map (fun k : ℕ => (k : ℝ)) (binomialMeasure n q hq)
      = ∫ k : ℕ, Complex.exp (↑s * ↑(k : ℝ) * Complex.I) ∂ binomialMeasure n q hq
      from integral_map_of_stronglyMeasurable (measurable_of_countable _) (by measurability)]
  unfold binomialMeasure
  rw [show ∫ k : ℕ, Complex.exp (↑s * ↑(k : ℝ) * Complex.I) ∂
        Measure.map (fun i : Fin (n + 1) => (i : ℕ)) ((PMF.binomial q hq n).toMeasure)
      = ∫ i : Fin (n + 1), Complex.exp (↑s * ↑((i : ℕ) : ℝ) * Complex.I) ∂
          ((PMF.binomial q hq n).toMeasure)
      from integral_map_of_stronglyMeasurable (measurable_of_countable _) (by measurability)]
  have hdec : (PMF.binomial q hq n).toMeasure
      = Measure.sum (fun i : Fin (n + 1) => (PMF.binomial q hq n) i • Measure.dirac i) := by
    refine Measure.ext fun t ht => ?_
    rw [PMF.toMeasure_apply_eq_tsum, Measure.sum_apply _ ht]
    refine tsum_congr fun i => ?_
    by_cases hi : i ∈ t <;>
      simp [Measure.smul_apply, Measure.dirac_apply, Set.indicator_apply, hi]
  have hdec' : (PMF.binomial q hq n).toMeasure
      = ∑ i : Fin (n + 1), (PMF.binomial q hq n) i • Measure.dirac i := by
    refine Measure.ext fun t ht => ?_
    rw [hdec, Measure.sum_apply _ ht, Measure.finset_sum_apply, tsum_fintype]
  have hsum : (∫ i : Fin (n + 1), Complex.exp (↑s * ↑((i : ℕ) : ℝ) * Complex.I) ∂
        ((PMF.binomial q hq n).toMeasure))
      = ∑ i : Fin (n + 1), ((PMF.binomial q hq n) i).toReal •
          Complex.exp (↑s * ↑((i : ℕ) : ℝ) * Complex.I) := by
    have hint : ∀ i ∈ (Finset.univ : Finset (Fin (n + 1))),
        Integrable (fun x : Fin (n + 1) => Complex.exp (↑s * ↑((x : ℕ) : ℝ) * Complex.I))
          ((PMF.binomial q hq n) i • Measure.dirac i) := by
      intro i _
      exact (MeasureTheory.integrable_dirac (by simp)).smul_measure
        (PMF.apply_ne_top (PMF.binomial q hq n) i)
    rw [hdec', integral_finset_sum_measure hint]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_smul_measure, integral_dirac]
  rw [hsum]
  have hsub : ((1 : ENNReal) - (q : ENNReal)).toReal = 1 - (q : ℝ) := by
    rw [ENNReal.toReal_sub_of_le (by exact_mod_cast hq) (by simp)]
    simp
  have hmass : ∀ i : Fin (n + 1),
      ((PMF.binomial q hq n) i).toReal
        = (q : ℝ) ^ (i : ℕ) * (1 - (q : ℝ)) ^ (n - (i : ℕ)) * (n.choose (i : ℕ) : ℝ) := by
    intro i
    rw [PMF.binomial_apply]
    simp [hsub]
  have hE : ∀ m : ℕ, Complex.exp (↑s * ↑((m : ℕ) : ℝ) * Complex.I)
      = Complex.exp (Complex.I * (s : ℂ)) ^ m := by
    intro m
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hsmul : ∀ (r : ℝ) (z : ℂ), r • z = (r : ℂ) * z := by
    intro r z
    rw [Algebra.smul_def]
    rfl
  rw [show ((((1 : ℝ) - (q : ℝ) : ℝ) : ℂ)
        + ((q : ℝ) : ℂ) * Complex.exp (Complex.I * (s : ℂ)))
      = ((q : ℝ) : ℂ) * Complex.exp (Complex.I * (s : ℂ))
        + (((1 : ℝ) - (q : ℝ) : ℝ) : ℂ) from add_comm _ _]
  rw [add_pow, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hmass i, hE (i : ℕ), hsmul]
  push_cast
  rw [mul_pow]
  ring
  /- @proof-region region.target-node.session.3a1894502064ebdc end -/

end Msc62GroundTruth
