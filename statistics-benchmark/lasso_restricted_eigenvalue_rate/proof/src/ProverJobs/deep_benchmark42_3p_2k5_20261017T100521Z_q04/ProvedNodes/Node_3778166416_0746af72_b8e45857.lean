import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q04.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q04.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q04.ProvedNodes.Node_174105582_dad1d727_7418a5fc
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q04.ProvedNodes.Node_4162532863_4d0277a7_a0b41224
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q04.ProvedNodes.Node_570887230_87c93162_7814af42



open MeasureTheory ProbabilityTheory
open Msc62GroundTruth

open MeasureTheory ProbabilityTheory
namespace Msc62GroundTruth

set_option autoImplicit false in
theorem statopia_math_node_3778166416_0746af72 : ∀ {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (m n : ℕ) (hm : 1 ≤ m)
    (X : Fin m → Fin n → ℝ)
    (epsilon : Fin m → Omega → ℝ)
    (h_epsilon_meas : ∀ i : Fin m, Measurable (epsilon i))
    (h_epsilon_indep : iIndepFun (β := fun _ : Fin m => ℝ) epsilon P)
    (sigma B lambda : ℝ)
    (hsigma : 0 < sigma) (hB : 0 < B) (hlambda : 0 < lambda)
    (h_epsilon_exp_integrable : ∀ (i : Fin m) (t : ℝ),
      Integrable (fun omega => Real.exp (t * epsilon i omega)) P)
    (h_epsilon_subGaussian : ∀ (i : Fin m) (t : ℝ),
      ∫ omega, Real.exp (t * epsilon i omega) ∂P ≤ Real.exp (sigma * t ^ 2 / 2))
    (hcol : ∀ j : Fin n, ∑ i : Fin m, (X i j) ^ 2 ≤ B ^ 2)
    (j : Fin n),
    P.real {omega | lambda / 2 ≤
        |(1 / (m : ℝ)) * ∑ i : Fin m, X i j * epsilon i omega|} ≤
      2 * Real.exp (-(((m : ℝ) ^ 2) * (lambda / 2) ^ 2) / (2 * sigma * B ^ 2)) := by
  /- @proof-region region.target-node.session.a0fa755f9c91d963 begin -/
  intro Omega instO P instP m n hm X epsilon h_epsilon_meas h_epsilon_indep sigma B lambda
    hsigma hB hlambda h_epsilon_exp_integrable h_epsilon_subGaussian hcol j
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    have h1 : (0 : ℕ) < m := lt_of_lt_of_le Nat.zero_lt_one hm
    exact_mod_cast h1
  have hZeq : ∀ omega : Omega,
      (∑ i : Fin m, (X i j / (m : ℝ)) * epsilon i omega)
        = (1 / (m : ℝ)) * ∑ i : Fin m, X i j * epsilon i omega := by
    intro omega
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    ring
  have h_ws := statopia_math_node_4162532863_4d0277a7 P m epsilon sigma (le_of_lt hsigma)
    h_epsilon_meas h_epsilon_indep h_epsilon_exp_integrable h_epsilon_subGaussian
    (fun i => X i j / (m : ℝ))
  have hInt : ∀ t : ℝ,
      Integrable (fun omega =>
        Real.exp (t * ((1 / (m : ℝ)) * ∑ i : Fin m, X i j * epsilon i omega))) P := by
    intro t
    simpa only [hZeq] using (h_ws t).1
  have hsum_sq :
      (∑ i : Fin m, (X i j / (m : ℝ)) ^ 2) = (∑ i : Fin m, (X i j) ^ 2) / (m : ℝ) ^ 2 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [div_pow]
  have hcj_le : sigma * ∑ i : Fin m, (X i j / (m : ℝ)) ^ 2 ≤ sigma * B ^ 2 / (m : ℝ) ^ 2 := by
    rw [hsum_sq]
    have hcolj := hcol j
    have hm2 : (0 : ℝ) < (m : ℝ) ^ 2 := pow_pos hmpos 2
    have hdiv : (∑ i : Fin m, (X i j) ^ 2) / (m : ℝ) ^ 2 ≤ B ^ 2 / (m : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hcolj (le_of_lt hm2)
    calc sigma * ((∑ i : Fin m, (X i j) ^ 2) / (m : ℝ) ^ 2)
        ≤ sigma * (B ^ 2 / (m : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hdiv (le_of_lt hsigma)
      _ = sigma * B ^ 2 / (m : ℝ) ^ 2 := by ring
  have hcpos : 0 < sigma * B ^ 2 / (m : ℝ) ^ 2 := by
    have hm2 : (0 : ℝ) < (m : ℝ) ^ 2 := pow_pos hmpos 2
    have hB2 : (0 : ℝ) < B ^ 2 := pow_pos hB 2
    exact div_pos (mul_pos hsigma hB2) hm2
  have hmgf : ∀ t : ℝ,
      ∫ omega,
          Real.exp (t * ((1 / (m : ℝ)) * ∑ i : Fin m, X i j * epsilon i omega)) ∂P
        ≤ Real.exp ((sigma * B ^ 2 / (m : ℝ) ^ 2) * t ^ 2 / 2) := by
    intro t
    have h2 : ∫ omega,
          Real.exp (t * ((1 / (m : ℝ)) * ∑ i : Fin m, X i j * epsilon i omega)) ∂P
        ≤ Real.exp ((sigma * ∑ i : Fin m, (X i j / (m : ℝ)) ^ 2) * t ^ 2 / 2) := by
      simpa only [hZeq] using (h_ws t).2
    refine le_trans h2 (Real.exp_le_exp.mpr ?_)
    have ht : (0 : ℝ) ≤ t ^ 2 / 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_right hcj_le ht
    convert hmul using 1 <;> ring
  have hlambda2 : (0 : ℝ) < lambda / 2 := by linarith
  have htail := statopia_math_node_174105582_dad1d727 P
    (fun omega => (1 / (m : ℝ)) * ∑ i : Fin m, X i j * epsilon i omega)
    (sigma * B ^ 2 / (m : ℝ) ^ 2) (lambda / 2) hcpos hlambda2 hInt hmgf
  have hexp : Real.exp (-((lambda / 2) ^ 2) / (2 * (sigma * B ^ 2 / (m : ℝ) ^ 2)))
      = Real.exp (-(((m : ℝ) ^ 2) * (lambda / 2) ^ 2) / (2 * sigma * B ^ 2)) := by
    congr 1
    have hsigma_ne : sigma ≠ 0 := ne_of_gt hsigma
    have hB_ne : B ≠ 0 := ne_of_gt hB
    have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hmpos
    have hm2_ne : (m : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hm_ne
    field_simp
  rw [hexp] at htail
  simpa using htail
  /- @proof-region region.target-node.session.a0fa755f9c91d963 end -/

end Msc62GroundTruth
