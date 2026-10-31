import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q04.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q04.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q04.ProvedNodes.Node_3778166416_0746af72_b8e45857

open MeasureTheory ProbabilityTheory
open Msc62GroundTruth

open MeasureTheory ProbabilityTheory
namespace Msc62GroundTruth

set_option autoImplicit false in
theorem statopia_math_node_3915940999_868aa0ce : ∀ {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
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
    (hcol : ∀ j : Fin n, ∑ i : Fin m, (X i j) ^ 2 ≤ B ^ 2),
    (P {omega | ∀ j : Fin n,
        |(1 / (m : ℝ)) * ∑ i : Fin m, X i j * epsilon i omega| ≤ lambda / 2}).toReal ≥
      1 - 2 * (n : ℝ) * Real.exp (-(((m : ℝ) ^ 2) * (lambda / 2) ^ 2) /
        (2 * sigma * B ^ 2)) := by
  /- @proof-region region.target-node.session.5edf43ea810e29b6 begin -/
  intro Omega instMS P instProb m n hm hn X epsilon h_epsilon_meas h_epsilon_indep sigma B lambda hsigma hB hlambda h_epsilon_exp_integrable h_epsilon_subGaussian hcol
  have hZmeas : ∀ j : Fin n, Measurable
      (fun omega : Omega => (1 / (m : ℝ)) * ∑ i : Fin m, X i j * epsilon i omega) := by
    intro j
    measurability
  have htail : ∀ j : Fin n, P.real {omega | lambda / 2 ≤
      |(1 / (m : ℝ)) * ∑ i : Fin m, X i j * epsilon i omega|} ≤
      2 * Real.exp (-(((m : ℝ) ^ 2) * (lambda / 2) ^ 2) / (2 * sigma * B ^ 2)) :=
    fun j =>
      statopia_math_node_3778166416_0746af72 P m n hm X epsilon h_epsilon_meas
        h_epsilon_indep sigma B lambda hsigma hB hlambda h_epsilon_exp_integrable
        h_epsilon_subGaussian hcol j
  have hscore : MeasurableSet {omega : Omega | ∀ j : Fin n,
      |(1 / (m : ℝ)) * ∑ i : Fin m, X i j * epsilon i omega| ≤ lambda / 2} := by
    have hset : {omega : Omega | ∀ j : Fin n,
        |(1 / (m : ℝ)) * ∑ i : Fin m, X i j * epsilon i omega| ≤ lambda / 2}
        = ⋂ j : Fin n, {omega : Omega |
            |(1 / (m : ℝ)) * ∑ i : Fin m, X i j * epsilon i omega| ≤ lambda / 2} := by
      ext omega
      simp [Set.mem_iInter]
    rw [hset]
    exact MeasurableSet.iInter fun j => measurableSet_le (hZmeas j).abs measurable_const
  have hcompl_subset : {omega : Omega | ∀ j : Fin n,
      |(1 / (m : ℝ)) * ∑ i : Fin m, X i j * epsilon i omega| ≤ lambda / 2}ᶜ ⊆
      ⋃ j : Fin n, {omega : Omega |
        lambda / 2 ≤ |(1 / (m : ℝ)) * ∑ i : Fin m, X i j * epsilon i omega|} := by
    intro omega homega
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_forall] at homega
    obtain ⟨j, hj⟩ := homega
    exact Set.mem_iUnion.mpr ⟨j, le_of_lt (not_le.mp hj)⟩
  let c : ℝ := 2 * Real.exp (-(((m : ℝ) ^ 2) * (lambda / 2) ^ 2) / (2 * sigma * B ^ 2))
  have hcpos : (0:ℝ) ≤ c :=
    show (0:ℝ) ≤ 2 * Real.exp (-(((m : ℝ) ^ 2) * (lambda / 2) ^ 2) / (2 * sigma * B ^ 2)) by positivity
  have hPt : ∀ j : Fin n, P {omega : Omega |
        lambda / 2 ≤ |(1 / (m : ℝ)) * ∑ i : Fin m, X i j * epsilon i omega|} ≤ ENNReal.ofReal c := by
    intro j
    have hne : P {omega : Omega |
        lambda / 2 ≤ |(1 / (m : ℝ)) * ∑ i : Fin m, X i j * epsilon i omega|} ≠ ⊤ :=
      measure_ne_top P _
    calc P {omega : Omega | lambda / 2 ≤ |(1 / (m : ℝ)) * ∑ i : Fin m, X i j * epsilon i omega|}
        = ENNReal.ofReal (P.real {omega : Omega |
            lambda / 2 ≤ |(1 / (m : ℝ)) * ∑ i : Fin m, X i j * epsilon i omega|}) :=
          (ENNReal.ofReal_toReal hne).symm
      _ ≤ ENNReal.ofReal c := ENNReal.ofReal_le_ofReal (htail j)
  have hUnion : P (⋃ j : Fin n, {omega : Omega |
        lambda / 2 ≤ |(1 / (m : ℝ)) * ∑ i : Fin m, X i j * epsilon i omega|}) ≤
      ENNReal.ofReal (2 * (n : ℝ) * Real.exp (-(((m : ℝ) ^ 2) * (lambda / 2) ^ 2) / (2 * sigma * B ^ 2))) := by
    calc P (⋃ j : Fin n, {omega : Omega |
          lambda / 2 ≤ |(1 / (m : ℝ)) * ∑ i : Fin m, X i j * epsilon i omega|})
        ≤ ∑ j : Fin n, P {omega : Omega |
            lambda / 2 ≤ |(1 / (m : ℝ)) * ∑ i : Fin m, X i j * epsilon i omega|} :=
          MeasureTheory.measure_iUnion_fintype_le P
            (fun j : Fin n => {omega : Omega |
              lambda / 2 ≤ |(1 / (m : ℝ)) * ∑ i : Fin m, X i j * epsilon i omega|})
      _ ≤ ∑ j : Fin n, ENNReal.ofReal c := Finset.sum_le_sum (fun j _ => hPt j)
      _ = ENNReal.ofReal ((n : ℝ) * c) := by
          have hstep : ENNReal.ofReal (∑ j ∈ (Finset.univ : Finset (Fin n)), (fun _ => c) j) =
              ∑ j ∈ (Finset.univ : Finset (Fin n)), ENNReal.ofReal ((fun _ => c) j) := by
            apply ENNReal.ofReal_sum_of_nonneg (f := fun _ => c)
            intro j _
            exact hcpos
          rw [← hstep]
          congr 1
          change ∑ _j : Fin n, c = (n : ℝ) * c
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = ENNReal.ofReal (2 * (n : ℝ) * Real.exp (-(((m : ℝ) ^ 2) * (lambda / 2) ^ 2) / (2 * sigma * B ^ 2))) := by
          congr 1
          show (n : ℝ) * (2 * Real.exp (-(((m : ℝ) ^ 2) * (lambda / 2) ^ 2) / (2 * sigma * B ^ 2))) =
            2 * (n : ℝ) * Real.exp (-(((m : ℝ) ^ 2) * (lambda / 2) ^ 2) / (2 * sigma * B ^ 2))
          ring
  have hcompl_le : P {omega : Omega | ∀ j : Fin n,
        |(1 / (m : ℝ)) * ∑ i : Fin m, X i j * epsilon i omega| ≤ lambda / 2}ᶜ ≤
      ENNReal.ofReal (2 * (n : ℝ) * Real.exp (-(((m : ℝ) ^ 2) * (lambda / 2) ^ 2) / (2 * sigma * B ^ 2))) :=
    le_trans (MeasureTheory.measure_mono hcompl_subset) hUnion
  have hcompl_real : (P {omega : Omega | ∀ j : Fin n,
        |(1 / (m : ℝ)) * ∑ i : Fin m, X i j * epsilon i omega| ≤ lambda / 2}ᶜ).toReal ≤
      2 * (n : ℝ) * Real.exp (-(((m : ℝ) ^ 2) * (lambda / 2) ^ 2) / (2 * sigma * B ^ 2)) := by
    have hr : (0:ℝ) ≤ 2 * (n : ℝ) * Real.exp (-(((m : ℝ) ^ 2) * (lambda / 2) ^ 2) / (2 * sigma * B ^ 2)) := by
      positivity
    calc (P {omega : Omega | ∀ j : Fin n,
          |(1 / (m : ℝ)) * ∑ i : Fin m, X i j * epsilon i omega| ≤ lambda / 2}ᶜ).toReal
        ≤ (ENNReal.ofReal (2 * (n : ℝ) * Real.exp (-(((m : ℝ) ^ 2) * (lambda / 2) ^ 2) / (2 * sigma * B ^ 2)))).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hcompl_le
      _ = 2 * (n : ℝ) * Real.exp (-(((m : ℝ) ^ 2) * (lambda / 2) ^ 2) / (2 * sigma * B ^ 2)) :=
          ENNReal.toReal_ofReal hr
  have hEq : 1 - (P {omega : Omega | ∀ j : Fin n,
        |(1 / (m : ℝ)) * ∑ i : Fin m, X i j * epsilon i omega| ≤ lambda / 2}).toReal =
      (P {omega : Omega | ∀ j : Fin n,
        |(1 / (m : ℝ)) * ∑ i : Fin m, X i j * epsilon i omega| ≤ lambda / 2}ᶜ).toReal := by
    have hne : P Set.univ ≠ ⊤ := measure_ne_top P _
    have hle : P {omega : Omega | ∀ j : Fin n,
          |(1 / (m : ℝ)) * ∑ i : Fin m, X i j * epsilon i omega| ≤ lambda / 2} ≤ P Set.univ :=
      MeasureTheory.measure_mono (Set.subset_univ _)
    have hcomp : P {omega : Omega | ∀ j : Fin n,
          |(1 / (m : ℝ)) * ∑ i : Fin m, X i j * epsilon i omega| ≤ lambda / 2}ᶜ =
        P Set.univ - P {omega : Omega | ∀ j : Fin n,
          |(1 / (m : ℝ)) * ∑ i : Fin m, X i j * epsilon i omega| ≤ lambda / 2} :=
      MeasureTheory.measure_compl hscore (measure_ne_top P _)
    calc 1 - (P {omega : Omega | ∀ j : Fin n,
            |(1 / (m : ℝ)) * ∑ i : Fin m, X i j * epsilon i omega| ≤ lambda / 2}).toReal
        = (P Set.univ).toReal - (P {omega : Omega | ∀ j : Fin n,
            |(1 / (m : ℝ)) * ∑ i : Fin m, X i j * epsilon i omega| ≤ lambda / 2}).toReal := by
          rw [measure_univ, ENNReal.toReal_one]
      _ = (P Set.univ - P {omega : Omega | ∀ j : Fin n,
            |(1 / (m : ℝ)) * ∑ i : Fin m, X i j * epsilon i omega| ≤ lambda / 2}).toReal :=
          (ENNReal.toReal_sub_of_le hle hne).symm
      _ = (P {omega : Omega | ∀ j : Fin n,
            |(1 / (m : ℝ)) * ∑ i : Fin m, X i j * epsilon i omega| ≤ lambda / 2}ᶜ).toReal := by
          rw [hcomp]
  linarith [hEq, hcompl_real]
  /- @proof-region region.target-node.session.5edf43ea810e29b6 end -/

end Msc62GroundTruth
