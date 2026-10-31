import ProverJobs.job_paper_d731a49b3997405b944f72bca5b16eab.Vocabulary
import ProverJobs.job_paper_d731a49b3997405b944f72bca5b16eab.Base
import ProverJobs.job_paper_d731a49b3997405b944f72bca5b16eab.ProvedNodes.Node_360175676_13120084_e3b47c9f

namespace PaperProofTasks.job_paper_d731a49b3997405b944f72bca5b16eab

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open _root_.PaperProofTasks.job_paper_d731a49b3997405b944f72bca5b16eab.Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace Statlib.Imported


set_option autoImplicit false in
theorem statopia_math_node_2042219946_a98a529d : ∀ (m : ℕ) (hm : 3 ≤ m)
    (R : Matrix (Fin m) (Fin m) ℝ)
    (hR_symm : R.IsSymm)
    (hR_psd : R.PosSemidef)
    (hR_diag : ∀ i : Fin m, R i i = 1)
    (hR_off : ∀ i j : Fin m, i ≠ j → R i j < 1)
        (hS_psd : (R.map (fun x : ℝ => max x 0)).PosSemidef)
        (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (ζ : Ω → Fin m → ℝ)
        (hζ : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector μ ζ R),
        (μ {ω : Ω | ∀ j : Fin m, ζ ω j ≤ Real.sqrt (Real.log (m : ℝ))}).toReal ≤
          Statlib.StatFoundation.RandomVariable.Gaussian.slepianCorrectionFactor m
              (R.map (fun x : ℝ => max x 0)) (Real.sqrt (Real.log (m : ℝ))) *
            (Statlib.StatFoundation.RandomVariable.Gaussian.standardGaussianCDF
              (Real.sqrt (Real.log (m : ℝ)))) ^ m := by
  /- @proof-region region.target-node.session.f0bf304650788ef2 begin -/
  classical
  intro m hm R hR_symm hR_psd hR_diag hR_off hS_psd Ω instΩ μ instμ ζ hζ
  haveI : IsProbabilityMeasure (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi m) :=
    Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.standardPi_probability m
  set t : ℝ := Real.sqrt (Real.log (m : ℝ)) with ht
  have ht0 : 0 ≤ t := by rw [ht]; exact Real.sqrt_nonneg _
  have htr : Matrix.transpose R = R := hR_symm
  have hsymm : ∀ i j : Fin m, R i j = R j i := fun i j => (congrFun (congrFun htr i) j).symm
  have hm0 : 0 < m := by omega
  have hcR : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector
      (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi m)
      (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector R) R :=
    Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector_isCenteredGaussianVector
      hm0 R hR_psd
  have hcS : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector
      (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi m)
      (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector
        (R.map (fun x : ℝ => max x 0)))
      (R.map (fun x : ℝ => max x 0)) :=
    Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector_isCenteredGaussianVector
      hm0 (R.map (fun x : ℝ => max x 0)) hS_psd
  have horth : MeasurableSet {y : Fin m → ℝ | ∀ j : Fin m, y j ≤ t} := by
    have h : {y : Fin m → ℝ | ∀ j : Fin m, y j ≤ t}
        = ⋂ j : Fin m, {y : Fin m → ℝ | y j ≤ t} := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [h]
    exact MeasurableSet.iInter (fun j => measurableSet_le (measurable_pi_apply j) measurable_const)
  have hslep := Statlib.StatFoundation.RandomVariable.Gaussian.slepian_lowerOrthant_bounds
      m hm R hsymm hR_psd hR_diag (fun i j hij => hR_off i j hij)
      (R.map (fun x : ℝ => max x 0)) rfl hS_psd
      (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi m)
      (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector R) hcR
      (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector
        (R.map (fun x : ℝ => max x 0))) hcS t ht0
  have hmap := Statlib.StatFoundation.RandomVariable.Gaussian.map_eq_map_of_centeredGaussianVector
      μ (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi m) ζ
      (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector R) R hζ hcR hR_psd
  have step1 : μ {ω : Ω | ∀ j : Fin m, ζ ω j ≤ t}
      = (Measure.map ζ μ) {y : Fin m → ℝ | ∀ j : Fin m, y j ≤ t} :=
    (Measure.map_apply hζ.1 horth).symm
  have step2 : (Measure.map ζ μ) {y : Fin m → ℝ | ∀ j : Fin m, y j ≤ t}
      = (Measure.map (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector R)
          (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi m))
          {y : Fin m → ℝ | ∀ j : Fin m, y j ≤ t} := by
    rw [hmap]
  have step3 : (Measure.map (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector R)
          (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi m))
          {y : Fin m → ℝ | ∀ j : Fin m, y j ≤ t}
      = (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi m)
          {x : Fin m → ℝ |
            ∀ j : Fin m,
              Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector R x j ≤ t} :=
    Measure.map_apply hcR.1 horth
  have hkey : μ {ω : Ω | ∀ j : Fin m, ζ ω j ≤ t}
      = (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi m)
          {x : Fin m → ℝ |
            ∀ j : Fin m,
              Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector R x j ≤ t} := by
    rw [step1, step2, step3]
  rw [hkey]
  exact le_trans hslep.1 hslep.2
  /- @proof-region region.target-node.session.f0bf304650788ef2 end -/

end Statlib.Imported

