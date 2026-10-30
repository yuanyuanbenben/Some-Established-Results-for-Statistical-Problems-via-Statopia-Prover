import ProverJobs.job_paper_d731a49b3997405b944f72bca5b16eab.Vocabulary
import ProverJobs.job_paper_d731a49b3997405b944f72bca5b16eab.Base

namespace PaperProofTasks.job_paper_d731a49b3997405b944f72bca5b16eab

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open _root_.PaperProofTasks.job_paper_d731a49b3997405b944f72bca5b16eab.Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace Statlib.Imported
open _root_.Statlib

set_option autoImplicit false in
theorem statopia_math_node_360175676_13120084 : ∀ (m : ℕ) (hm : 1 ≤ m) (Sigma : Matrix (Fin m) (Fin m) ℝ)
    (hSigma_symm : Sigma.IsSymm) (hSigma_psd : Sigma.PosSemidef),
    ∃ ν : Measure (Fin m → ℝ),
      IsProbabilityMeasure ν ∧
      Measurable (fun x : Fin m → ℝ => x) ∧
      (∀ u : Fin m → ℝ,
        Integrable (fun x : Fin m → ℝ => Real.exp (∑ j : Fin m, u j * x j)) ν) ∧
      (∀ u : Fin m → ℝ,
        ∫ x : Fin m → ℝ, Real.exp (∑ j : Fin m, u j * x j) ∂ν =
          Real.exp ((∑ i : Fin m, ∑ j : Fin m, u i * Sigma i j * u j) / 2)) ∧
      Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector
        ν (fun x : Fin m → ℝ => x) Sigma := by
  /- @proof-region region.target-node.session.f11d7e9138ea6b15 begin -/
  intro m hm Sigma hSigma_symm hSigma_psd
  have hmpos : 0 < m := Nat.lt_of_lt_of_le Nat.zero_lt_one hm
  haveI hprob :
      IsProbabilityMeasure (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi m) :=
    Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.standardPi_probability m
  obtain ⟨hXmeas, hXint, hXeq⟩ :=
    Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector_isCenteredGaussianVector
      hmpos Sigma hSigma_psd
  have hAE : ∀ u : Fin m → ℝ,
      AEStronglyMeasurable (fun y : Fin m → ℝ => Real.exp (∑ j : Fin m, u j * y j))
        (Measure.map
          (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector Sigma)
          (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi m)) := by
    intro u
    have hmeasG : Measurable (fun y : Fin m → ℝ => Real.exp (∑ j : Fin m, u j * y j)) := by
      measurability
    exact hmeasG.aestronglyMeasurable
  have hInt : ∀ u : Fin m → ℝ,
      Integrable (fun y : Fin m → ℝ => Real.exp (∑ j : Fin m, u j * y j))
        (Measure.map
          (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector Sigma)
          (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi m)) := by
    intro u
    exact (MeasureTheory.integrable_map_measure
      (f := Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector Sigma)
      (g := fun y : Fin m → ℝ => Real.exp (∑ j : Fin m, u j * y j))
      (hAE u) hXmeas.aemeasurable).mpr (hXint u)
  have hEq : ∀ u : Fin m → ℝ,
      ∫ y : Fin m → ℝ, Real.exp (∑ j : Fin m, u j * y j)
          ∂(Measure.map
            (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector Sigma)
            (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi m)) =
        Real.exp ((∑ i : Fin m, ∑ j : Fin m, u i * Sigma i j * u j) / 2) := by
    intro u
    calc ∫ y : Fin m → ℝ, Real.exp (∑ j : Fin m, u j * y j)
          ∂(Measure.map
            (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector Sigma)
            (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi m))
        = ∫ x : Fin m → ℝ,
            Real.exp (∑ j : Fin m, u j *
              Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector Sigma x j)
            ∂(Statlib.StatFoundation.RandomVariable.Gaussian.standardPi m) :=
          MeasureTheory.integral_map hXmeas.aemeasurable (hAE u)
      _ = Real.exp ((∑ i : Fin m, ∑ j : Fin m, u i * Sigma i j * u j) / 2) := hXeq u
  exact ⟨Measure.map
      (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector Sigma)
      (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi m),
    MeasureTheory.Measure.isProbabilityMeasure_map hXmeas.aemeasurable,
    measurable_id, hInt, hEq, ⟨measurable_id, hInt, hEq⟩⟩
  /- @proof-region region.target-node.session.f11d7e9138ea6b15 end -/

end Statlib.Imported

