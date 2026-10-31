import Statlib.StatFoundation.Statistics.Asymptotic.ScoreCLT
import Statlib.StatFoundation.Convergence.Resampling.GaussianMaxComparison
import Statlib.StatFoundation.Convergence.AnalysisTools.GaussianMaxAnticoncentration
import Statlib.StatFoundation.Statistics.Asymptotic.LAN
import Statlib.StatFoundation.Convergence.AnalysisTools.SmoothMax
import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.Vocabulary
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.Base
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.ProvedNodes.Node_1572792732_43168f8b_9f1c2f60

namespace PaperProofTasks.job_paper_de3065fb922748188f3a0354eba90ed9

open _root_.PaperProofTasks.job_paper_de3065fb922748188f3a0354eba90ed9.Statlib.Imported
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

set_option autoImplicit false in
theorem statopia_math_node_2728575719_e5a804ed : ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℕ) (hp : 1 ≤ p) (X : Ω → Fin p → ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (hGauss : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector μ X Sigma)
    (hpos : ∀ j : Fin p, 0 < ∫ ω, (X ω j) ^ 2 ∂μ),
    ∀ j : Fin p,
      (∫ ω, X ω j ∂μ = 0) ∧
        (∀ r : ℝ, 0 ≤ r →
          μ {ω | X ω j ≤ -r} ≤
            ENNReal.ofReal (Real.exp (-((r / Statlib.Imported.coordStdDev μ X j) ^ 2) / 2))) := by
  /- @proof-region region.target-node.session.4818624d2aa76fd1 begin -/
  intro Ω _ μ _ p hp X Sigma hGauss hpos j
  let S : Matrix (Fin p) (Fin p) ℝ := (2:ℝ)⁻¹ • (Sigma + Sigma.transpose)
  have hS : S.PosSemidef :=
    Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector.posSemidef_symmetrizedCovariance hGauss hp
  have hmap : Measure.map X μ =
      Measure.map (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector S)
        (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi p) :=
    Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector.map_eq_canonicalGaussianVector hGauss hp
  have hXmeas : Measurable X := hGauss.measurable
  have hXjmeas : Measurable (fun ω => X ω j) := (measurable_pi_apply j).comp hXmeas
  have hp0 : 0 < p := by omega
  have hcanon : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector
      (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi p)
      (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector S) S :=
    Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector_isCenteredGaussianVector hp0 S hS
  haveI hPi : IsProbabilityMeasure (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi p) := by
    have himg : IsProbabilityMeasure
        (Measure.map (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector S)
          (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi p)) := by
      rw [← hmap]
      exact Measure.isProbabilityMeasure_map hXmeas.aemeasurable
    exact (Measure.isProbabilityMeasure_map_iff hcanon.measurable.aemeasurable).mp himg
  set u : Fin p → ℝ := (fun k => if k = j then 1 else 0) with hu
  have hlin := Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector.map_linearCombination
    (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi p)
    (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector S) S hcanon hS u
  have hLHS : (fun z => ∑ k, u k * Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector S z k)
      = (fun z => Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector S z j) := by
    funext z
    simp only [hu]
    have hsum : (∑ k, (if k = j then (1:ℝ) else 0) *
          Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector S z k)
        = (if j = j then (1:ℝ) else 0) *
          Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector S z j := by
      refine Finset.sum_eq_single j ?_ ?_
      · intro k _ hk; simp [if_neg hk]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    rw [hsum]; simp
  obtain ⟨V, hlaw_canon⟩ : ∃ V : NNReal,
      Measure.map (fun z => Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector S z j)
        (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi p) = gaussianReal 0 V := by
    have h := hlin
    rw [hLHS] at h
    exact ⟨_, h⟩
  have hCGVmeas : Measurable (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector S) := hcanon.measurable
  have hlawX : Measure.map (fun ω => X ω j) μ = gaussianReal 0 V := by
    have step : Measure.map (fun v : Fin p → ℝ => v j) (Measure.map X μ)
        = Measure.map (fun v : Fin p → ℝ => v j)
            (Measure.map (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector S)
              (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi p)) := by
      rw [hmap]
    rw [Measure.map_map (measurable_pi_apply j) hXmeas,
        Measure.map_map (measurable_pi_apply j) hCGVmeas] at step
    simpa only [Function.comp_apply] using step.trans hlaw_canon
  constructor
  · have h1 : ∫ y, y ∂(Measure.map (fun ω => X ω j) μ) = ∫ ω, X ω j ∂μ :=
      MeasureTheory.integral_map_of_stronglyMeasurable hXjmeas measurable_id.stronglyMeasurable
    rw [← h1, hlawX, ProbabilityTheory.integral_id_gaussianReal]
  · intro r hr
    have h2 : ∫ ω, (X ω j) ^ 2 ∂μ = (V : ℝ) := by
      have h1 : ∫ y, y ^ 2 ∂(Measure.map (fun ω => X ω j) μ) = ∫ ω, (X ω j) ^ 2 ∂μ :=
        MeasureTheory.integral_map_of_stronglyMeasurable hXjmeas (continuous_id.pow 2).stronglyMeasurable
      rw [← h1, hlawX]
      have hvar := ProbabilityTheory.variance_of_integral_eq_zero (X := id) (μ := gaussianReal 0 V)
        measurable_id.aemeasurable
        (by simpa using ProbabilityTheory.integral_id_gaussianReal (μ := 0) (v := V))
      rw [ProbabilityTheory.variance_id_gaussianReal] at hvar
      simpa using hvar.symm
    have hVpos : 0 < (V : ℝ) := by
      rw [← h2]; exact hpos j
    have hσeq : coordStdDev μ X j = Real.sqrt (V : ℝ) := by
      have hdef : coordStdDev μ X j = Real.sqrt (∫ ω, (X ω j) ^ 2 ∂μ) := rfl
      rw [hdef, h2]
    have hσpos : 0 < coordStdDev μ X j := by
      rw [hσeq]; exact Real.sqrt_pos.mpr hVpos
    have hscale : Measure.map (fun x : ℝ => coordStdDev μ X j * x) (gaussianReal 0 1) = gaussianReal 0 V := by
      have hsqrt := Statlib.StatFoundation.Statistics.Asymptotic.gaussianReal_map_sqrt_mul (V : ℝ) V.coe_nonneg
      rw [show (⟨(V : ℝ), V.coe_nonneg⟩ : NNReal) = V from Subtype.ext rfl] at hsqrt
      rw [show (fun x : ℝ => coordStdDev μ X j * x) = (fun x : ℝ => Real.sqrt (V : ℝ) * x) from by
        funext x; rw [hσeq]]
      exact hsqrt
    have hset_eq : {ω | X ω j ≤ -r} = (fun ω => X ω j) ⁻¹' Set.Iic (-r) := by
      ext ω; simp [Set.mem_preimage, Set.mem_Iic]
    have hmeas_set : μ {ω | X ω j ≤ -r} = (gaussianReal 0 V) (Set.Iic (-r)) := by
      rw [hset_eq, ← Measure.map_apply hXjmeas (s := Set.Iic (-r)) measurableSet_Iic, hlawX]
    have hset2 : (fun x : ℝ => coordStdDev μ X j * x) ⁻¹' Set.Iic (-r)
        = Set.Iic (-(r / coordStdDev μ X j)) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_Iic]
      rw [show -(r / coordStdDev μ X j) = -r / coordStdDev μ X j from by ring]
      rw [le_div_iff₀ hσpos]
      constructor
      · intro hh; rwa [mul_comm x (coordStdDev μ X j)]
      · intro hh; rwa [mul_comm x (coordStdDev μ X j)] at hh
    rw [hmeas_set, ← hscale,
      Measure.map_apply (f := fun x : ℝ => coordStdDev μ X j * x) (by fun_prop)
        (s := Set.Iic (-r)) measurableSet_Iic,
      hset2, ProbabilityTheory.gaussianReal_apply_eq_integral 0 (by norm_num : (1 : NNReal) ≠ 0)]
    apply ENNReal.ofReal_le_ofReal
    exact statopia_math_node_1572792732_43168f8b (r / coordStdDev μ X j) (div_nonneg hr hσpos.le)
  /- @proof-region region.target-node.session.4818624d2aa76fd1 end -/

end Statlib.Imported

