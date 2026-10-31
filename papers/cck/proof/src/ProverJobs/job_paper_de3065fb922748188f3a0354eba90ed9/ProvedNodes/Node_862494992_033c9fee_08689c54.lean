import Statlib.StatFoundation.Statistics.Asymptotic.ScoreCLT
import Statlib.StatFoundation.Convergence.Resampling.GaussianMaxComparison
import Statlib.StatFoundation.Convergence.AnalysisTools.GaussianMaxAnticoncentration
import Statlib.StatFoundation.Statistics.Asymptotic.LAN
import Statlib.StatFoundation.Convergence.AnalysisTools.SmoothMax
import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.Vocabulary
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.Base
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.ProvedNodes.Node_2518884549_dcb952d7_baff574e
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.ProvedNodes.Node_3326423151_cf0f28e2_13ed3acb
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.ExternalNodes.Node_169d50a09ba170573f49
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.ExternalNodes.Node_6515c10a3b2a6920f75d

namespace PaperProofTasks.job_paper_de3065fb922748188f3a0354eba90ed9



open _root_.PaperProofTasks.job_paper_de3065fb922748188f3a0354eba90ed9.Statlib.Imported
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

set_option autoImplicit false in
theorem statopia_math_node_862494992_033c9fee : ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : ℕ) (hq : 1 ≤ q)
    (V : Ω → Fin q → ℝ) (hV : Measurable V)
    (Sigma : Matrix (Fin q) (Fin q) ℝ) (nu : Fin q → ℝ)
    (b : ℝ) (hb : 0 ≤ b)
    (hVar : ∀ k : Fin q, Sigma k k = 1)
    (hMean : ∀ k : Fin q, nu k = ∫ ω, V ω k ∂μ)
    (hCov : ∀ k l : Fin q, Sigma k l = ∫ ω, (V ω k - nu k) * (V ω l - nu l) ∂μ)
    (hGauss : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector μ
      (fun ω k => V ω k - nu k) Sigma)
    (hL2 : ∀ k : Fin q, MemLp (fun ω => V ω k) 2 μ)
    (hCorr : ∀ k l : Fin q, k ≠ l → Sigma k l < 1)
    (hnu_nonneg : ∀ k : Fin q, 0 ≤ nu k)
    (hnu_le : ∀ k : Fin q, nu k ≤ b),
      (Measure.map (fun ω => coordMax V ω) μ) ≪ volume ∧
        Measurable (fun x : ℝ =>
          (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2) *
            (∑ j : Fin q,
              Real.exp (nu j * x - nu j ^ 2 / 2) *
                (Statlib.Imported.gaussianVecMeasure
                  (fun k : {k : Fin q // k ≠ j} => nu k.1 + (x - nu j) * Sigma k.1 j)
                  (fun k l : {k : Fin q // k ≠ j} =>
                    Sigma k.1 l.1 - Sigma k.1 j * Sigma l.1 j)
                  {y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ x}).toReal)) ∧
        (∀ (s : Set ℝ), MeasurableSet s →
          (Measure.map (fun ω => coordMax V ω) μ) s =
            ∫⁻ x in s, ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2) *
              (∑ j : Fin q,
                Real.exp (nu j * x - nu j ^ 2 / 2) *
                  (Statlib.Imported.gaussianVecMeasure
                    (fun k : {k : Fin q // k ≠ j} => nu k.1 + (x - nu j) * Sigma k.1 j)
                    (fun k l : {k : Fin q // k ≠ j} =>
                      Sigma k.1 l.1 - Sigma k.1 j * Sigma l.1 j)
                    {y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ x}).toReal)) ∂volume) ∧
        (∀ z : ℝ,
          0 ≤ ∑ j : Fin q,
            Real.exp (nu j * z - nu j ^ 2 / 2) *
              (Statlib.Imported.gaussianVecMeasure
                (fun k : {k : Fin q // k ≠ j} => nu k.1 + (z - nu j) * Sigma k.1 j)
                (fun k l : {k : Fin q // k ≠ j} =>
                  Sigma k.1 l.1 - Sigma k.1 j * Sigma l.1 j)
                {y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ z}).toReal) ∧
        Monotone (fun z : ℝ =>
          ∑ j : Fin q,
            Real.exp (nu j * z - nu j ^ 2 / 2) *
              (Statlib.Imported.gaussianVecMeasure
                (fun k : {k : Fin q // k ≠ j} => nu k.1 + (z - nu j) * Sigma k.1 j)
                (fun k l : {k : Fin q // k ≠ j} =>
                  Sigma k.1 l.1 - Sigma k.1 j * Sigma l.1 j)
                {y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ z}).toReal) := by
  /- @proof-region region.target-node.session.67d42183a87c0e0d begin -/
  intro Ω _ μ _ q hq V hV Sigma nu b hb hVar hMean hCov hGauss hL2 hCorr hnu_nonneg hnu_le
  let G : ℝ → ℝ := fun z =>
    ∑ j : Fin q, Real.exp (nu j * z - (nu j) ^ 2 / 2) *
      (Statlib.Imported.gaussianVecMeasure
        (fun k : {k : Fin q // k ≠ j} => nu k.1 + (z - nu j) * Sigma k.1 j)
        (fun k l : {k : Fin q // k ≠ j} => Sigma k.1 l.1 - Sigma k.1 j * Sigma l.1 j)
        {y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ z}).toReal
  have hG_nonneg : ∀ z : ℝ, 0 ≤ G z := by
    intro z
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg
  have hG_mono : Monotone G := by
    intro a b hab
    simp only [G]
    refine Finset.sum_le_sum (fun j _ => ?_)
    refine mul_le_mul ?_ ?_ ?_ ?_
    · apply Real.exp_le_exp.mpr
      have h1 : nu j * a ≤ nu j * b := mul_le_mul_of_nonneg_left hab (hnu_nonneg j)
      linarith
    · set Sj : Matrix {k : Fin q // k ≠ j} {k : Fin q // k ≠ j} ℝ :=
        (fun k l => Sigma k.1 l.1 - Sigma k.1 j * Sigma l.1 j) with hSj
      set ma : {k : Fin q // k ≠ j} → ℝ := (fun k => nu k.1 + (a - nu j) * Sigma k.1 j) with hma
      set mb : {k : Fin q // k ≠ j} → ℝ := (fun k => nu k.1 + (b - nu j) * Sigma k.1 j) with hmb
      by_cases hA : ((((1:ℝ)/2) • (Sj + Sj.transpose))).PosSemidef
      · simp only [Statlib.Imported.gaussianVecMeasure, dif_pos hA]
        haveI hprob : IsProbabilityMeasure (Statlib.Imported.stdGaussianPi {k : Fin q // k ≠ j}) := by
          unfold Statlib.Imported.stdGaussianPi
          infer_instance
        have hsa : MeasurableSet {y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ a} := by
          have h : MeasurableSet (⋂ k : {k : Fin q // k ≠ j}, {y : {k : Fin q // k ≠ j} → ℝ | y k ≤ a}) := by
            refine MeasurableSet.iInter (fun k => ?_)
            have hk : Measurable (fun y : {k : Fin q // k ≠ j} → ℝ => y k) := measurable_pi_apply k
            exact measurableSet_le hk measurable_const
          simpa only [Set.setOf_forall] using h
        have hsb : MeasurableSet {y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ b} := by
          have h : MeasurableSet (⋂ k : {k : Fin q // k ≠ j}, {y : {k : Fin q // k ≠ j} → ℝ | y k ≤ b}) := by
            refine MeasurableSet.iInter (fun k => ?_)
            have hk : Measurable (fun y : {k : Fin q // k ≠ j} → ℝ => y k) := measurable_pi_apply k
            exact measurableSet_le hk measurable_const
          simpa only [Set.setOf_forall] using h
        have hmv : Measurable (fun y : {k : Fin q // k ≠ j} → ℝ => Matrix.mulVec (Matrix.PosSemidef.sqrt hA) y) := by
          have hcont : Continuous (fun y : {k : Fin q // k ≠ j} → ℝ => Matrix.mulVec (Matrix.PosSemidef.sqrt hA) y) :=
            LinearMap.continuous_of_finiteDimensional (Matrix.mulVecLin (Matrix.PosSemidef.sqrt hA))
          exact hcont.measurable
        have hsub : (fun y : {k : Fin q // k ≠ j} → ℝ => ma + Matrix.mulVec (Matrix.PosSemidef.sqrt hA) y) ⁻¹' {y | ∀ k, y k ≤ a} ⊆
            (fun y : {k : Fin q // k ≠ j} → ℝ => mb + Matrix.mulVec (Matrix.PosSemidef.sqrt hA) y) ⁻¹' {y | ∀ k, y k ≤ b} := by
          intro y hy
          simp only [Set.mem_preimage, Set.mem_setOf_eq, Pi.add_apply] at hy ⊢
          intro k
          have hk : Sigma k.1 j < 1 := hCorr k.1 j k.2
          simp only [hma, hmb] at hy ⊢
          nlinarith [hy k, hk, hab]
        rw [Measure.map_apply (measurable_const.add hmv) hsa,
            Measure.map_apply (measurable_const.add hmv) hsb]
        exact ENNReal.toReal_mono
          (ne_of_lt (lt_of_le_of_lt (measure_mono (Set.subset_univ _))
            (by rw [measure_univ]; exact ENNReal.one_lt_top)))
          (MeasureTheory.measure_mono hsub)
      · simp only [Statlib.Imported.gaussianVecMeasure, dif_neg hA]
        simp
    · exact ENNReal.toReal_nonneg
    · exact (Real.exp_pos _).le
  obtain ⟨hac, hmeas, hint⟩ :=
    statopia_math_node_2518884549_dcb952d7 μ q hq V hV Sigma nu hVar hMean hCov hGauss hCorr
      (fun j => (statopia_math_node_3326423151_cf0f28e2 μ q hq V hV Sigma nu hVar hMean hCov hGauss hL2 j).2.1)
  exact ⟨hac, hmeas, hint, hG_nonneg, hG_mono⟩
  /- @proof-region region.target-node.session.67d42183a87c0e0d end -/

end Statlib.Imported

