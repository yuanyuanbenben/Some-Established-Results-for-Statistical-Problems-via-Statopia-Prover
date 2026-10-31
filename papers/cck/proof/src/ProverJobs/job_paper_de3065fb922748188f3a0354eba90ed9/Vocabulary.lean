import Statlib.StatFoundation.Statistics.Asymptotic.ScoreCLT
import Statlib.StatFoundation.Convergence.Resampling.GaussianMaxComparison
import Statlib.StatFoundation.Convergence.AnalysisTools.GaussianMaxAnticoncentration
import Statlib.StatFoundation.Statistics.Asymptotic.LAN
import Statlib.StatFoundation.Convergence.AnalysisTools.SmoothMax
import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import Mathlib

namespace PaperProofTasks.job_paper_de3065fb922748188f3a0354eba90ed9

-- Shared append-only definitions for the root theorem and every Math node.
-- Node Formalize may add def/abbrev/structure/class/inductive declarations here.

/-- The standard Gaussian product measure on `ι → ℝ`, i.e. the law of `ι`-many independent
standard normal coordinates. -/
noncomputable def Statlib.Imported.stdGaussianPi (ι : Type*) [Fintype ι] :
    MeasureTheory.Measure (ι → ℝ) :=
  MeasureTheory.Measure.pi (fun _ : ι => ProbabilityTheory.gaussianReal 0 1)

/-- `N(m, S)`: the Gaussian measure on `ι → ℝ` with mean vector `m` and covariance matrix
`(1/2) • (S + Sᵀ)` (which is `S` itself whenever `S` is symmetric). It is the law of
`y ↦ m + √S y` under the standard Gaussian product measure `stdGaussianPi`, hence it is
defined also for singular (degenerate) covariance matrices. If `S` is not positive
semidefinite the definition takes the junk value `0`. -/
noncomputable def Statlib.Imported.gaussianVecMeasure {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℝ) (S : Matrix ι ι ℝ) : MeasureTheory.Measure (ι → ℝ) :=
  letI : Decidable ((((1 : ℝ) / 2) • (S + S.transpose))).PosSemidef := Classical.propDecidable _
  if h : ((((1 : ℝ) / 2) • (S + S.transpose))).PosSemidef then
    MeasureTheory.Measure.map
      (fun y : ι → ℝ => m + Matrix.mulVec (Matrix.PosSemidef.sqrt h) y)
      (Statlib.Imported.stdGaussianPi ι)
  else 0

