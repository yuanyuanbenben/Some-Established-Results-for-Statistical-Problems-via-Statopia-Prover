import Statlib
import ProverJobs.cqr_005_split_conformal_score_miscoverage_bound_of_exchangeable.Main

open MeasureTheory
open Statlib.StatFoundation.Vocabulary
open Statlib.Nonparametric.Vocabulary
open Statlib.Nonparametric.ConformalQuantileRegression

namespace Statlib.Workspace.Conformal

theorem cqr_006_romano_patterson_candes_cqr_finite_sample_miscoverage_bound {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n k : ℕ} (hn : 0 < n) (alpha : ℝ)
    (qlo qhi : X → ℝ)
    (Xcal : Fin n → Ω → X) (Ycal : Fin n → Ω → ℝ)
    (Xnew : Ω → X) (Ynew threshold : Ω → ℝ)
    (hqlo_meas : Measurable qlo)
    (hqhi_meas : Measurable qhi)
    (hXcal_meas : ∀ i : Fin n, Measurable (Xcal i))
    (hYcal_meas : ∀ i : Fin n, Measurable (Ycal i))
    (hXnew_meas : Measurable Xnew)
    (hYnew_meas : Measurable Ynew)
    (hthreshold_meas : Measurable threshold)
    (hmiscoverage_meas :
      MeasurableSet
        {ω | Ynew ω ∉ cqrInterval qlo qhi (threshold ω) (Xnew ω)})
    (hquantile :
      HasAtLeastKCalibrationScoresLE
        (cqrCalibrationScores qlo qhi Xcal Ycal)
        threshold k)
    (hscore_meas :
      ∀ i : Fin (n + 1),
        Measurable
          ((appendCalibrationTestScoreProcess
            (cqrCalibrationScores qlo qhi Xcal Ycal)
            (cqrTestScore qlo qhi Xnew Ynew)) i))
    (hscore_exch :
      IsExchangeable
        (appendCalibrationTestScoreProcess
          (cqrCalibrationScores qlo qhi Xcal Ycal)
          (cqrTestScore qlo qhi Xnew Ynew)) μ)
    (hk_alpha : (((n + 1 - k : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) ≤ alpha) :
    MarginalEventBound μ
      {ω | Ynew ω ∉ cqrInterval qlo qhi (threshold ω) (Xnew ω)}
      alpha := by
  have _hqlo_regular : Measurable qlo := hqlo_meas
  have _hqhi_regular : Measurable qhi := hqhi_meas
  have _hXcal_regular : ∀ i : Fin n, Measurable (Xcal i) := hXcal_meas
  have _hYcal_regular : ∀ i : Fin n, Measurable (Ycal i) := hYcal_meas
  have _hXnew_regular : Measurable Xnew := hXnew_meas
  have _hYnew_regular : Measurable Ynew := hYnew_meas
  have _hmiscoverage_regular :
      MeasurableSet {ω | Ynew ω ∉ cqrInterval qlo qhi (threshold ω) (Xnew ω)} :=
    hmiscoverage_meas
  have hscore_bound :
      HasScoreMiscoverageBound μ (cqrTestScore qlo qhi Xnew Ynew) threshold alpha := by
    exact cqr_005_split_conformal_score_miscoverage_bound_of_exchangeable μ hn alpha
      (cqrCalibrationScores qlo qhi Xcal Ycal)
      (cqrTestScore qlo qhi Xnew Ynew) threshold
      hthreshold_meas hquantile hscore_meas hscore_exch hk_alpha
  exact cqr_miscoverage_bound_of_score_miscoverage μ alpha qlo qhi Xnew Ynew threshold
    hscore_bound

end Statlib.Workspace.Conformal
