import Mathlib
import Statlib.StatFoundation.Statistics.Conformal
import ProverJobs.cqr_001_split_miscoverage_subset_strict_lower_rank_event.Main
import ProverJobs.cqr_002_strict_lower_rank_event_cardinality_bound.Main
import ProverJobs.cqr_003_rank_event_measure_bound_of_equiprobable.Main
import ProverJobs.cqr_004_rank_events_equiprobable_of_score_exchangeable.Main

open MeasureTheory
open Statlib.StatFoundation.Vocabulary
open Statlib.StatFoundation.Statistics.Conformal

namespace Statlib.Workspace.Conformal

theorem cqr_005_split_conformal_score_miscoverage_bound_of_exchangeable {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n k : ℕ} (hn : 0 < n) (alpha : ℝ)
    (calScore : Fin n → Ω → ℝ) (newScore threshold : Ω → ℝ)
    (hthreshold_meas : Measurable threshold)
    (hquantile : HasAtLeastKCalibrationScoresLE calScore threshold k)
    (hscore_meas :
      ∀ i : Fin (n + 1),
        Measurable ((appendCalibrationTestScoreProcess calScore newScore) i))
    (hscore_exch : IsExchangeable (appendCalibrationTestScoreProcess calScore newScore) μ)
    (hk_alpha : (((n + 1 - k : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) ≤ alpha) :
    HasScoreMiscoverageBound μ newScore threshold alpha := by
  classical
  let scoreApp : Fin (n + 1) → Ω → ℝ := appendCalibrationTestScoreProcess calScore newScore
  have hsubset :
      ScoreMiscoveredBy newScore threshold ⊆
        StrictLowerRankEvent scoreApp (calibrationTestLastIndex n) k := by
    dsimp [scoreApp]
    exact cqr_001_split_miscoverage_subset_strict_lower_rank_event
      hn calScore newScore threshold hquantile
  have hequip : RankEventsEquiprobable μ scoreApp k := by
    dsimp [scoreApp]
    exact cqr_004_rank_events_equiprobable_of_score_exchangeable μ
      (Nat.succ_pos n)
      (appendCalibrationTestScoreProcess calScore newScore) hscore_meas hscore_exch
  have hscore_meas_app : ∀ i : Fin (n + 1), Measurable (scoreApp i) := by
    intro i
    dsimp [scoreApp]
    exact hscore_meas i
  have hbad_meas :
      ∀ i : Fin (n + 1), MeasurableSet (StrictLowerRankEvent scoreApp i k) := by
    intro i
    exact strictLowerRankEvent_measurableSet scoreApp hscore_meas_app i
  have hcard :
      ∀ ω,
        (Finset.univ.filter
          (fun i : Fin (n + 1) =>
            k ≤ strictLowerScoreCount (fun j => scoreApp j ω) i)).card ≤
          n + 1 - k := by
    intro ω
    exact cqr_002_strict_lower_rank_event_cardinality_bound
      (Nat.succ_pos n)
      (fun j : Fin (n + 1) => scoreApp j ω)
  have hrank_bound :
      (μ (StrictLowerRankEvent scoreApp (calibrationTestLastIndex n) k)).toReal ≤
        (((n + 1 - k : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) := by
    exact cqr_003_rank_event_measure_bound_of_equiprobable μ (Nat.succ_pos n)
      scoreApp hbad_meas hequip hcard (calibrationTestLastIndex n)
  have hmis_le_rank :
      (μ (ScoreMiscoveredBy newScore threshold)).toReal ≤
        (μ (StrictLowerRankEvent scoreApp (calibrationTestLastIndex n) k)).toReal := by
    exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hsubset)
  exact hmis_le_rank.trans (hrank_bound.trans hk_alpha)

end Statlib.Workspace.Conformal
