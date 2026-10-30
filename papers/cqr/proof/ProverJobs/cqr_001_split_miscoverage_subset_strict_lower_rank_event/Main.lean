import Statlib

open Statlib.StatFoundation.Vocabulary

namespace Statlib.Workspace.Conformal

theorem cqr_001_split_miscoverage_subset_strict_lower_rank_event {Ω : Type*} {n k : ℕ}
    (hn : 0 < n) (calScore : Fin n → Ω → ℝ) (newScore threshold : Ω → ℝ)
    (hquantile : HasAtLeastKCalibrationScoresLE calScore threshold k) :
    ScoreMiscoveredBy newScore threshold ⊆
      StrictLowerRankEvent
        (appendCalibrationTestScoreProcess calScore newScore)
        (calibrationTestLastIndex n) k := by
  intro ω hmis
  dsimp [ScoreMiscoveredBy] at hmis
  dsimp [StrictLowerRankEvent]
  unfold strictLowerScoreCount
  have hle : k ≤ calibrationLECount (fun i => calScore i ω) (threshold ω) := hquantile ω
  refine le_trans hle ?_
  unfold calibrationLECount
  refine Finset.card_le_card_of_injOn (fun i : Fin n => Fin.castSucc i) ?maps ?inj
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    dsimp [appendCalibrationTestScoreProcess]
    have hleft :
        appendCalibrationTestScore (fun j => calScore j ω) (newScore ω) (Fin.castSucc i) =
          calScore i ω := by
      unfold appendCalibrationTestScore
      simp
    have hright :
        appendCalibrationTestScore (fun j => calScore j ω) (newScore ω)
            (calibrationTestLastIndex n) =
          newScore ω := by
      unfold appendCalibrationTestScore calibrationTestLastIndex
      simp
    rw [hleft, hright]
    exact lt_of_le_of_lt hi hmis
  · intro i _ j _ hij
    exact Fin.castSucc_injective n hij

end Statlib.Workspace.Conformal
