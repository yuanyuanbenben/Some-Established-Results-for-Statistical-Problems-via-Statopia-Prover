import Mathlib
import Statlib.StatFoundation.Vocabulary.Conformal

open MeasureTheory
open Statlib.StatFoundation.Vocabulary

namespace Statlib.Workspace.Conformal

theorem cqr_004_rank_events_equiprobable_of_score_exchangeable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {m k : ℕ} (hm : 0 < m)
    (score : Fin m → Ω → ℝ)
    (hscore_meas : ∀ i : Fin m, Measurable (score i))
    (hscore_exch : IsExchangeable score μ) :
    RankEventsEquiprobable μ score k := by
  classical
  have _hscore_meas : ∀ i : Fin m, Measurable (score i) := hscore_meas
  intro i j
  let S : Set (Fin m → ℝ) := {v | k ≤ strictLowerScoreCount v j}
  have hS_meas : MeasurableSet S := by
    let countFun : (Fin m → ℝ) → ℕ :=
      fun v => ∑ l : Fin m, if v l < v j then (1 : ℕ) else 0
    have hcount_meas : Measurable countFun := by
      dsimp [countFun]
      apply Finset.measurable_fun_sum
      intro l _
      exact Measurable.ite
        (measurableSet_lt (measurable_pi_apply l) (measurable_pi_apply j))
        measurable_const measurable_const
    have hset_eq : S = {v : Fin m → ℝ | k ≤ countFun v} := by
      ext v
      dsimp [S]
      unfold strictLowerScoreCount
      dsimp [countFun]
      rw [Finset.card_filter]
    rw [hset_eq]
    exact measurableSet_le measurable_const hcount_meas
  let σ : Equiv.Perm (Fin m) := Equiv.swap i j
  have hdist := hscore_exch σ
  have hmeasure := hdist.measure_mem_eq hS_meas
  have hleft :
      ((fun ω : Ω => fun l : Fin m => score l ω) ⁻¹' S) =
        StrictLowerRankEvent score j k := by
    ext ω
    simp [S, StrictLowerRankEvent]
  have hright :
      ((fun ω : Ω => fun l : Fin m => score (σ l) ω) ⁻¹' S) =
        StrictLowerRankEvent score i k := by
    ext ω
    dsimp [S, StrictLowerRankEvent]
    have hcount_perm :
        strictLowerScoreCount (fun l => score (σ l) ω) j =
          strictLowerScoreCount (fun l => score l ω) (σ j) := by
      unfold strictLowerScoreCount
      refine Finset.card_bij (fun l _ => σ l) ?hi ?hinj ?hsurj
      · intro l hl
        rw [Finset.mem_filter] at hl ⊢
        exact ⟨Finset.mem_univ _, hl.2⟩
      · intro a _ b _ hab
        exact σ.injective hab
      · intro b hb
        refine ⟨σ.symm b, ?_, ?_⟩
        · rw [Finset.mem_filter] at hb ⊢
          constructor
          · exact Finset.mem_univ _
          · simpa using hb.2
        · simp
    rw [hcount_perm]
    simp [σ]
  rw [hleft, hright] at hmeasure
  exact hmeasure.symm

end Statlib.Workspace.Conformal
