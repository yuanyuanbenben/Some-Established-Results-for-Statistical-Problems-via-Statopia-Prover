import Statlib

open MeasureTheory
open Statlib.StatFoundation.Vocabulary

namespace Statlib.Workspace.Conformal

theorem cqr_003_rank_event_measure_bound_of_equiprobable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m k : ℕ} (hm : 0 < m)
    (score : Fin m → Ω → ℝ)
    (hbad_meas : ∀ i : Fin m, MeasurableSet (StrictLowerRankEvent score i k))
    (hequip : RankEventsEquiprobable μ score k)
    (hcard :
      ∀ ω,
        (Finset.univ.filter
          (fun i : Fin m => k ≤ strictLowerScoreCount (fun j => score j ω) i)).card ≤
          m - k)
    (target : Fin m) :
    (μ (StrictLowerRankEvent score target k)).toReal ≤
      ((m - k : ℕ) : ℝ) / (m : ℝ) := by
  classical
  have hsum_indicator_le :
      (∫⁻ ω, ∑ i : Fin m,
        (StrictLowerRankEvent score i k).indicator (fun _ => (1 : ENNReal)) ω ∂μ) ≤
        (((m - k : ℕ) : ENNReal)) := by
    calc
      (∫⁻ ω, ∑ i : Fin m,
        (StrictLowerRankEvent score i k).indicator (fun _ => (1 : ENNReal)) ω ∂μ)
          ≤ ∫⁻ ω, (((m - k : ℕ) : ENNReal)) ∂μ := by
        apply lintegral_mono
        intro ω
        calc
          (∑ i : Fin m,
              (StrictLowerRankEvent score i k).indicator (fun _ => (1 : ENNReal)) ω)
              = (∑ i ∈ (Finset.univ : Finset (Fin m)),
                  if ω ∈ StrictLowerRankEvent score i k then (1 : ENNReal) else 0) := by
            simp [Set.indicator_apply]
          _ = (((Finset.univ : Finset (Fin m)).filter
                  (fun i => ω ∈ StrictLowerRankEvent score i k)).card : ENNReal) := by
            rw [Finset.sum_boole]
          _ ≤ (((m - k : ℕ) : ENNReal)) := by
            have hfilter_eq : ((Finset.univ : Finset (Fin m)).filter
                (fun i => ω ∈ StrictLowerRankEvent score i k)) =
                ((Finset.univ : Finset (Fin m)).filter
                  (fun i : Fin m => k ≤ strictLowerScoreCount (fun j => score j ω) i)) := by
              apply Finset.filter_congr
              intro i _
              simp [StrictLowerRankEvent]
            rw [hfilter_eq]
            exact_mod_cast hcard ω
      _ = (((m - k : ℕ) : ENNReal)) := by
        rw [lintegral_const, IsProbabilityMeasure.measure_univ, mul_one]
  have hsum_measure_le :
      (∑ i : Fin m, μ (StrictLowerRankEvent score i k)) ≤
        (((m - k : ℕ) : ENNReal)) := by
    calc
      (∑ i : Fin m, μ (StrictLowerRankEvent score i k)) =
          ∫⁻ ω, ∑ i : Fin m,
            (StrictLowerRankEvent score i k).indicator (fun _ => (1 : ENNReal)) ω ∂μ := by
        rw [MeasureTheory.lintegral_finset_sum]
        · simp [hbad_meas]
        · intro i _
          exact measurable_const.indicator (hbad_meas i)
      _ ≤ (((m - k : ℕ) : ENNReal)) := hsum_indicator_le
  have hsum_eq :
      (∑ i : Fin m, μ (StrictLowerRankEvent score i k)) =
        (m : ENNReal) * μ (StrictLowerRankEvent score target k) := by
    calc
      (∑ i : Fin m, μ (StrictLowerRankEvent score i k)) =
          ∑ i : Fin m, μ (StrictLowerRankEvent score target k) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        exact hequip i target
      _ = (m : ENNReal) * μ (StrictLowerRankEvent score target k) := by
        simp
  have hmul_le :
      (m : ENNReal) * μ (StrictLowerRankEvent score target k) ≤
        (((m - k : ℕ) : ENNReal)) := by
    simpa [hsum_eq] using hsum_measure_le
  have hm_ne_zero : (m : ENNReal) ≠ 0 := by
    exact_mod_cast (ne_of_gt hm)
  have hm_ne_top : (m : ENNReal) ≠ ⊤ := by simp
  have hdiv_enn :
      μ (StrictLowerRankEvent score target k) ≤
        (((m - k : ℕ) : ENNReal)) / (m : ENNReal) := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hm_ne_zero) (Or.inl hm_ne_top)]
    simpa [mul_comm] using hmul_le
  have hright_ne_top : (((m - k : ℕ) : ENNReal)) / (m : ENNReal) ≠ ⊤ := by
    exact ENNReal.div_ne_top (ENNReal.natCast_ne_top (m - k)) hm_ne_zero
  have hreal := ENNReal.toReal_mono hright_ne_top hdiv_enn
  rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast] at hreal
  exact hreal

end Statlib.Workspace.Conformal
