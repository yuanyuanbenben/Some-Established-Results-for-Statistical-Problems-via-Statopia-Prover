import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q05.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q05.Base

open MeasureTheory ProbabilityTheory Filter
open Msc62GroundTruth

open MeasureTheory ProbabilityTheory Filter
namespace Msc62GroundTruth

set_option autoImplicit false in
theorem statopia_math_node_932896096_2342c8d2 : ∀ (Ω : Type*) [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → ℕ)
    (hY_meas : ∀ n, 1 ≤ n → AEMeasurable (Y n) μ)
    (hY_dist : ∀ (n : ℕ) (hn : 1 ≤ n),
      Measure.map (Y n) μ =
        binomialMeasure n
          (Real.toNNReal (1 / Real.sqrt (n : ℝ)))
          (toNNReal_one_div_sqrt_n_le_one n hn)),
    ∀ (n : ℕ) (hn : 1 ≤ n),
      Measure.map
        (fun ω =>
          if 1 ≤ n then
            (n : ℝ) ^ (3 / 4 : ℝ) *
              (((Y n ω : ℝ) / (n : ℝ)) - 1 / Real.sqrt (n : ℝ))
          else
            0)
        μ =
        Measure.map
          (fun y : ℝ => (n : ℝ) ^ (-(1 / 4) : ℝ) * y - (n : ℝ) ^ (1 / 4 : ℝ))
          (Measure.map (fun k : ℕ => (k : ℝ))
            (binomialMeasure n
              (Real.toNNReal (1 / Real.sqrt (n : ℝ)))
              (toNNReal_one_div_sqrt_n_le_one n hn))) := by
  /- @proof-region region.target-node.session.058708e94842bd7d begin -/
  intro Ω _ μ _ Y hY_meas hY_dist n hn
  have hpos : (0 : ℝ) < (n : ℝ) := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have key : ∀ y : ℝ, (n : ℝ) ^ (3 / 4 : ℝ) * (y / (n : ℝ) - 1 / Real.sqrt (n : ℝ))
      = (n : ℝ) ^ (-(1 / 4) : ℝ) * y - (n : ℝ) ^ (1 / 4 : ℝ) := by
    intro y
    have hsq : Real.sqrt (n : ℝ) = (n : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow (n : ℝ)
    have hB : (n : ℝ) ^ (3 / 4 : ℝ) * (n : ℝ) ^ (-(1 / 2) : ℝ) = (n : ℝ) ^ (1 / 4 : ℝ) := by
      have h := Real.rpow_add hpos (3 / 4 : ℝ) (-(1 / 2) : ℝ)
      rw [show (3 / 4 : ℝ) + (-(1 / 2)) = 1 / 4 by norm_num] at h
      exact h.symm
    have hmul : (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (-(1 / 2) : ℝ) = 1 := by
      rw [← Real.rpow_add hpos, show (1 / 2 : ℝ) + (-(1 / 2)) = 0 by norm_num, Real.rpow_zero]
    have hD : (n : ℝ) ^ (-(1 / 2) : ℝ) = 1 / (n : ℝ) ^ (1 / 2 : ℝ) := by
      rw [eq_div_iff (ne_of_gt (Real.rpow_pos_of_pos hpos (1 / 2 : ℝ))), mul_comm]
      exact hmul
    have hC : (n : ℝ) ^ (3 / 4 : ℝ) / (n : ℝ) = (n : ℝ) ^ (-(1 / 4) : ℝ) := by
      have h := Real.rpow_sub hpos (3 / 4 : ℝ) 1
      rw [show (3 / 4 : ℝ) - 1 = -(1 / 4) by norm_num, Real.rpow_one] at h
      exact h.symm
    have step2 : (n : ℝ) ^ (3 / 4 : ℝ) * (y / (n : ℝ)) =
        ((n : ℝ) ^ (3 / 4 : ℝ) / (n : ℝ)) * y := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring
    have step3 : (n : ℝ) ^ (3 / 4 : ℝ) * (1 / Real.sqrt (n : ℝ)) = (n : ℝ) ^ (1 / 4 : ℝ) := by
      rw [hsq, ← hD, hB]
    calc (n : ℝ) ^ (3 / 4 : ℝ) * (y / (n : ℝ) - 1 / Real.sqrt (n : ℝ))
        = (n : ℝ) ^ (3 / 4 : ℝ) * (y / (n : ℝ)) -
            (n : ℝ) ^ (3 / 4 : ℝ) * (1 / Real.sqrt (n : ℝ)) := by
          rw [mul_sub]
      _ = ((n : ℝ) ^ (3 / 4 : ℝ) / (n : ℝ)) * y - (n : ℝ) ^ (1 / 4 : ℝ) := by
          rw [step2, step3]
      _ = (n : ℝ) ^ (-(1 / 4) : ℝ) * y - (n : ℝ) ^ (1 / 4 : ℝ) := by rw [hC]
  have hfun : (fun ω => if 1 ≤ n then
      (n : ℝ) ^ (3 / 4 : ℝ) * ((Y n ω : ℝ) / (n : ℝ) - 1 / Real.sqrt (n : ℝ)) else 0)
      = fun ω => (n : ℝ) ^ (-(1 / 4) : ℝ) * (Y n ω : ℝ) - (n : ℝ) ^ (1 / 4 : ℝ) := by
    funext ω
    rw [if_pos hn]
    exact key (Y n ω : ℝ)
  rw [hfun]
  have hT : Measurable (fun y : ℝ => (n : ℝ) ^ (-(1 / 4) : ℝ) * y - (n : ℝ) ^ (1 / 4 : ℝ)) :=
    (measurable_const.mul measurable_id).sub measurable_const
  have hg : Measurable (fun k : ℕ => (k : ℝ)) := measurable_of_countable _
  have hfae : AEMeasurable (fun ω => (Y n ω : ℝ)) μ := hg.comp_aemeasurable (hY_meas n hn)
  have hcomp1 :
      Measure.map (fun ω => (n : ℝ) ^ (-(1 / 4) : ℝ) * (Y n ω : ℝ) - (n : ℝ) ^ (1 / 4 : ℝ)) μ
        = Measure.map (fun y : ℝ => (n : ℝ) ^ (-(1 / 4) : ℝ) * y - (n : ℝ) ^ (1 / 4 : ℝ))
            (Measure.map (fun ω => (Y n ω : ℝ)) μ) := by
    have h := AEMeasurable.map_map_of_aemeasurable (μ := μ)
      (g := fun y : ℝ => (n : ℝ) ^ (-(1 / 4) : ℝ) * y - (n : ℝ) ^ (1 / 4 : ℝ))
      (f := fun ω => (Y n ω : ℝ)) hT.aemeasurable hfae
    exact h.symm
  rw [hcomp1]
  have hfm : Measure.map (fun ω => (Y n ω : ℝ)) μ
      = Measure.map (fun k : ℕ => (k : ℝ))
          (binomialMeasure n (Real.toNNReal (1 / Real.sqrt (n : ℝ)))
            (toNNReal_one_div_sqrt_n_le_one n hn)) := by
    have h := AEMeasurable.map_map_of_aemeasurable (μ := μ)
      (g := fun k : ℕ => (k : ℝ)) (f := Y n) hg.aemeasurable (hY_meas n hn)
    have h2 : Measure.map (fun k : ℕ => (k : ℝ)) (Measure.map (Y n) μ)
        = Measure.map (fun k : ℕ => (k : ℝ))
            (binomialMeasure n (Real.toNNReal (1 / Real.sqrt (n : ℝ)))
              (toNNReal_one_div_sqrt_n_le_one n hn)) := by
      rw [hY_dist n hn]
    exact h.symm.trans h2
  rw [hfm]
  /- @proof-region region.target-node.session.058708e94842bd7d end -/

end Msc62GroundTruth
