import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.Vocabulary
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.Base

open MeasureTheory
open Statlib.Imported

noncomputable section
open MeasureTheory
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_2121685325_82fde9c2 : ∀ (t β ε : ℝ) (n : ℕ)
    (hε : 0 < ε) (hn : 2 ≤ n) (htau : 0 < t + β),
    MeasureTheory.IntegrableOn
        (fun α : ℝ => α ^ (t + β - 1) * Real.exp (-(1 + Real.log (n : ℝ)) * α))
        (Set.Ioo (0 : ℝ) ε)
      ∧ Real.exp (-1) * (min ε (1 / (1 + Real.log (n : ℝ)))) ^ (t + β) / (t + β)
          ≤ ∫ α in Set.Ioo (0 : ℝ) ε,
              α ^ (t + β - 1) * Real.exp (-(1 + Real.log (n : ℝ)) * α) := by
  /- @proof-region region.target-node.session.2efd3c1b8a185452 begin -/
  intro t β ε n hε hn htau
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hlog_nn : 0 ≤ Real.log (n : ℝ) := by
    have h := Real.log_le_log (show (0 : ℝ) < 1 by norm_num) hn1
    rwa [Real.log_one] at h
  have hc_pos : 0 < 1 + Real.log (n : ℝ) := by linarith
  have hc_ne : (1 + Real.log (n : ℝ)) ≠ 0 := ne_of_gt hc_pos
  have hp_gt : -1 < t + β - 1 := by linarith
  have hτ_pos : 0 < t + β := htau
  have hInt_pow : MeasureTheory.IntegrableOn (fun α : ℝ => α ^ (t + β - 1)) (Set.Ioo (0:ℝ) ε) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff (s := t + β - 1) hε).mpr hp_gt
  have hpow_asm : AEStronglyMeasurable (fun α : ℝ => α ^ (t + β - 1)) (volume.restrict (Set.Ioo (0:ℝ) ε)) :=
    hInt_pow.aestronglyMeasurable
  have hexp_cont : Continuous (fun α : ℝ => Real.exp (-(1 + Real.log (n : ℝ)) * α)) := by fun_prop
  have hexp_asm : AEStronglyMeasurable (fun α : ℝ => Real.exp (-(1 + Real.log (n : ℝ)) * α)) (volume.restrict (Set.Ioo (0:ℝ) ε)) :=
    hexp_cont.measurable.aestronglyMeasurable
  have hprod_asm : AEStronglyMeasurable (fun α : ℝ => α ^ (t + β - 1) * Real.exp (-(1 + Real.log (n : ℝ)) * α)) (volume.restrict (Set.Ioo (0:ℝ) ε)) :=
    hpow_asm.mul hexp_asm
  have hb_nn : 0 ≤ᶠ[ae (volume.restrict (Set.Ioo (0:ℝ) ε))] (fun α : ℝ => α ^ (t + β - 1) * Real.exp (-(1 + Real.log (n : ℝ)) * α)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with α hα
    exact le_of_lt (mul_pos (Real.rpow_pos_of_pos hα.1 (t + β - 1)) (Real.exp_pos _))
  have hb_int : MeasureTheory.IntegrableOn (fun α : ℝ => α ^ (t + β - 1) * Real.exp (-(1 + Real.log (n : ℝ)) * α)) (Set.Ioo (0:ℝ) ε) := by
    change MeasureTheory.Integrable (fun α : ℝ => α ^ (t + β - 1) * Real.exp (-(1 + Real.log (n : ℝ)) * α)) (volume.restrict (Set.Ioo (0:ℝ) ε))
    refine MeasureTheory.Integrable.mono (g := fun α : ℝ => α ^ (t + β - 1)) hInt_pow hprod_asm ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with α hα
    have hα0 : 0 < α := hα.1
    have hpow_pos : 0 < α ^ (t + β - 1) := Real.rpow_pos_of_pos hα0 (t + β - 1)
    have hexp_le : Real.exp (-(1 + Real.log (n : ℝ)) * α) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have hmul : 0 ≤ (1 + Real.log (n : ℝ)) * α := mul_nonneg (le_of_lt hc_pos) (le_of_lt hα0)
      nlinarith
    have hb_pos : 0 < α ^ (t + β - 1) * Real.exp (-(1 + Real.log (n : ℝ)) * α) :=
      mul_pos hpow_pos (Real.exp_pos _)
    rw [Real.norm_of_nonneg (le_of_lt hb_pos), Real.norm_of_nonneg (le_of_lt hpow_pos)]
    calc α ^ (t + β - 1) * Real.exp (-(1 + Real.log (n : ℝ)) * α)
        ≤ α ^ (t + β - 1) * 1 := mul_le_mul_of_nonneg_left hexp_le (le_of_lt hpow_pos)
      _ = α ^ (t + β - 1) := mul_one _
  constructor
  · exact hb_int
  · set u : ℝ := min ε (1 / (1 + Real.log (n : ℝ))) with hu
    have hu_pos : 0 < u := by rw [hu]; exact lt_min hε (div_pos one_pos hc_pos)
    have hu_le_eps : u ≤ ε := by rw [hu]; exact min_le_left _ _
    have hu_le_invc : u ≤ 1 / (1 + Real.log (n : ℝ)) := by rw [hu]; exact min_le_right _ _
    have hu_sub : Set.Ioo (0:ℝ) u ⊆ Set.Ioo (0:ℝ) ε := Set.Ioo_subset_Ioo_right hu_le_eps
    have hInt_pow_u : MeasureTheory.IntegrableOn (fun α : ℝ => α ^ (t + β - 1)) (Set.Ioo (0:ℝ) u) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff (s := t + β - 1) hu_pos).mpr hp_gt
    have hInt_b_u : MeasureTheory.IntegrableOn (fun α : ℝ => α ^ (t + β - 1) * Real.exp (-(1 + Real.log (n : ℝ)) * α)) (Set.Ioo (0:ℝ) u) :=
      hb_int.mono_set hu_sub
    have hInt_const_pow_u : MeasureTheory.IntegrableOn (fun α : ℝ => Real.exp (-1) * (α ^ (t + β - 1))) (Set.Ioo (0:ℝ) u) :=
      hInt_pow_u.const_mul (Real.exp (-1))
    have hInt_rpow : ∫ α in Set.Ioo (0:ℝ) u, α ^ (t + β - 1) = u ^ (t + β) / (t + β) := by
      have h1 : ∫ α in Set.Ioo (0:ℝ) u, α ^ (t + β - 1) = ∫ α in Set.Ioc (0:ℝ) u, α ^ (t + β - 1) := by
        rw [MeasureTheory.Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Ioc (μ := volume))]
      have h2 : ∫ α in Set.Ioc (0:ℝ) u, α ^ (t + β - 1) = ∫ α in (0:ℝ)..u, α ^ (t + β - 1) :=
        (intervalIntegral.integral_of_le (le_of_lt hu_pos)).symm
      have h3 : ∫ α in (0:ℝ)..u, α ^ (t + β - 1) = (u ^ ((t + β - 1) + 1) - (0:ℝ) ^ ((t + β - 1) + 1)) / ((t + β - 1) + 1) :=
        integral_rpow (Or.inl hp_gt)
      rw [h1, h2, h3]
      rw [show (t + β - 1) + 1 = t + β by ring]
      rw [Real.zero_rpow (ne_of_gt hτ_pos), sub_zero]
    have hstep2 : ∫ α in Set.Ioo (0:ℝ) u, Real.exp (-1) * α ^ (t + β - 1) ≤ ∫ α in Set.Ioo (0:ℝ) u, α ^ (t + β - 1) * Real.exp (-(1 + Real.log (n : ℝ)) * α) := by
      apply MeasureTheory.setIntegral_mono_on hInt_const_pow_u hInt_b_u measurableSet_Ioo
      intro α hα
      have hα0 : 0 < α := hα.1
      have hαu : α < u := hα.2
      have hpow_pos : 0 < α ^ (t + β - 1) := Real.rpow_pos_of_pos hα0 (t + β - 1)
      have hcα_le : (1 + Real.log (n : ℝ)) * α ≤ 1 := by
        have h1 : α < 1 / (1 + Real.log (n : ℝ)) := lt_of_lt_of_le hαu hu_le_invc
        have h2 : (1 + Real.log (n : ℝ)) * α < (1 + Real.log (n : ℝ)) * (1 / (1 + Real.log (n : ℝ))) :=
          mul_lt_mul_of_pos_left h1 hc_pos
        have h3 : (1 + Real.log (n : ℝ)) * (1 / (1 + Real.log (n : ℝ))) = 1 := by
          rw [one_div, mul_inv_cancel₀ hc_ne]
        linarith
      have hexp_ge : Real.exp (-1) ≤ Real.exp (-(1 + Real.log (n : ℝ)) * α) := by
        apply Real.exp_le_exp_of_le
        linarith
      calc Real.exp (-1) * α ^ (t + β - 1)
          = α ^ (t + β - 1) * Real.exp (-1) := by ring
        _ ≤ α ^ (t + β - 1) * Real.exp (-(1 + Real.log (n : ℝ)) * α) :=
            mul_le_mul_of_nonneg_left hexp_ge (le_of_lt hpow_pos)
    have hstep1 : ∫ α in Set.Ioo (0:ℝ) u, α ^ (t + β - 1) * Real.exp (-(1 + Real.log (n : ℝ)) * α) ≤ ∫ α in Set.Ioo (0:ℝ) ε, α ^ (t + β - 1) * Real.exp (-(1 + Real.log (n : ℝ)) * α) := by
      exact MeasureTheory.setIntegral_mono_set hb_int hb_nn (Filter.Eventually.of_forall hu_sub)
    calc Real.exp (-1) * u ^ (t + β) / (t + β)
        = Real.exp (-1) * (u ^ (t + β) / (t + β)) := by ring
      _ = Real.exp (-1) * ∫ α in Set.Ioo (0:ℝ) u, α ^ (t + β - 1) := by rw [hInt_rpow]
      _ = ∫ α in Set.Ioo (0:ℝ) u, Real.exp (-1) * α ^ (t + β - 1) := by rw [MeasureTheory.integral_const_mul]
      _ ≤ ∫ α in Set.Ioo (0:ℝ) u, α ^ (t + β - 1) * Real.exp (-(1 + Real.log (n : ℝ)) * α) := hstep2
      _ ≤ ∫ α in Set.Ioo (0:ℝ) ε, α ^ (t + β - 1) * Real.exp (-(1 + Real.log (n : ℝ)) * α) := hstep1
  /- @proof-region region.target-node.session.2efd3c1b8a185452 end -/

end Statlib.Imported
end
