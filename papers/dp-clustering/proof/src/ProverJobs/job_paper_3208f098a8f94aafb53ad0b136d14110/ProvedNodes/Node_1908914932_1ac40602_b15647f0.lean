import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.Vocabulary
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.Base
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.ProvedNodes.Node_1445702134_3c8d3810_8f7a15fe
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.ProvedNodes.Node_2202358284_edd9d5c8_284d2a8b
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.ProvedNodes.Node_3224678180_5a630a9f_7124eef7



open MeasureTheory
open Statlib.Imported

noncomputable section
open MeasureTheory
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_1908914932_1ac40602 : ∀ (t eps beta : ℝ) (n s : ℕ)
    (ht : 1 ≤ t) (heps_pos : 0 < eps) (heps_lt_one : eps < 1) (hbeta : 0 < beta)
    (hs : 1 ≤ s) (hns : t + (s : ℝ) ≤ (n : ℝ)),
    (MeasureTheory.IntegrableOn (fun alpha : ℝ => alpha ^ (t + beta) / risingFac alpha n)
        (Set.Ioo (0 : ℝ) eps)) ∧
      (MeasureTheory.IntegrableOn
          (fun alpha : ℝ => alpha ^ (t + (s : ℝ) + beta) / risingFac alpha n)
          (Set.Ioo (0 : ℝ) eps)) ∧
        (0 < ∫ alpha in Set.Ioo (0 : ℝ) eps, alpha ^ (t + beta) / risingFac alpha n) ∧
          (∫ alpha in Set.Ioo (0 : ℝ) eps, alpha ^ (t + (s : ℝ) + beta) / risingFac alpha n) /
              (∫ alpha in Set.Ioo (0 : ℝ) eps, alpha ^ (t + beta) / risingFac alpha n) ≤
            (Real.log ((n : ℝ) / (1 + eps))) ^ (-(s : ℝ)) *
              (lowerGamma (t + (s : ℝ) + beta) (eps * Real.log ((n : ℝ) / (1 + eps))) /
                lowerGamma (t + beta) (eps * Real.log ((n : ℝ) / (1 + eps)))) := by
  /- @proof-region region.target-node.session.2440f2cfda476fee begin -/
  intro t ε β n s ht heps_pos heps_lt_one hbeta hs hns
  have hε0 : (0 : ℝ) < ε := heps_pos
  have hε1 : ε ≤ 1 := le_of_lt heps_lt_one
  have hs1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have htb : (0 : ℝ) < t + β := by linarith
  have hn1 : 1 ≤ n := by
    have h2 : (1 : ℝ) ≤ (n : ℝ) := by linarith
    exact_mod_cast h2
  obtain ⟨hRpos, _, hRbound, _, _⟩ := statopia_math_node_1445702134_3c8d3810
  have hDpos : (0 : ℝ) < ((n - 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (n - 1)
  have key : ∀ N : ℝ, 0 < N →
      IntegrableOn (fun α : ℝ => α ^ N / risingFac α n) (Set.Ioo (0 : ℝ) ε) := by
    intro N hN
    have hcont_num : Continuous (fun α : ℝ => α ^ N) :=
      Continuous.rpow_const continuous_id (fun _ => Or.inr (le_of_lt hN))
    have hcont_R : Continuous (fun α : ℝ => risingFac α n) := by
      unfold risingFac
      exact continuous_finset_prod _ (fun k _ => continuous_id.add continuous_const)
    have hmeas : Measurable (fun α : ℝ => α ^ N / risingFac α n) :=
      hcont_num.measurable.div hcont_R.measurable
    have hrpow_int : IntegrableOn (fun α : ℝ => α ^ (N - 1)) (Set.Ioo (0 : ℝ) ε) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff hε0).mpr (by linarith)
    have hbound_int :
        IntegrableOn (fun α : ℝ => (1 / ((n - 1).factorial : ℝ)) * α ^ (N - 1))
          (Set.Ioo (0 : ℝ) ε) := hrpow_int.const_mul _
    refine hbound_int.mono' hmeas.aestronglyMeasurable ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with α hα
    have hα0 : 0 < α := hα.1
    have hα1 : α ≤ 1 := le_of_lt (lt_of_lt_of_le hα.2 hε1)
    have hRp : 0 < risingFac α n := hRpos α n hα0
    have hbnd : α * ((n - 1).factorial : ℝ) ≤ risingFac α n := hRbound α n hα0 hα1 hn1
    have hAle : α ≤ (1 / ((n - 1).factorial : ℝ)) * risingFac α n := by
      have heq : (1 / ((n - 1).factorial : ℝ)) * risingFac α n
          = risingFac α n / ((n - 1).factorial : ℝ) := by
        rw [div_mul_eq_mul_div, one_mul]
      rw [heq, le_div_iff₀ hDpos]
      exact hbnd
    have hratio : α / risingFac α n ≤ 1 / ((n - 1).factorial : ℝ) :=
      (div_le_iff₀ hRp).mpr hAle
    have hpow : α ^ N = α ^ (N - 1) * α := by
      have h := Real.rpow_add hα0 (N - 1) 1
      rw [Real.rpow_one] at h
      rw [show (N - 1) + 1 = N by ring] at h
      exact h
    have hsplit : α ^ N / risingFac α n = α ^ (N - 1) * (α / risingFac α n) := by
      rw [hpow, mul_div_assoc]
    have hnorm : ‖α ^ N / risingFac α n‖ = α ^ N / risingFac α n :=
      Real.norm_of_nonneg (le_of_lt (div_pos (Real.rpow_pos_of_pos hα0 N) hRp))
    rw [hnorm, hsplit]
    calc α ^ (N - 1) * (α / risingFac α n)
        ≤ α ^ (N - 1) * (1 / ((n - 1).factorial : ℝ)) := by
          apply mul_le_mul_of_nonneg_left hratio
          exact le_of_lt (Real.rpow_pos_of_pos hα0 (N - 1))
      _ = (1 / ((n - 1).factorial : ℝ)) * α ^ (N - 1) := by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact key (t + β) htb
  · exact key (t + (s : ℝ) + β) (by linarith)
  · have hInt := key (t + β) htb
    refine (MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae ?_ hInt).mpr ?_
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with α hα
      have hα0 : 0 < α := hα.1
      have hRp : 0 < risingFac α n := hRpos α n hα0
      exact le_of_lt (div_pos (Real.rpow_pos_of_pos hα0 (t + β)) hRp)
    · have hsub : Set.Ioo (0 : ℝ) ε ⊆ Function.support (fun α : ℝ => α ^ (t + β) / risingFac α n) := by
        intro α hα
        simp only [Function.mem_support]
        have hα0 : 0 < α := hα.1
        have hRp : 0 < risingFac α n := hRpos α n hα0
        exact ne_of_gt (div_pos (Real.rpow_pos_of_pos hα0 (t + β)) hRp)
      have hset : Function.support (fun α : ℝ => α ^ (t + β) / risingFac α n) ∩ Set.Ioo (0 : ℝ) ε
          = Set.Ioo (0 : ℝ) ε := by
        apply Set.Subset.antisymm
        · intro x hx
          exact hx.2
        · intro x hx
          exact ⟨hsub hx, hx⟩
      rw [hset, Real.volume_Ioo]
      simp only [sub_zero]
      exact ENNReal.ofReal_pos.mpr hε0
  · exact statopia_math_node_2202358284_edd9d5c8 t ε β n s ht heps_pos heps_lt_one hbeta hs hns
  /- @proof-region region.target-node.session.2440f2cfda476fee end -/

end Statlib.Imported
end
