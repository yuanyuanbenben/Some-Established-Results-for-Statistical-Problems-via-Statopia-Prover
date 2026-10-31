import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.Vocabulary
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.Base
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.ProvedNodes.Node_1113054774_24697df7_0035d7e4
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.ProvedNodes.Node_1445702134_3c8d3810_8f7a15fe
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.ProvedNodes.Node_3224678180_5a630a9f_7124eef7



open MeasureTheory
open Statlib.Imported

noncomputable section
open MeasureTheory
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_1136441573_47d2c9c7 : ∀ (t eps beta : ℝ) (n s : ℕ)
    (ht : 1 ≤ t) (heps : 0 < eps) (heps1 : eps < 1) (hbeta : 0 < beta)
    (hs : 1 ≤ s) (hts : t + (s : ℝ) ≤ (n : ℝ)),
    (0 < ∫ a in Set.Ioo (0 : ℝ) eps, a ^ (t + beta) / risingFac a n) ∧
      ((Real.log (n : ℝ) + 1) ^ (-(s : ℝ)) *
          (lowerGamma (t + (s : ℝ) + beta) (eps * (Real.log (n : ℝ) + 1)) /
            lowerGamma (t + beta) (eps * (Real.log (n : ℝ) + 1))) ≤
        (∫ a in Set.Ioo (0 : ℝ) eps, a ^ (t + (s : ℝ) + beta) / risingFac a n) /
          (∫ a in Set.Ioo (0 : ℝ) eps, a ^ (t + beta) / risingFac a n)) := by
  /- @proof-region region.target-node.session.d071cd196b4bbe28 begin -/
  intro t ε β n s ht hε hε1 hβ hs hts
  have hG := statopia_math_node_1445702134_3c8d3810
  have hL := statopia_math_node_3224678180_5a630a9f
  have hts' : (1 : ℝ) ≤ (n : ℝ) := by linarith
  have hn1 : 1 ≤ n := by exact_mod_cast hts'
  have htβ : 0 < t + β := by linarith
  have hfacpos : ∀ α : ℝ, 0 < α → 0 < risingFac α n := fun α hα => hG.1 α n hα
  constructor
  · have hdpos : (0 : ℝ) < ((n - 1).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_pos (n - 1)
    have hrpowmeas : Measurable fun α : ℝ => α ^ (t + β) :=
      (Real.continuous_rpow_const (le_of_lt htβ)).measurable
    have hfacmeas : Measurable fun α : ℝ => risingFac α n := by
      simpa [risingFac] using
        (Finset.measurable_prod (Finset.range n)
          (fun k _ => (measurable_id : Measurable fun α : ℝ => α).add measurable_const))
    have hmeas : AEStronglyMeasurable (fun α : ℝ => α ^ (t + β) / risingFac α n)
        (volume.restrict (Set.Ioo (0 : ℝ) ε)) :=
      (hrpowmeas.div hfacmeas).aestronglyMeasurable
    have hle : ∀ α ∈ Set.Ioo (0 : ℝ) ε,
        ‖α ^ (t + β) / risingFac α n‖ ≤ α ^ (t + β - 2) := by
      intro α hα
      obtain ⟨hα0, hαε⟩ := hα
      have hα1 : α ≤ 1 := le_of_lt (lt_trans hαε hε1)
      have hfacp : 0 < risingFac α n := hfacpos α hα0
      have hC := hG.2.2.1 α n hα0 hα1 hn1
      have hαdpos : 0 < α * ((n - 1).factorial : ℝ) := mul_pos hα0 hdpos
      have hdfact : (1 : ℝ) ≤ ((n - 1).factorial : ℝ) := by
        have h1 : (1 : ℕ) ≤ (n - 1).factorial := Nat.factorial_pos (n - 1)
        exact_mod_cast h1
      have hαle : α ≤ ((n - 1).factorial : ℝ) := le_trans hα1 hdfact
      have hinv1 : (risingFac α n)⁻¹ ≤ (α * ((n - 1).factorial : ℝ))⁻¹ :=
        (inv_le_inv₀ hfacp hαdpos).2 hC
      have hA : α ^ (t + β) / risingFac α n
          ≤ α ^ (t + β) / (α * ((n - 1).factorial : ℝ)) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left hinv1 (le_of_lt (Real.rpow_pos_of_pos hα0 (t + β)))
      have hB : α ^ (t + β) / (α * ((n - 1).factorial : ℝ))
          = α ^ (t + β - 1) / ((n - 1).factorial : ℝ) := by
        rw [← div_div, Real.rpow_sub_one (ne_of_gt hα0)]
      have hD : (((n - 1).factorial : ℝ))⁻¹ ≤ α⁻¹ := (inv_le_inv₀ hdpos hα0).2 hαle
      have hfpos : 0 < α ^ (t + β) / risingFac α n :=
        div_pos (Real.rpow_pos_of_pos hα0 (t + β)) hfacp
      rw [Real.norm_eq_abs, abs_of_pos hfpos]
      calc α ^ (t + β) / risingFac α n
          ≤ α ^ (t + β) / (α * ((n - 1).factorial : ℝ)) := hA
        _ = α ^ (t + β - 1) / ((n - 1).factorial : ℝ) := hB
        _ = α ^ (t + β - 1) * (((n - 1).factorial : ℝ))⁻¹ := by rw [div_eq_mul_inv]
        _ ≤ α ^ (t + β - 1) * α⁻¹ :=
            mul_le_mul_of_nonneg_left hD (le_of_lt (Real.rpow_pos_of_pos hα0 (t + β - 1)))
        _ = α ^ ((t + β - 1) - 1) := by
            rw [← div_eq_mul_inv, ← Real.rpow_sub_one (ne_of_gt hα0)]
        _ = α ^ (t + β - 2) := by rw [show (t + β - 1) - 1 = t + β - 2 by ring]
    have hIbound : IntegrableOn (fun α : ℝ => α ^ (t + β - 2)) (Set.Ioo (0 : ℝ) ε) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff (s := t + β - 2) (t := ε) hε).2 (by linarith)
    have hfint : IntegrableOn (fun α : ℝ => α ^ (t + β) / risingFac α n) (Set.Ioo (0 : ℝ) ε) := by
      refine hIbound.mono' hmeas ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with a ha
      exact hle a ha
    have hnn : 0 ≤ᶠ[ae (volume.restrict (Set.Ioo (0 : ℝ) ε))]
        (fun α : ℝ => α ^ (t + β) / risingFac α n) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with a ha
      exact le_of_lt (div_pos (Real.rpow_pos_of_pos ha.1 (t + β)) (hfacpos a ha.1))
    refine (MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae hnn hfint).2 ?_
    have hsub : Set.Ioo (0 : ℝ) ε ⊆
        Function.support (fun α : ℝ => α ^ (t + β) / risingFac α n) ∩ Set.Ioo (0 : ℝ) ε := by
      intro a ha
      exact ⟨ne_of_gt (div_pos (Real.rpow_pos_of_pos ha.1 (t + β)) (hfacpos a ha.1)), ha⟩
    have hvol : (0 : ENNReal) < volume (Set.Ioo (0 : ℝ) ε) := by
      rw [Real.volume_Ioo]
      simpa using (ENNReal.ofReal_pos.mpr hε)
    exact lt_of_lt_of_le hvol (measure_mono hsub)
  · set L : ℝ := Real.log (n : ℝ) + 1 with hLdef
    set Z : ℝ :=
      ∫ a in Set.Ioo (0 : ℝ) ε, (Real.exp 1 * (n : ℝ)) ^ (-a) * a ^ (t + β - 1) with hZdef
    have hLpos : 0 < L := by
      have hs1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
      have h1n : (1 : ℝ) < (n : ℝ) := by linarith
      have hlog : 0 < Real.log (n : ℝ) := Real.log_pos h1n
      rw [hLdef]
      linarith
    have hnp : (0 : ℝ) < (n : ℝ) := by linarith
    have hnexp : Real.exp L = Real.exp 1 * (n : ℝ) := by
      rw [hLdef, Real.exp_add, Real.exp_log hnp]
      ring
    have key : ∀ N : ℝ, 0 < N →
        (∫ a in Set.Ioo (0 : ℝ) ε, (Real.exp 1 * (n : ℝ)) ^ (-a) * a ^ (N - 1))
          = L ^ (-N) * lowerGamma N (ε * L) := by
      intro N _
      have hexp : ∀ a : ℝ, (Real.exp 1 * (n : ℝ)) ^ (-a) = Real.exp (-(a * L)) := by
        intro a
        rw [← hnexp, Real.rpow_def_of_pos (Real.exp_pos L), Real.log_exp]
        rw [show L * -a = -(a * L) by ring]
      have h1 : (∫ a in Set.Ioo (0 : ℝ) ε, (Real.exp 1 * (n : ℝ)) ^ (-a) * a ^ (N - 1))
          = ∫ a in Set.Ioc (0 : ℝ) ε, Real.exp (-(a * L)) * a ^ (N - 1) := by
        rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo]
        simp only [hexp]
      have h2 : (∫ a in Set.Ioc (0 : ℝ) ε, Real.exp (-(a * L)) * a ^ (N - 1))
          = ∫ a in (0 : ℝ)..ε, Real.exp (-(a * L)) * a ^ (N - 1) := by
        rw [intervalIntegral.integral_of_le hε.le]
      have h3 : (∫ x in (0 : ℝ)..ε, (L * x) ^ (N - 1) * Real.exp (-(L * x)))
          = ∫ x in Set.Ioc (0 : ℝ) ε, (L * x) ^ (N - 1) * Real.exp (-(L * x)) := by
        rw [intervalIntegral.integral_of_le hε.le]
      have h4 : (∫ x in Set.Ioc (0 : ℝ) ε, (L * x) ^ (N - 1) * Real.exp (-(L * x)))
          = ∫ x in Set.Ioc (0 : ℝ) ε, L ^ (N - 1) * (Real.exp (-(x * L)) * x ^ (N - 1)) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
        have hx0 : 0 < x := hx.1
        rw [Real.mul_rpow (le_of_lt hLpos) (le_of_lt hx0), mul_comm L x]
        ring
      have h5 : (∫ x in Set.Ioc (0 : ℝ) ε, L ^ (N - 1) * (Real.exp (-(x * L)) * x ^ (N - 1)))
          = L ^ (N - 1) * ∫ x in Set.Ioc (0 : ℝ) ε, Real.exp (-(x * L)) * x ^ (N - 1) := by
        rw [MeasureTheory.integral_const_mul]
      have h6 : (∫ x in Set.Ioc (0 : ℝ) ε, Real.exp (-(x * L)) * x ^ (N - 1))
          = ∫ a in (0 : ℝ)..ε, Real.exp (-(a * L)) * a ^ (N - 1) := by
        rw [intervalIntegral.integral_of_le hε.le]
      have hmul := intervalIntegral.mul_integral_comp_mul_left (a := (0 : ℝ)) (b := ε)
        (f := fun z : ℝ => z ^ (N - 1) * Real.exp (-z)) L
      rw [mul_zero, mul_comm L ε] at hmul
      have hLN : L * L ^ (N - 1) = L ^ N := by
        rw [mul_comm L (L ^ (N - 1)), ← Real.rpow_add_one (ne_of_gt hLpos) (N - 1)]
        congr 1
        ring
      have h8 : L ^ N * (∫ a in (0 : ℝ)..ε, Real.exp (-(a * L)) * a ^ (N - 1))
          = ∫ z in (0 : ℝ)..(ε * L), z ^ (N - 1) * Real.exp (-z) := by
        rw [← hLN, mul_assoc, ← h6, ← h5, ← h4, ← h3]
        exact hmul
      have h9 : (∫ a in (0 : ℝ)..ε, Real.exp (-(a * L)) * a ^ (N - 1))
          = L ^ (-N) * (∫ z in (0 : ℝ)..(ε * L), z ^ (N - 1) * Real.exp (-z)) := by
        have hNz : L ^ N ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hLpos N)
        have hfin : ∀ X : ℝ, L ^ (-N) * (L ^ N * X) = X := by
          intro X
          rw [Real.rpow_neg hLpos.le N, ← mul_assoc]
          field_simp
        rw [← h8]
        exact (hfin _).symm
      calc (∫ a in Set.Ioo (0 : ℝ) ε, (Real.exp 1 * (n : ℝ)) ^ (-a) * a ^ (N - 1))
          = ∫ a in Set.Ioc (0 : ℝ) ε, Real.exp (-(a * L)) * a ^ (N - 1) := h1
        _ = ∫ a in (0 : ℝ)..ε, Real.exp (-(a * L)) * a ^ (N - 1) := h2
        _ = L ^ (-N) * (∫ z in (0 : ℝ)..(ε * L), z ^ (N - 1) * Real.exp (-z)) := h9
        _ = L ^ (-N) * lowerGamma N (ε * L) := by
              simp only [lowerGamma]
    have hZval : Z = L ^ (-(t + β)) * lowerGamma (t + β) (ε * L) := by
      rw [hZdef]
      exact key (t + β) htβ
    have hZsv : (∫ a in Set.Ioo (0 : ℝ) ε,
          a ^ (s : ℝ) * ((Real.exp 1 * (n : ℝ)) ^ (-a) * a ^ (t + β - 1)))
        = L ^ (-(t + (s : ℝ) + β)) * lowerGamma (t + (s : ℝ) + β) (ε * L) := by
      have hcongr : (∫ a in Set.Ioo (0 : ℝ) ε,
            a ^ (s : ℝ) * ((Real.exp 1 * (n : ℝ)) ^ (-a) * a ^ (t + β - 1)))
          = ∫ a in Set.Ioo (0 : ℝ) ε,
              (Real.exp 1 * (n : ℝ)) ^ (-a) * a ^ (t + (s : ℝ) + β - 1) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with a ha
        have ha0 : 0 < a := ha.1
        rw [show t + (s : ℝ) + β - 1 = (s : ℝ) + (t + β - 1) by ring,
          Real.rpow_add ha0 (s : ℝ) (t + β - 1)]
        ring
      rw [hcongr]
      refine key (t + (s : ℝ) + β) ?_
      have hs1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
      linarith
    have hratio : L ^ (-(s : ℝ)) *
          (lowerGamma (t + (s : ℝ) + β) (ε * L) / lowerGamma (t + β) (ε * L))
        = (∫ a in Set.Ioo (0 : ℝ) ε,
            a ^ (s : ℝ) * ((Real.exp 1 * (n : ℝ)) ^ (-a) * a ^ (t + β - 1))) / Z := by
      rw [hZsv, hZval]
      have hC0 : lowerGamma (t + β) (ε * L) ≠ 0 :=
        ne_of_gt (hL.1 (t + β) (ε * L) htβ (mul_pos hε hLpos))
      have hQ0 : L ^ (-(t + β)) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hLpos (-(t + β)))
      have hLs : L ^ (-(s : ℝ)) = L ^ (-(t + (s : ℝ) + β)) / L ^ (-(t + β)) := by
        rw [← Real.rpow_sub hLpos]
        congr 1
        ring
      rw [hLs]
      field_simp
    have hMLR : (∫ a in Set.Ioo (0 : ℝ) ε,
          a ^ (s : ℝ) * ((Real.exp 1 * (n : ℝ)) ^ (-a) * a ^ (t + β - 1))) / Z
         ≤ (∫ a in Set.Ioo (0 : ℝ) ε, a ^ (t + (s : ℝ) + β) / risingFac a n) /
           (∫ a in Set.Ioo (0 : ℝ) ε, a ^ (t + β) / risingFac a n) :=
        statopia_math_node_1113054774_24697df7 t ε β n s ht hε hε1 hβ hs hts
    rw [hratio]
    exact hMLR
  /- @proof-region region.target-node.session.d071cd196b4bbe28 end -/

end Statlib.Imported
end
