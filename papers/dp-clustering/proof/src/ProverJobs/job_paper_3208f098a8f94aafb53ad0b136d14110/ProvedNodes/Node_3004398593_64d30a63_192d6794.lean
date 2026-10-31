import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.Vocabulary
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.Base
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.ProvedNodes.Node_1136441573_47d2c9c7_d085168a
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.ProvedNodes.Node_1445702134_3c8d3810_8f7a15fe
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.ProvedNodes.Node_1908914932_1ac40602_b15647f0
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.ProvedNodes.Node_3224678180_5a630a9f_7124eef7
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.ProvedNodes.Node_3788355289_2a3e6b7e_b3f2870a





open MeasureTheory
open Statlib.Imported

noncomputable section
open MeasureTheory
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_3004398593_64d30a63 : ∀ (t : ℝ) (ht : 1 ≤ t)
    (pi : ℝ → ℝ) (hpi_meas : Measurable pi)
    (hpi_nonneg : ∀ α ∈ Set.Ioi (0 : ℝ), 0 ≤ pi α)
    (hpi_prob : ∫⁻ α in Set.Ioi (0 : ℝ), ENNReal.ofReal (pi α) = 1)
    (eps del beta : ℝ) (heps : 0 < eps) (heps_lt_one : eps < 1)
    (hdel : 0 < del) (hbeta : 0 < beta)
    (hA2 : ∀ α ∈ Set.Ioo (0 : ℝ) eps, del⁻¹ * α ^ beta ≤ pi α ∧ pi α ≤ del * α ^ beta)
    (n s : ℕ) (hs : 1 ≤ s) (hns : t + (s : ℝ) ≤ (n : ℝ)),
    lowerGamma (t + (s : ℝ) + beta) (eps * (Real.log (n : ℝ) + 1)) /
        (del ^ 2 * lowerGamma (t + beta) (eps * (Real.log (n : ℝ) + 1))) *
        (Real.log (n : ℝ) + 1) ^ (-(s : ℝ))
      ≤ (∫ α in Set.Ioo (0 : ℝ) eps, α ^ (t + (s : ℝ)) / risingFac α n * pi α) /
          (∫ α in Set.Ioo (0 : ℝ) eps, α ^ t / risingFac α n * pi α) ∧
    (∫ α in Set.Ioo (0 : ℝ) eps, α ^ (t + (s : ℝ)) / risingFac α n * pi α) /
          (∫ α in Set.Ioo (0 : ℝ) eps, α ^ t / risingFac α n * pi α)
      ≤ del ^ 2 * lowerGamma (t + (s : ℝ) + beta) (eps * Real.log (n : ℝ)) /
          lowerGamma (t + beta) (eps * Real.log (n : ℝ)) *
          (Real.log ((n : ℝ) / (1 + eps))) ^ (-(s : ℝ)) := by
  /- @proof-region region.target-node.session.7e03b86133c9ff05 begin -/
  intro t ht π hπ_meas hπ_nonneg hπ_prob ε δ β hε hε1 hδ hβ hA2 n s hs hns
  have hs1 : (1:ℝ) ≤ (s:ℝ) := by exact_mod_cast hs
  have hn2 : (2:ℝ) ≤ (n:ℝ) := by linarith
  have hlogc : 0 < Real.log ((n:ℝ) / (1 + ε)) := by
    apply Real.log_pos
    rw [lt_div_iff₀ (by linarith : (0:ℝ) < 1 + ε)]
    nlinarith
  obtain ⟨hIntAs, -, hIntB, hBpos, -, -, -, -, -⟩ :=
    statopia_math_node_3788355289_2a3e6b7e t ht π hπ_meas hπ_nonneg hπ_prob
      ε δ β hε hδ hβ hA2 n s hs (by linarith)
  obtain ⟨hInt0, hInts, hΦ0pos, hEup⟩ :=
    statopia_math_node_1908914932_1ac40602 t ε β n s ht hε hε1 hβ hs (by linarith)
  have hElow : (Real.log (n:ℝ) + 1) ^ (-(s:ℝ)) *
        (lowerGamma (t + (s:ℝ) + β) (ε * (Real.log (n:ℝ) + 1)) /
          lowerGamma (t + β) (ε * (Real.log (n:ℝ) + 1))) ≤
      (∫ α in Set.Ioo (0:ℝ) ε, α ^ (t + (s:ℝ) + β) / risingFac α n) /
      (∫ α in Set.Ioo (0:ℝ) ε, α ^ (t + β) / risingFac α n) :=
    (statopia_math_node_1136441573_47d2c9c7 t ε β n s ht hε hε1 hβ hs (by linarith)).2
  have hγmono : lowerGamma (t + (s:ℝ) + β) (ε * Real.log ((n:ℝ) / (1 + ε))) /
        lowerGamma (t + β) (ε * Real.log ((n:ℝ) / (1 + ε))) ≤
      lowerGamma (t + (s:ℝ) + β) (ε * Real.log (n:ℝ)) /
        lowerGamma (t + β) (ε * Real.log (n:ℝ)) := by
    obtain ⟨-, -, -, -, -, -, -, hratio⟩ := statopia_math_node_3224678180_5a630a9f
    have hlogn : 0 < Real.log (n:ℝ) := Real.log_pos (by linarith)
    have harg : t + (s:ℝ) + β = (t + β) + (s:ℝ) := by ring
    rw [harg]
    refine hratio (t + β) (s:ℝ) (by linarith) (by linarith) ?_ ?_ ?_
    · exact mul_pos hε hlogc
    · exact mul_pos hε hlogn
    · have hposn : (0:ℝ) < (n:ℝ) := by linarith
      have hle : (n:ℝ) / (1 + ε) ≤ (n:ℝ) := by
        rw [div_le_iff₀ (by linarith : (0:ℝ) < 1 + ε)]
        nlinarith
      exact mul_le_mul_of_nonneg_left
        (Real.log_le_log (div_pos hposn (by linarith : (0:ℝ) < 1 + ε)) hle) (le_of_lt hε)
  obtain ⟨hrfacpos, -, -, -, -⟩ := statopia_math_node_1445702134_3c8d3810
  have hrpos : ∀ (a : ℝ), 0 < a → ∀ n : ℕ, 0 < risingFac a n := fun a ha n => hrfacpos a n ha
  have hsIoo : MeasurableSet (Set.Ioo (0:ℝ) ε) := measurableSet_Ioo
  have hΦs_nonneg : 0 ≤ ∫ α in Set.Ioo (0:ℝ) ε, α ^ (t + (s:ℝ) + β) / risingFac α n :=
    MeasureTheory.setIntegral_nonneg hsIoo (fun x hx =>
      div_nonneg (Real.rpow_nonneg (le_of_lt hx.1) _) (le_of_lt (hrpos x hx.1 n)))
  have hAle : (∫ α in Set.Ioo (0:ℝ) ε, α ^ (t + (s:ℝ)) / risingFac α n * π α)
      ≤ δ * (∫ α in Set.Ioo (0:ℝ) ε, α ^ (t + (s:ℝ) + β) / risingFac α n) := by
    have hg : IntegrableOn (fun α : ℝ => δ * (α ^ (t + (s:ℝ) + β) / risingFac α n))
        (Set.Ioo (0:ℝ) ε) := MeasureTheory.Integrable.const_mul hInts δ
    have hpt : ∀ x ∈ Set.Ioo (0:ℝ) ε,
        x ^ (t + (s:ℝ)) / risingFac x n * π x ≤ δ * (x ^ (t + (s:ℝ) + β) / risingFac x n) := by
      intro x hx
      obtain ⟨hx0, hxlt⟩ := hx
      obtain ⟨-, hup⟩ := hA2 x ⟨hx0, hxlt⟩
      have hfac : (0:ℝ) < risingFac x n := hrpos x hx0 n
      have hbase : 0 ≤ x ^ (t + (s:ℝ)) / risingFac x n :=
        div_nonneg (Real.rpow_nonneg (le_of_lt hx0) _) (le_of_lt hfac)
      have hsplit : x ^ (t + (s:ℝ) + β) = x ^ (t + (s:ℝ)) * x ^ β := Real.rpow_add hx0 _ _
      calc x ^ (t + (s:ℝ)) / risingFac x n * π x
          ≤ x ^ (t + (s:ℝ)) / risingFac x n * (δ * x ^ β) := mul_le_mul_of_nonneg_left hup hbase
        _ = δ * (x ^ (t + (s:ℝ) + β) / risingFac x n) := by
            rw [hsplit, div_eq_mul_inv, div_eq_mul_inv]
            ring
    have hstep := MeasureTheory.setIntegral_mono_on hIntAs hg hsIoo hpt
    rwa [MeasureTheory.integral_const_mul] at hstep
  have hAge : δ⁻¹ * (∫ α in Set.Ioo (0:ℝ) ε, α ^ (t + (s:ℝ) + β) / risingFac α n)
      ≤ (∫ α in Set.Ioo (0:ℝ) ε, α ^ (t + (s:ℝ)) / risingFac α n * π α) := by
    have hg : IntegrableOn (fun α : ℝ => δ⁻¹ * (α ^ (t + (s:ℝ) + β) / risingFac α n))
        (Set.Ioo (0:ℝ) ε) := MeasureTheory.Integrable.const_mul hInts δ⁻¹
    have hpt : ∀ x ∈ Set.Ioo (0:ℝ) ε,
        δ⁻¹ * (x ^ (t + (s:ℝ) + β) / risingFac x n)
          ≤ x ^ (t + (s:ℝ)) / risingFac x n * π x := by
      intro x hx
      obtain ⟨hx0, hxlt⟩ := hx
      obtain ⟨hlow, -⟩ := hA2 x ⟨hx0, hxlt⟩
      have hfac : (0:ℝ) < risingFac x n := hrpos x hx0 n
      have hbase : 0 ≤ x ^ (t + (s:ℝ)) / risingFac x n :=
        div_nonneg (Real.rpow_nonneg (le_of_lt hx0) _) (le_of_lt hfac)
      have hsplit : x ^ (t + (s:ℝ) + β) = x ^ (t + (s:ℝ)) * x ^ β := Real.rpow_add hx0 _ _
      calc δ⁻¹ * (x ^ (t + (s:ℝ) + β) / risingFac x n)
          = x ^ (t + (s:ℝ)) / risingFac x n * (δ⁻¹ * x ^ β) := by
            rw [hsplit, div_eq_mul_inv, div_eq_mul_inv]
            ring
        _ ≤ x ^ (t + (s:ℝ)) / risingFac x n * π x := mul_le_mul_of_nonneg_left hlow hbase
    have hstep := MeasureTheory.setIntegral_mono_on hg hIntAs hsIoo hpt
    rwa [MeasureTheory.integral_const_mul] at hstep
  have hBle : (∫ α in Set.Ioo (0:ℝ) ε, α ^ t / risingFac α n * π α)
      ≤ δ * (∫ α in Set.Ioo (0:ℝ) ε, α ^ (t + β) / risingFac α n) := by
    have hg : IntegrableOn (fun α : ℝ => δ * (α ^ (t + β) / risingFac α n))
        (Set.Ioo (0:ℝ) ε) := MeasureTheory.Integrable.const_mul hInt0 δ
    have hpt : ∀ x ∈ Set.Ioo (0:ℝ) ε,
        x ^ t / risingFac x n * π x ≤ δ * (x ^ (t + β) / risingFac x n) := by
      intro x hx
      obtain ⟨hx0, hxlt⟩ := hx
      obtain ⟨-, hup⟩ := hA2 x ⟨hx0, hxlt⟩
      have hfac : (0:ℝ) < risingFac x n := hrpos x hx0 n
      have hbase : 0 ≤ x ^ t / risingFac x n :=
        div_nonneg (Real.rpow_nonneg (le_of_lt hx0) _) (le_of_lt hfac)
      have hsplit : x ^ (t + β) = x ^ t * x ^ β := Real.rpow_add hx0 _ _
      calc x ^ t / risingFac x n * π x
          ≤ x ^ t / risingFac x n * (δ * x ^ β) := mul_le_mul_of_nonneg_left hup hbase
        _ = δ * (x ^ (t + β) / risingFac x n) := by
            rw [hsplit, div_eq_mul_inv, div_eq_mul_inv]
            ring
    have hstep := MeasureTheory.setIntegral_mono_on hIntB hg hsIoo hpt
    rwa [MeasureTheory.integral_const_mul] at hstep
  have hBGe : δ⁻¹ * (∫ α in Set.Ioo (0:ℝ) ε, α ^ (t + β) / risingFac α n)
      ≤ (∫ α in Set.Ioo (0:ℝ) ε, α ^ t / risingFac α n * π α) := by
    have hg : IntegrableOn (fun α : ℝ => δ⁻¹ * (α ^ (t + β) / risingFac α n))
        (Set.Ioo (0:ℝ) ε) := MeasureTheory.Integrable.const_mul hInt0 δ⁻¹
    have hpt : ∀ x ∈ Set.Ioo (0:ℝ) ε,
        δ⁻¹ * (x ^ (t + β) / risingFac x n) ≤ x ^ t / risingFac x n * π x := by
      intro x hx
      obtain ⟨hx0, hxlt⟩ := hx
      obtain ⟨hlow, -⟩ := hA2 x ⟨hx0, hxlt⟩
      have hfac : (0:ℝ) < risingFac x n := hrpos x hx0 n
      have hbase : 0 ≤ x ^ t / risingFac x n :=
        div_nonneg (Real.rpow_nonneg (le_of_lt hx0) _) (le_of_lt hfac)
      have hsplit : x ^ (t + β) = x ^ t * x ^ β := Real.rpow_add hx0 _ _
      calc δ⁻¹ * (x ^ (t + β) / risingFac x n)
          = x ^ t / risingFac x n * (δ⁻¹ * x ^ β) := by
            rw [hsplit, div_eq_mul_inv, div_eq_mul_inv]
            ring
        _ ≤ x ^ t / risingFac x n * π x := mul_le_mul_of_nonneg_left hlow hbase
    have hstep := MeasureTheory.setIntegral_mono_on hg hIntB hsIoo hpt
    rwa [MeasureTheory.integral_const_mul] at hstep
  have hsand_lo : (δ^2)⁻¹ * ((∫ α in Set.Ioo (0:ℝ) ε, α ^ (t + (s:ℝ) + β) / risingFac α n) /
        (∫ α in Set.Ioo (0:ℝ) ε, α ^ (t + β) / risingFac α n)) ≤
      (∫ α in Set.Ioo (0:ℝ) ε, α ^ (t + (s:ℝ)) / risingFac α n * π α) /
        (∫ α in Set.Ioo (0:ℝ) ε, α ^ t / risingFac α n * π α) := by
    rw [le_div_iff₀ hBpos]
    have hcoe : 0 ≤ (δ^2)⁻¹ * ((∫ α in Set.Ioo (0:ℝ) ε, α ^ (t + (s:ℝ) + β) / risingFac α n) /
        (∫ α in Set.Ioo (0:ℝ) ε, α ^ (t + β) / risingFac α n)) :=
      mul_nonneg (le_of_lt (by positivity : (0:ℝ) < (δ^2)⁻¹))
        (div_nonneg hΦs_nonneg (le_of_lt hΦ0pos))
    calc (δ^2)⁻¹ * ((∫ α in Set.Ioo (0:ℝ) ε, α ^ (t + (s:ℝ) + β) / risingFac α n) /
          (∫ α in Set.Ioo (0:ℝ) ε, α ^ (t + β) / risingFac α n)) *
          (∫ α in Set.Ioo (0:ℝ) ε, α ^ t / risingFac α n * π α)
        ≤ (δ^2)⁻¹ * ((∫ α in Set.Ioo (0:ℝ) ε, α ^ (t + (s:ℝ) + β) / risingFac α n) /
          (∫ α in Set.Ioo (0:ℝ) ε, α ^ (t + β) / risingFac α n)) *
          (δ * (∫ α in Set.Ioo (0:ℝ) ε, α ^ (t + β) / risingFac α n)) :=
          mul_le_mul_of_nonneg_left hBle hcoe
      _ = δ⁻¹ * (∫ α in Set.Ioo (0:ℝ) ε, α ^ (t + (s:ℝ) + β) / risingFac α n) := by
          have h0 : (∫ α in Set.Ioo (0:ℝ) ε, α ^ (t + β) / risingFac α n) ≠ 0 := ne_of_gt hΦ0pos
          have hδ0 : δ ≠ 0 := ne_of_gt hδ
          field_simp
      _ ≤ _ := hAge
  have hsand_up : (∫ α in Set.Ioo (0:ℝ) ε, α ^ (t + (s:ℝ)) / risingFac α n * π α) /
        (∫ α in Set.Ioo (0:ℝ) ε, α ^ t / risingFac α n * π α) ≤
      δ^2 * ((∫ α in Set.Ioo (0:ℝ) ε, α ^ (t + (s:ℝ) + β) / risingFac α n) /
        (∫ α in Set.Ioo (0:ℝ) ε, α ^ (t + β) / risingFac α n)) := by
    rw [div_le_iff₀ hBpos]
    have hcoe : 0 ≤ δ^2 * ((∫ α in Set.Ioo (0:ℝ) ε, α ^ (t + (s:ℝ) + β) / risingFac α n) /
        (∫ α in Set.Ioo (0:ℝ) ε, α ^ (t + β) / risingFac α n)) :=
      mul_nonneg (by positivity) (div_nonneg hΦs_nonneg (le_of_lt hΦ0pos))
    calc (∫ α in Set.Ioo (0:ℝ) ε, α ^ (t + (s:ℝ)) / risingFac α n * π α)
        ≤ δ * (∫ α in Set.Ioo (0:ℝ) ε, α ^ (t + (s:ℝ) + β) / risingFac α n) := hAle
      _ = δ^2 * ((∫ α in Set.Ioo (0:ℝ) ε, α ^ (t + (s:ℝ) + β) / risingFac α n) /
            (∫ α in Set.Ioo (0:ℝ) ε, α ^ (t + β) / risingFac α n)) *
            (δ⁻¹ * (∫ α in Set.Ioo (0:ℝ) ε, α ^ (t + β) / risingFac α n)) := by
          have h0 : (∫ α in Set.Ioo (0:ℝ) ε, α ^ (t + β) / risingFac α n) ≠ 0 := ne_of_gt hΦ0pos
          have hδ0 : δ ≠ 0 := ne_of_gt hδ
          field_simp
      _ ≤ δ^2 * ((∫ α in Set.Ioo (0:ℝ) ε, α ^ (t + (s:ℝ) + β) / risingFac α n) /
            (∫ α in Set.Ioo (0:ℝ) ε, α ^ (t + β) / risingFac α n)) *
            (∫ α in Set.Ioo (0:ℝ) ε, α ^ t / risingFac α n * π α) :=
          mul_le_mul_of_nonneg_left hBGe hcoe
  refine ⟨?_, ?_⟩
  · have h1 : lowerGamma (t + (s:ℝ) + β) (ε * (Real.log (n:ℝ) + 1)) /
          (δ ^ 2 * lowerGamma (t + β) (ε * (Real.log (n:ℝ) + 1))) *
          (Real.log (n:ℝ) + 1) ^ (-(s:ℝ))
        = (δ^2)⁻¹ * ((Real.log (n:ℝ) + 1) ^ (-(s:ℝ)) *
            (lowerGamma (t + (s:ℝ) + β) (ε * (Real.log (n:ℝ) + 1)) /
              lowerGamma (t + β) (ε * (Real.log (n:ℝ) + 1)))) := by
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
      ring
    rw [h1]
    exact le_trans (mul_le_mul_of_nonneg_left hElow (by positivity)) hsand_lo
  · have h2 : δ^2 * ((Real.log ((n:ℝ) / (1 + ε))) ^ (-(s:ℝ)) *
          (lowerGamma (t + (s:ℝ) + β) (ε * Real.log (n:ℝ)) /
            lowerGamma (t + β) (ε * Real.log (n:ℝ))))
        = δ ^ 2 * lowerGamma (t + (s:ℝ) + β) (ε * Real.log (n:ℝ)) /
              lowerGamma (t + β) (ε * Real.log (n:ℝ)) *
            (Real.log ((n:ℝ) / (1 + ε))) ^ (-(s:ℝ)) := by
      rw [div_eq_mul_inv]
      ring
    rw [← h2]
    exact le_trans hsand_up (le_trans (mul_le_mul_of_nonneg_left hEup (by positivity))
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hγmono (by positivity))
        (by positivity)))
  /- @proof-region region.target-node.session.7e03b86133c9ff05 end -/

end Statlib.Imported
end
