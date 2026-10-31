import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q09.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q09.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q09.ProvedNodes.Node_2073386701_8222945a_f09b5f00
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q09.ProvedNodes.Node_3172609595_1d5a6f27_98766584


open MeasureTheory ProbabilityTheory
open Msc62GroundTruth

open MeasureTheory ProbabilityTheory
namespace Msc62GroundTruth

set_option autoImplicit false in
theorem statopia_math_node_2486692478_7ec19360 : ∀ (d : ℕ) (alpha : ℝ) (halpha : 0 < alpha)
    (n : ℕ) (hn : 1 ≤ n)
    (h : ℝ) (hh : h = Real.rpow (n : ℝ) (-1 / (2 * alpha + (d : ℝ))))
    (hh_pos : 0 < h)
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (g : Cube d → Omega → ℝ) (f0 : Cube d → ℝ)
    (L0 MAlpha Cv : ℝ) (hL0 : 0 ≤ L0) (hMAlpha : 0 ≤ MAlpha) (hCv : 0 ≤ Cv)
    (h_integrable : ∀ x, InInteriorBand h x →
      Integrable (g x) P ∧
        Integrable (fun omega => (g x omega - f0 x) ^ 2) P ∧
          Integrable (fun omega => (g x omega - ∫ z, g x z ∂P) ^ 2) P)
    (h_fluctuation : ∀ x, InInteriorBand h x →
      ∫ omega, (g x omega - ∫ z, g x z ∂P) ^ 2 ∂P ≤ Cv / ((n : ℝ) * h ^ d))
    (h_bias : ∀ x, InInteriorBand h x →
      |(∫ omega, g x omega ∂P) - f0 x| ≤ L0 * MAlpha * Real.rpow h alpha)
    (h_bandwidth : 1 / ((n : ℝ) * h ^ d) = Real.rpow h (2 * alpha))
    (x : Cube d) (hx : InInteriorBand h x),
    ∫ omega, (g x omega - f0 x) ^ 2 ∂P ≤
      (Cv + (L0 * MAlpha) ^ 2) * Real.rpow h (2 * alpha) := by
  /- @proof-region region.target-node.session.3653a7ae9ddd80ea begin -/
  intro d alpha halpha n hn h hh hh_pos Omega
  intro _
  intro P
  intro _
  intro g f0 L0 MAlpha Cv hL0 hMAlpha hCv h_integrable h_fluctuation h_bias h_bandwidth x hx
  obtain ⟨hg, _, hgv⟩ := h_integrable x hx
  set gb : ℝ := ∫ z, g x z ∂P with hgb
  have hgv' : Integrable (fun ω => (g x ω - gb) ^ 2) P := by
    simpa only [hgb] using hgv
  have hgb_int : Integrable (fun ω => g x ω - gb) P :=
    hg.sub (integrable_const gb)
  have hcross_int : Integrable (fun ω => 2 * (gb - f0 x) * (g x ω - gb)) P :=
    hgb_int.const_mul (2 * (gb - f0 x))
  have hconst_int : Integrable (fun _ : Omega => (gb - f0 x) ^ 2) P :=
    integrable_const _
  have hcenter : ∫ ω, (g x ω - gb) ∂P = 0 := by
    rw [integral_sub hg (integrable_const gb)]
    have hw : ∫ _ : Omega, gb ∂P = gb := by
      simp
    rw [hw, hgb]
    exact sub_self _
  have hexpand : ∫ ω, (g x ω - f0 x) ^ 2 ∂P
      = ∫ ω, (g x ω - gb) ^ 2 ∂P + (gb - f0 x) ^ 2 := by
    have hpt : ∀ ω : Omega, (g x ω - f0 x) ^ 2
        = (g x ω - gb) ^ 2 + 2 * (gb - f0 x) * (g x ω - gb) + (gb - f0 x) ^ 2 := by
      intro ω
      ring
    have h1 : ∫ ω, (g x ω - f0 x) ^ 2 ∂P
        = ∫ ω, ((g x ω - gb) ^ 2 + 2 * (gb - f0 x) * (g x ω - gb) + (gb - f0 x) ^ 2) ∂P :=
      integral_congr_ae (Filter.Eventually.of_forall hpt)
    have hstep : ∫ ω, ((g x ω - gb) ^ 2 + 2 * (gb - f0 x) * (g x ω - gb) + (gb - f0 x) ^ 2) ∂P
        = (∫ ω, ((g x ω - gb) ^ 2 + 2 * (gb - f0 x) * (g x ω - gb)) ∂P) + (gb - f0 x) ^ 2 := by
      have key : ∫ ω, ((g x ω - gb) ^ 2 + 2 * (gb - f0 x) * (g x ω - gb) + (gb - f0 x) ^ 2) ∂P
          = (∫ ω, ((g x ω - gb) ^ 2 + 2 * (gb - f0 x) * (g x ω - gb)) ∂P)
            + ∫ ω, (gb - f0 x) ^ 2 ∂P :=
        integral_add (hgv'.add hcross_int) hconst_int
      rw [key]
      have hw : ∫ _ : Omega, (gb - f0 x) ^ 2 ∂P = (gb - f0 x) ^ 2 := by
        simp
      rw [hw]
    have hstep2 : ∫ ω, ((g x ω - gb) ^ 2 + 2 * (gb - f0 x) * (g x ω - gb)) ∂P
        = (∫ ω, (g x ω - gb) ^ 2 ∂P) + 2 * (gb - f0 x) * ∫ ω, (g x ω - gb) ∂P := by
      have key : ∫ ω, ((g x ω - gb) ^ 2 + 2 * (gb - f0 x) * (g x ω - gb)) ∂P
          = (∫ ω, (g x ω - gb) ^ 2 ∂P) + ∫ ω, 2 * (gb - f0 x) * (g x ω - gb) ∂P :=
        integral_add hgv' hcross_int
      have key2 : ∫ ω, 2 * (gb - f0 x) * (g x ω - gb) ∂P
          = 2 * (gb - f0 x) * ∫ ω, (g x ω - gb) ∂P :=
        integral_const_mul (2 * (gb - f0 x)) (fun ω => g x ω - gb)
      rw [key, key2]
    rw [h1, hstep, hstep2, hcenter]
    ring
  have hfluc : ∫ ω, (g x ω - gb) ^ 2 ∂P ≤ Cv / ((n : ℝ) * h ^ d) := by
    simpa only [hgb] using h_fluctuation x hx
  have hbias : |gb - f0 x| ≤ L0 * MAlpha * Real.rpow h alpha := by
    simpa only [hgb] using h_bias x hx
  have hpow : (Real.rpow h alpha) ^ 2 = Real.rpow h (2 * alpha) := by
    have h1 : (Real.rpow h alpha) * (Real.rpow h alpha) = Real.rpow h (alpha + alpha) :=
      (Real.rpow_add hh_pos alpha alpha).symm
    calc (Real.rpow h alpha) ^ 2 = (Real.rpow h alpha) * (Real.rpow h alpha) := by ring
      _ = Real.rpow h (alpha + alpha) := h1
      _ = Real.rpow h (2 * alpha) := by
          rw [show alpha + alpha = 2 * alpha by ring]
  have hbias_sq : (gb - f0 x) ^ 2 ≤ (L0 * MAlpha) ^ 2 * Real.rpow h (2 * alpha) := by
    have hB : -(L0 * MAlpha * Real.rpow h alpha) ≤ gb - f0 x ∧
        gb - f0 x ≤ L0 * MAlpha * Real.rpow h alpha := abs_le.mp hbias
    have h1 : (gb - f0 x) ^ 2 ≤ (L0 * MAlpha * Real.rpow h alpha) ^ 2 :=
      sq_le_sq' hB.1 hB.2
    have h2 : (L0 * MAlpha * Real.rpow h alpha) ^ 2
        = (L0 * MAlpha) ^ 2 * (Real.rpow h alpha) ^ 2 := by ring
    rw [h2, hpow] at h1
    exact h1
  calc ∫ ω, (g x ω - f0 x) ^ 2 ∂P
      = ∫ ω, (g x ω - gb) ^ 2 ∂P + (gb - f0 x) ^ 2 := hexpand
    _ ≤ Cv / ((n : ℝ) * h ^ d) + (L0 * MAlpha) ^ 2 * Real.rpow h (2 * alpha) :=
        add_le_add hfluc hbias_sq
    _ = (Cv + (L0 * MAlpha) ^ 2) * Real.rpow h (2 * alpha) := by
        have h1 : Cv / ((n : ℝ) * h ^ d) = Cv * Real.rpow h (2 * alpha) := by
          rw [div_eq_mul_inv, ← one_div, h_bandwidth]
        rw [h1]
        ring
  /- @proof-region region.target-node.session.3653a7ae9ddd80ea end -/

end Msc62GroundTruth
