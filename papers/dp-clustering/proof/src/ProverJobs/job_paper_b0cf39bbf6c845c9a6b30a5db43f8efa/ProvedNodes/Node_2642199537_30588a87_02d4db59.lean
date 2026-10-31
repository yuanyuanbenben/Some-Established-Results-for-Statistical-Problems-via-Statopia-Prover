import ProverJobs.job_paper_b0cf39bbf6c845c9a6b30a5db43f8efa.Vocabulary
import ProverJobs.job_paper_b0cf39bbf6c845c9a6b30a5db43f8efa.Base

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal MeasureTheory Topology BigOperators
open Statlib.Imported
open Statlib.Imported.DPMModel

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal MeasureTheory Topology BigOperators
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_2642199537_30588a87 : ∀ {X H : Type*} [MeasurableSpace X] [MeasurableSpace H]
    (P : Measure X) [IsProbabilityMeasure P] (ν : Measure H) [IsProbabilityMeasure ν]
    (g : H → X → ℝ) (hg : Measurable (Function.uncurry g)) (delta1 : ℝ)
    (h_int : ∀ᵐ h ∂ν, MeasureTheory.Integrable (g h) P)
    (h_lower : ∀ᵐ h ∂ν, -delta1 ≤ ∫ x, g h x ∂P)
    (h_pos_bound : ∀ᵐ h ∂ν, ∫⁻ x, ENNReal.ofReal (max (g h x) 0) ∂P ≤ (1 : ℝ≥0∞))
    (h_neg_bound : ∀ᵐ h ∂ν,
      ∫⁻ x, ENNReal.ofReal (max (-(g h x)) 0) ∂P ≤ ENNReal.ofReal (delta1 + 1)),
    Measurable (fun x => ∫ h, g h x ∂ν) ∧
      MeasureTheory.Integrable (fun x => ∫ h, g h x ∂ν) P ∧
      -delta1 ≤ ∫ x, (∫ h, g h x ∂ν) ∂P := by
  /- @proof-region region.target-node.session.cc7ebc352c403d91 begin -/
  intro X H _ _ P _ ν _ g hg delta1 h_int h_lower h_pos_bound h_neg_bound
  have hFm : Measurable (fun p : X × H => g p.2 p.1) := hg.comp measurable_swap
  have hbar_meas : Measurable (fun x => ∫ h, g h x ∂ν) :=
    (MeasureTheory.StronglyMeasurable.integral_prod_right' (ν := ν) hFm.stronglyMeasurable).measurable
  have hnice : ∀ h : H, Measurable (fun x => g h x) := fun h =>
    hg.comp (measurable_prodMk_left (x := h))
  have hkey : ∀ (h : H) (x : X),
      ‖g h x‖ₑ = ENNReal.ofReal (max (g h x) 0) + ENNReal.ofReal (max (-(g h x)) 0) := by
    intro h x
    classical
    rw [Real.enorm_eq_ofReal_abs,
      ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)]
    congr 1
    by_cases hx : (0 : ℝ) ≤ g h x
    · rw [abs_of_nonneg hx, max_eq_left hx, max_eq_right (by linarith : -(g h x) ≤ 0)]
      ring
    · rw [not_le] at hx
      rw [abs_of_neg hx, max_eq_right hx.le,
        max_eq_left (by linarith : (0 : ℝ) ≤ -(g h x))]
      ring
  have hkernel : ∀ h : H,
      ∫⁻ x, ‖g h x‖ₑ ∂P
        ≤ (∫⁻ x, ENNReal.ofReal (max (g h x) 0) ∂P)
          + ∫⁻ x, ENNReal.ofReal (max (-(g h x)) 0) ∂P := by
    intro h
    calc ∫⁻ x, ‖g h x‖ₑ ∂P
        = ∫⁻ x, (ENNReal.ofReal (max (g h x) 0)
            + ENNReal.ofReal (max (-(g h x)) 0)) ∂P := by
          simp only [hkey]
      _ ≤ (∫⁻ x, ENNReal.ofReal (max (g h x) 0) ∂P)
            + ∫⁻ x, ENNReal.ofReal (max (-(g h x)) 0) ∂P :=
          le_of_eq (MeasureTheory.lintegral_add_left
            (f := fun x => ENNReal.ofReal (max (g h x) 0))
            (g := fun x => ENNReal.ofReal (max (-(g h x)) 0))
            (by measurability))
  have h3 : ∀ᵐ h ∂ν, ∫⁻ x, ‖g h x‖ₑ ∂P ≤ 1 + ENNReal.ofReal (delta1 + 1) := by
    filter_upwards [h_pos_bound, h_neg_bound] with h hp hn
    exact le_trans (hkernel h) (add_le_add hp hn)
  have hIntF : MeasureTheory.Integrable (fun p : X × H => g p.2 p.1) (P.prod ν) := by
    have hgu : Measurable (fun z : H × X => g z.1 z.2) := hg
    have hKmf : Measurable (fun z : H × X => ‖g z.1 z.2‖ₑ) := by measurability
    have hb : ∫⁻ z : H × X, ‖g z.1 z.2‖ₑ ∂(ν.prod P)
        ≤ 1 + ENNReal.ofReal (delta1 + 1) := by
      rw [MeasureTheory.lintegral_prod (f := fun z : H × X => ‖g z.1 z.2‖ₑ)
        hKmf.aemeasurable]
      calc ∫⁻ h, ∫⁻ x, ‖g h x‖ₑ ∂P ∂ν
          ≤ ∫⁻ _h, (1 + ENNReal.ofReal (delta1 + 1)) ∂ν :=
            MeasureTheory.lintegral_mono_ae h3
        _ = 1 + ENNReal.ofReal (delta1 + 1) := by simp
    have hswap : ∫⁻ p : X × H, ‖g p.2 p.1‖ₑ ∂(P.prod ν)
        = ∫⁻ z : H × X, ‖g z.1 z.2‖ₑ ∂(ν.prod P) :=
      (MeasureTheory.lintegral_prod_swap (f := fun p : X × H => ‖g p.2 p.1‖ₑ)).symm
    have hC : (1 + ENNReal.ofReal (delta1 + 1)) < ⊤ := by simp
    have hFfi : MeasureTheory.HasFiniteIntegral (fun p : X × H => g p.2 p.1) (P.prod ν) := by
      show ∫⁻ p : X × H, ‖g p.2 p.1‖ₑ ∂(P.prod ν) < ⊤
      rw [hswap]
      exact lt_of_le_of_lt hb hC
    exact ⟨hFm.aestronglyMeasurable, hFfi⟩
  refine ⟨hbar_meas, ?_, ?_⟩
  · exact MeasureTheory.Integrable.integral_prod_left
      (f := fun p : X × H => g p.2 p.1) hIntF
  · have hintH : MeasureTheory.Integrable (fun h => ∫ x, g h x ∂P) ν :=
      MeasureTheory.Integrable.integral_prod_right
        (f := fun p : X × H => g p.2 p.1) hIntF
    have hswapint : ∫ x, (∫ h, g h x ∂ν) ∂P = ∫ h, (∫ x, g h x ∂P) ∂ν :=
      MeasureTheory.integral_integral_swap (f := fun x h => g h x) hIntF
    have hconst : MeasureTheory.Integrable (fun _ : H => -delta1) ν :=
      MeasureTheory.integrable_const (-delta1)
    have hmono : ∫ _h : H, -delta1 ∂ν ≤ ∫ h, (∫ x, g h x ∂P) ∂ν :=
      MeasureTheory.integral_mono_ae hconst hintH h_lower
    have hc : ∫ _h : H, -delta1 ∂ν = -delta1 := by simp
    calc -delta1 = ∫ _h : H, -delta1 ∂ν := hc.symm
      _ ≤ ∫ h, (∫ x, g h x ∂P) ∂ν := hmono
      _ = ∫ x, (∫ h, g h x ∂ν) ∂P := hswapint.symm
  /- @proof-region region.target-node.session.cc7ebc352c403d91 end -/

end Statlib.Imported
