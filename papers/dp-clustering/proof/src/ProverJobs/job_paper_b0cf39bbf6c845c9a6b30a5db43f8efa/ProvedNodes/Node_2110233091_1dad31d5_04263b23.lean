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
theorem statopia_math_node_2110233091_1dad31d5 : ∀ {X H : Type*} [MeasurableSpace X] [MeasurableSpace H]
    (P : Measure X) [IsProbabilityMeasure P]
    (nu : Measure H) [IsProbabilityMeasure nu]
    (g : H → X → ℝ) (hg : Measurable (Function.uncurry g))
    (h_neg_fin : ∀ᵐ x ∂P, ∫⁻ h, ENNReal.ofReal (max (-(g h x)) 0) ∂nu < ⊤)
    (h_pos_fin : ∀ᵐ x ∂P, ∫⁻ h, ENNReal.ofReal (max (g h x) 0) ∂nu < ⊤),
    ∀ᵐ x ∂(Measure.infinitePi (fun _ : ℕ => P)), ∀ n : ℕ,
      ENNReal.ofReal (Real.exp (∑ i ∈ Finset.range n, ∫ h, g h (x i) ∂nu))
        ≤ ∫⁻ h, ENNReal.ofReal (Real.exp (∑ i ∈ Finset.range n, g h (x i))) ∂nu := by
  /- @proof-region region.target-node.session.4caf69986dd6391c begin -/
  intro X H _ _ P _ ν _ g hg hNegFin hPosFin
  have hIntgAE : ∀ᵐ x ∂(Measure.infinitePi (fun _ : ℕ => P)), ∀ i : ℕ, Integrable (fun h => g h (x i)) ν := by
    have hsecMeas : ∀ y : X, Measurable (fun h => g h y) := fun y =>
      hg.comp (measurable_id.prod measurable_const : Measurable (fun h : H => (h, y)))
    have hPcombo : ∀ᵐ y ∂P,
        (∫⁻ h, ENNReal.ofReal (max (-(g h y)) 0) ∂ν < ⊤) ∧
        (∫⁻ h, ENNReal.ofReal (max (g h y) 0) ∂ν < ⊤) := hNegFin.and hPosFin
    have hcoordinate : ∀ i : ℕ, ∀ᵐ x ∂(Measure.infinitePi (fun _ : ℕ => P)),
        (∫⁻ h, ENNReal.ofReal (max (-(g h (x i))) 0) ∂ν < ⊤) ∧
        (∫⁻ h, ENNReal.ofReal (max (g h (x i)) 0) ∂ν < ⊤) := by
      intro i
      have h := (measurePreserving_eval_infinitePi (fun _ : ℕ => P) i).quasiMeasurePreserving.ae hPcombo
      simpa only [Function.eval] using h
    rw [MeasureTheory.ae_all_iff]
    intro i
    filter_upwards [hcoordinate i] with x hx
    obtain ⟨hneg, hpos⟩ := hx
    have hposMeas : AEStronglyMeasurable (fun h => max (g h (x i)) 0) ν :=
      ((hsecMeas (x i)).max (measurable_const : Measurable fun _ : H => (0 : ℝ))).aestronglyMeasurable
    have hnegMeas : AEStronglyMeasurable (fun h => max (-(g h (x i))) 0) ν :=
      (((hsecMeas (x i)).neg).max (measurable_const : Measurable fun _ : H => (0 : ℝ))).aestronglyMeasurable
    have hposInt : Integrable (fun h => max (g h (x i)) 0) ν :=
      (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hposMeas
        (Filter.Eventually.of_forall (fun h => le_max_right (g h (x i)) 0))).mp (ne_of_lt hpos)
    have hnegInt : Integrable (fun h => max (-(g h (x i))) 0) ν :=
      (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hnegMeas
        (Filter.Eventually.of_forall (fun h => le_max_right (-(g h (x i))) 0))).mp (ne_of_lt hneg)
    have hfun : (fun h => max (g h (x i)) 0 - max (-(g h (x i))) 0) = fun h => g h (x i) := by
      funext h
      by_cases hle : g h (x i) ≤ 0
      · rw [max_eq_right hle, max_eq_left (by linarith), zero_sub, neg_neg]
      · rw [max_eq_left (by linarith), max_eq_right (by linarith), sub_zero]
    rw [← hfun]
    exact hposInt.sub hnegInt
  filter_upwards [hIntgAE] with x hx
  intro n
  have hSecMeas : ∀ i : ℕ, Measurable (fun h => g h (x i)) := fun i =>
    hg.comp (measurable_id.prod measurable_const : Measurable (fun h : H => (h, x i)))
  have hSMeas : Measurable (fun h => ∑ i ∈ Finset.range n, g h (x i)) :=
    Finset.measurable_sum (Finset.range n) (fun i _ => hSecMeas i)
  have hIntgS : Integrable (fun h => ∑ i ∈ Finset.range n, g h (x i)) ν :=
    MeasureTheory.integrable_finset_sum (s := Finset.range n) (fun i _ => hx i)
  have hIntS : ∫ h, (∑ i ∈ Finset.range n, g h (x i)) ∂ν
      = ∑ i ∈ Finset.range n, ∫ h, g h (x i) ∂ν :=
    integral_finset_sum (Finset.range n) (fun i _ => hx i)
  by_cases hfin : ∫⁻ h, ENNReal.ofReal (Real.exp (∑ i ∈ Finset.range n, g h (x i))) ∂ν = ⊤
  · rw [hfin]
    exact le_top
  · have hpos : 0 ≤ᶠ[ae ν] (fun h => Real.exp (∑ i ∈ Finset.range n, g h (x i))) :=
      Filter.Eventually.of_forall (fun h => (Real.exp_pos _).le)
    have hExpAES : AEStronglyMeasurable (fun h => Real.exp (∑ i ∈ Finset.range n, g h (x i))) ν :=
      (Real.measurable_exp.comp hSMeas).aestronglyMeasurable
    have hexpIntg : Integrable (fun h => Real.exp (∑ i ∈ Finset.range n, g h (x i))) ν :=
      (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hExpAES hpos).mp hfin
    have hjensen : Real.exp (∫ h, (∑ i ∈ Finset.range n, g h (x i)) ∂ν)
        ≤ ∫ h, Real.exp (∑ i ∈ Finset.range n, g h (x i)) ∂ν :=
      ConvexOn.map_integral_le convexOn_exp Real.continuous_exp.continuousOn isClosed_univ
        (Filter.Eventually.of_forall (fun _ => Set.mem_univ _)) hIntgS hexpIntg
    rw [hIntS] at hjensen
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hexpIntg hpos]
    exact ENNReal.ofReal_le_ofReal hjensen

  /- @proof-region region.target-node.session.4caf69986dd6391c end -/

end Statlib.Imported
