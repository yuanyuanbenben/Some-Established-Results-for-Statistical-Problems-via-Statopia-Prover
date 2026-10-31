import ProverJobs.job_paper_c1b4b2ae4a83402c9ed74e46a3652ba5.Vocabulary
import ProverJobs.job_paper_c1b4b2ae4a83402c9ed74e46a3652ba5.Base
import ProverJobs.job_paper_c1b4b2ae4a83402c9ed74e46a3652ba5.ProvedNodes.Node_566849461_e206dd4e_57422b29

open MeasureTheory Filter Topology
open scoped ENNReal
open Statlib.Imported

open MeasureTheory Filter Topology
open scoped ENNReal
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_3633848309_047de4fc : ∀ {X Θ : Type*} [MeasurableSpace X]
    (μ : Measure X) (k : Θ → X → ℝ) (hK : ∀ p : Θ, IsProbDensity μ (k p))
    (t : ℕ) (ht : 1 ≤ t) (w : Fin t → ℝ) (hw_pos : ∀ j, 0 < w j)
    (hw_sum : ∑ j, w j = 1) (params : Fin t → Θ),
    IsProbDensity μ (fun x => ∑ j, w j * k (params j) x) := by
  /- @proof-region region.target-node.session.80e3a311bff30fb5 begin -/
  intro X Θ hmX μ k hK t ht w hw_pos hw_sum params
  letI : MeasurableSpace X := hmX
  classical
  have ht0 : 0 < t := lt_of_lt_of_le Nat.zero_lt_one ht
  have hmass : ∀ θ : Θ, Integrable (k θ) μ ∧ ∫ x, k θ x ∂μ = 1 :=
    (statopia_math_node_566849461_e206dd4e μ (k (params ⟨0, ht0⟩))
      (hK (params ⟨0, ht0⟩))).2 Θ k hK
  have hterm : ∀ j : Fin t, Integrable (fun x => w j * k (params j) x) μ := fun j =>
    (hmass (params j)).1.const_mul (w j)
  have hInt : Integrable (fun x => ∑ j : Fin t, w j * k (params j) x) μ :=
    MeasureTheory.integrable_finset_sum Finset.univ fun j _ => hterm j
  have hcoef : ∀ j : Fin t, ∫ x, w j * k (params j) x ∂μ = w j := by
    intro j
    rw [MeasureTheory.integral_const_mul (w j) (k (params j)), (hmass (params j)).2, mul_one]
  have hint_eq : ∫ x, ∑ j : Fin t, w j * k (params j) x ∂μ = 1 := by
    rw [MeasureTheory.integral_finset_sum Finset.univ fun j _ => hterm j]
    have hsum_eq : ∑ j : Fin t, ∫ x, w j * k (params j) x ∂μ = ∑ j : Fin t, w j :=
      Finset.sum_congr rfl fun j _ => hcoef j
    rw [hsum_eq]
    exact hw_sum
  have hmeas : AEMeasurable (fun x => ∑ j : Fin t, w j * k (params j) x) μ := by
    have h : ∀ j : Fin t, AEMeasurable (fun x => w j * k (params j) x) μ := fun j =>
      (hK (params j)).1.const_mul (w j)
    simpa using Finset.aemeasurable_fun_sum (Finset.univ : Finset (Fin t)) fun j _ => h j
  have hnn : ∀ᵐ x ∂μ, 0 ≤ ∑ j : Fin t, w j * k (params j) x := by
    have h : ∀ᵐ x ∂μ, ∀ j : Fin t, 0 ≤ w j * k (params j) x :=
      Filter.eventually_all.2 fun j =>
        ((hK (params j)).2.1).mono fun x hx => mul_nonneg (le_of_lt (hw_pos j)) hx
    filter_upwards [h] with x hx
    exact Finset.sum_nonneg fun j _ => hx j
  refine ⟨hmeas, hnn, ?_⟩
  rw [MeasureTheory.isProbabilityMeasure_iff,
    MeasureTheory.withDensity_apply
      (fun x => ENNReal.ofReal (∑ j : Fin t, w j * k (params j) x)) MeasurableSet.univ,
    MeasureTheory.setLIntegral_univ]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hnn, hint_eq, ENNReal.ofReal_one]
  /- @proof-region region.target-node.session.80e3a311bff30fb5 end -/

end Statlib.Imported
