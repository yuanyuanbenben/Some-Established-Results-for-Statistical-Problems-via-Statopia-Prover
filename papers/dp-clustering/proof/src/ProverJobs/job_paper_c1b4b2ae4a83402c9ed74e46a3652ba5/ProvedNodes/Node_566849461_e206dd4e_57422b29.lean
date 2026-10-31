import ProverJobs.job_paper_c1b4b2ae4a83402c9ed74e46a3652ba5.Vocabulary
import ProverJobs.job_paper_c1b4b2ae4a83402c9ed74e46a3652ba5.Base

open MeasureTheory Filter Topology
open scoped ENNReal
open Statlib.Imported

open MeasureTheory Filter Topology
open scoped ENNReal
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_566849461_e206dd4e : ∀ {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hf : IsProbDensity μ f),
    (Integrable f μ ∧ ∫ x, f x ∂μ = 1) ∧
      (∀ (Θ : Type*) (k : Θ → X → ℝ), (∀ θ, IsProbDensity μ (k θ)) →
        ∀ θ : Θ, Integrable (k θ) μ ∧ ∫ x, k θ x ∂μ = 1) := by
  /- @proof-region region.target-node.session.73e2775043e0c1ac begin -/
  intro X inst μ f hf
  have key : ∀ g : X → ℝ, IsProbDensity μ g → Integrable g μ ∧ ∫ x, g x ∂μ = 1 := by
    intro g hg
    obtain ⟨hgmeas, hgnonneg, hgprob⟩ := hg
    have hlin : ∫⁻ x, ENNReal.ofReal (g x) ∂μ = 1 := by
      have hmeasuniv : MeasurableSet (Set.univ : Set X) := MeasurableSet.univ
      have h : (μ.withDensity (fun x => ENNReal.ofReal (g x))) Set.univ
          = ∫⁻ a in Set.univ, ENNReal.ofReal (g a) ∂μ :=
        withDensity_apply (fun x => ENNReal.ofReal (g x)) hmeasuniv
      have huniv : (μ.withDensity (fun x => ENNReal.ofReal (g x))) Set.univ = 1 := measure_univ
      rw [h] at huniv
      simpa using huniv
    have hfin : HasFiniteIntegral g μ := by
      rw [hasFiniteIntegral_iff_ofReal hgnonneg, hlin]
      simp
    have hint : Integrable g μ := ⟨hgmeas.aestronglyMeasurable, hfin⟩
    refine ⟨hint, ?_⟩
    rw [integral_eq_lintegral_of_nonneg_ae hgnonneg hgmeas.aestronglyMeasurable, hlin]
    simp
  exact ⟨key f hf, fun Θ k hk θ => key (k θ) (hk θ)⟩
  /- @proof-region region.target-node.session.73e2775043e0c1ac end -/

end Statlib.Imported
