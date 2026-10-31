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
theorem statopia_math_node_9940328_8cef1cea : ∀ {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X]
    (k : Θ → X → ℝ) (hk : Measurable (Function.uncurry k)),
    Measurable (Function.uncurry (fun (P : ProbabilityMeasure Θ) (x : X) => dpmDensity k P x)) := by
  /- @proof-region region.target-node.session.4e9ecf3668897276 begin -/
  intro Θ X _ _ k hk
  have hφ : Measurable (fun z : Θ × X => ENNReal.ofReal (k z.1 z.2)) :=
    ENNReal.measurable_ofReal.comp hk
  change Measurable (fun p : ProbabilityMeasure Θ × X =>
      ∫⁻ θ, ENNReal.ofReal (k θ p.2) ∂(p.1).toMeasure)
  have hN : Measurable (fun p : ProbabilityMeasure Θ × X =>
      (p.1).toMeasure.prod (Measure.dirac p.2)) := by
    haveI : ∀ p : ProbabilityMeasure Θ × X,
        IsProbabilityMeasure ((p.1).toMeasure.prod (Measure.dirac p.2)) :=
      fun p => inferInstance
    refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
      (S := Set.image2 (fun x1 x2 => x1 ×ˢ x2) {s | MeasurableSet s} {t | MeasurableSet t})
      ?_ isPiSystem_prod ?_
    · exact (generateFrom_eq_prod (MeasurableSpace.generateFrom_measurableSet)
        (MeasurableSpace.generateFrom_measurableSet)
        ⟨fun _ => Set.univ, fun _ => by simp, by ext x; simp⟩
        ⟨fun _ => Set.univ, fun _ => by simp, by ext x; simp⟩).symm
    · rintro s ⟨A, hA, B, hB, hAB⟩
      subst hAB
      change Measurable fun a : ProbabilityMeasure Θ × X =>
        ((a.1.toMeasure).prod (Measure.dirac a.2)) (A ×ˢ B)
      have hpt : ∀ a : ProbabilityMeasure Θ × X,
          ((a.1.toMeasure).prod (Measure.dirac a.2)) (A ×ˢ B)
            = a.1.toMeasure A * (Measure.dirac a.2) B := by
        intro a
        exact Measure.prod_prod A B
      simp only [hpt]
      refine Measurable.mul ?_ ?_
      · exact ((Measure.measurable_measure.mp measurable_id) A hA).comp
          (measurable_subtype_coe.comp measurable_fst)
      · measurability
  have hM : Measurable (fun p : ProbabilityMeasure Θ × X =>
      ∫⁻ z : Θ × X, ENNReal.ofReal (k z.1 z.2) ∂((p.1).toMeasure.prod (Measure.dirac p.2))) :=
    (Measure.measurable_lintegral hφ).comp hN
  have heq : (fun p : ProbabilityMeasure Θ × X =>
      ∫⁻ z : Θ × X, ENNReal.ofReal (k z.1 z.2) ∂((p.1).toMeasure.prod (Measure.dirac p.2)))
      = fun p => ∫⁻ θ, ENNReal.ofReal (k θ p.2) ∂(p.1).toMeasure := by
    funext p
    rw [lintegral_prod (fun z : Θ × X => ENNReal.ofReal (k z.1 z.2)) hφ.aemeasurable]
    apply lintegral_congr
    intro θ
    exact lintegral_dirac' p.2 (hφ.comp (by measurability))
  rw [← heq]
  exact hM
  /- @proof-region region.target-node.session.4e9ecf3668897276 end -/

end Statlib.Imported
