import ProverJobs.paper_fresh_20261028t224543381z_data_thinning.Vocabulary
import ProverJobs.paper_fresh_20261028t224543381z_data_thinning.Base

namespace PaperProofTasks.paper_fresh_20261028t224543381z_data_thinning

open _root_.PaperProofTasks.paper_fresh_20261028t224543381z_data_thinning.Statlib.Imported
open MeasureTheory ProbabilityTheory

namespace Statlib.Imported
open _root_.Statlib
open MeasureTheory ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_4104113938_66a528d1 : ∀ {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (hμ : IsProbabilityMeasure μ)
    (G : Kernel X Y) (hG : IsMarkovKernel G)
    (T : Y → X) (hT : Measurable T)
    (hRecon : ∀ᵐ x ∂μ, ∀ᵐ y ∂(G x), T y = x),
    Measure.map (fun y : Y => (T y, y)) (μ.bind G) =
      Measure.compProd (Measure.map T (μ.bind G)) G := by
  /- @proof-region region.target-node.session.1026a6981d769784 begin -/
  intro X Y _ _ μ hμ G hG T hT hRecon
  have hF : Measurable (fun y : Y => (T y, y)) := by measurability
  have hae : ∀ᵐ x ∂μ, (G x).map (fun y : Y => (T y, y)) = (G x).map (fun y : Y => (x, y)) := by
    filter_upwards [hRecon] with x hx
    refine Measure.map_congr ?_
    filter_upwards [hx] with y hy
    simp [hy]
  have hAG : AEMeasurable (⇑G) μ := by
    first | infer_instance | measurability
  have hkey : Measure.map (fun y : Y => (T y, y)) (μ.bind G) = Measure.compProd μ G := by
    refine Measure.ext ?_
    intro s hs
    rw [Measure.map_apply hF hs, Measure.bind_apply (hs.preimage hF) hAG, Measure.compProd_apply hs]
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with x hx
    have hmk : Measurable (fun y : Y => (x, y)) := by measurability
    rw [← Measure.map_apply hF hs, ← Measure.map_apply hmk hs]
    exact congrArg (fun ν : Measure (X × Y) => ν s) hx
  have hstat : Measure.map T (μ.bind G) = μ := by
    have hdet : AEMeasurable (fun y : Y => Measure.dirac (T y)) (μ.bind G) := by
      first | infer_instance | measurability
    have h1 : Measure.map T (μ.bind G) = (fun x => (G x).map T) ∘ₘ μ := by
      rw [← Measure.bind_dirac_eq_map (μ.bind G) hT, Measure.bind_bind hAG hdet]
      congr 1
      funext x
      exact Measure.bind_dirac_eq_map (G x) hT
    have h2 : (fun x => (G x).map T) =ᵐ[μ] (fun x => Measure.dirac x) := by
      filter_upwards [hRecon] with x hx
      have hc : (G x).map T = (G x).map (fun _ : Y => x) := by
        refine Measure.map_congr ?_
        filter_upwards [hx] with y hy
        simp [hy]
      rw [hc]
      simp
    rw [h1, Measure.bind_congr_right h2]
    rw [show (fun x : X => Measure.dirac x) ∘ₘ μ = Measure.map id μ from
      Measure.bind_dirac_eq_map μ measurable_id, Measure.map_id]
  rw [hstat, hkey]
  /- @proof-region region.target-node.session.1026a6981d769784 end -/

end Statlib.Imported

