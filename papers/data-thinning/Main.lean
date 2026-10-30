import ProverJobs.paper_fresh_20261028t224543381z_data_thinning.Vocabulary
import ProverJobs.paper_fresh_20261028t224543381z_data_thinning.ProvedNodes
import ProverJobs.paper_fresh_20261028t224543381z_data_thinning.Base

namespace Statlib.Imported
open MeasureTheory ProbabilityTheory

theorem Theorem_1_Main_theorem_thm_generalized_thinning
    {Ω X : Type*} [Nonempty Ω] [MeasurableSpace X]
    (K : ℕ) (hK : 0 < K)
    (P : Ω → Measure X) (hP : ∀ θ, IsProbabilityMeasure (P θ))
    (G : Kernel X (Fin K → X)) (hG : IsMarkovKernel G)
    (T : (Fin K → X) → X) (hT : Measurable T)
    (hThinIndep : ∀ θ, iIndepFun (fun k (y : Fin K → X) => y k) ((P θ).bind G))
    (hThinRecon : ∀ θ, ∀ᵐ x ∂(P θ), ∀ᵐ y ∂(G x), T y = x) :
    (∃ κ : Kernel X (Fin K → X), IsMarkovKernel κ ∧
        ∀ θ, Measure.map (fun y : Fin K → X => (T y, y)) ((P θ).bind G) =
          Measure.compProd (Measure.map T ((P θ).bind G)) κ) ∧
      (∀ θ, Measure.map (fun y : Fin K → X => (T y, y)) ((P θ).bind G) =
          Measure.compProd (Measure.map T ((P θ).bind G)) G)
:= by
  /- @proof-region region.root.7c0565f322f9 begin -/
  have key : ∀ θ, Measure.map (fun y : Fin K → X => (T y, y)) ((P θ).bind G) =
      Measure.compProd (Measure.map T ((P θ).bind G)) G := by
    intro θ
    exact statopia_math_node_4104113938_66a528d1 (P θ) (hP θ) G hG T hT (hThinRecon θ)
  exact ⟨⟨G, hG, key⟩, key⟩
  /- @proof-region region.root.7c0565f322f9 end -/

end Statlib.Imported
