import ProverJobs.job_paper_b0cf39bbf6c845c9a6b30a5db43f8efa.Vocabulary
import ProverJobs.job_paper_b0cf39bbf6c845c9a6b30a5db43f8efa.Base
import ProverJobs.job_paper_b0cf39bbf6c845c9a6b30a5db43f8efa.ProvedNodes.Node_115472241_0d96c29c_cf3486ff
import ProverJobs.job_paper_b0cf39bbf6c845c9a6b30a5db43f8efa.ProvedNodes.Node_1750728313_95a4e01c_4b30c0f8
import ProverJobs.job_paper_b0cf39bbf6c845c9a6b30a5db43f8efa.ProvedNodes.Node_2140220276_60816db7_96ec9972



open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal MeasureTheory Topology BigOperators
open Statlib.Imported
open Statlib.Imported.DPMModel

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal MeasureTheory Topology BigOperators
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_215231975_e5e8dd5e : ∀ {Θ X : Type*} [MeasurableSpace Θ] [TopologicalSpace Θ] [MeasurableSpace X]
    (M : DPMModel Θ) (μ : Measure X) (k : Θ → X → ℝ)
    (hk_nonneg : ∀ (θ : Θ) (x : X), 0 ≤ k θ x)
    (hk_meas : Measurable (Function.uncurry k))
    (n : ℕ) (x : Fin n → X),
    (∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ),
        ∏ i : Fin n, ENNReal.ofReal (k (ξ.2 i) (x i)) ∂M.latentLaw)
      = ∫⁻ h : X → ℝ≥0∞,
          ∏ i : Fin n, h (x i) ∂(M.latentLaw.map
            (fun ξ : ProbabilityMeasure Θ × (ℕ → Θ) => dpmDensity k ξ.1)) := by
  /- @proof-region region.target-node.session.0a6ab78166d11d35 begin -/
  intro Θ X _instΘ _instTop _instX M μ k hk_nonneg hk_meas n x
  classical
  have hden : Measurable (fun P : ProbabilityMeasure Θ => fun y : X =>
      ∫⁻ θ : Θ, ENNReal.ofReal (k θ y) ∂P.toMeasure) :=
    statopia_math_node_115472241_0d96c29c k hk_meas
  have hdens_meas : Measurable (fun ξ : ProbabilityMeasure Θ × (ℕ → Θ) => dpmDensity k ξ.1) := by
    simpa [dpmDensity] using hden.comp measurable_fst
  have hprod_meas : Measurable (fun h : X → ℝ≥0∞ => ∏ i : Fin n, h (x i)) := by
    simpa using Finset.measurable_prod (Finset.univ : Finset (Fin n))
      (f := fun i (h : X → ℝ≥0∞) => h (x i)) (fun i _ => measurable_pi_apply (x i))
  have hkern : Measurable (fun P : ProbabilityMeasure Θ =>
      (Measure.dirac P).prod (Measure.infinitePi (fun _ : ℕ => P.toMeasure))) :=
    statopia_math_node_1750728313_95a4e01c Θ
  have hae_outer : AEMeasurable (fun a : ℝ => (M.dpLaw a).bind (fun P : ProbabilityMeasure Θ =>
      (Measure.dirac P).prod (Measure.infinitePi (fun _ : ℕ => P.toMeasure)))) M.π := by
    have h1 : AEMeasurable (fun m : Measure (ProbabilityMeasure Θ) =>
        m.bind (fun P : ProbabilityMeasure Θ =>
          (Measure.dirac P).prod (Measure.infinitePi (fun _ : ℕ => P.toMeasure))))
        (M.π.map M.dpLaw) :=
      MeasureTheory.Measure.aemeasurable_bind (m := M.π.map M.dpLaw) hkern.aemeasurable
    exact h1.comp_measurable M.dpLaw_meas
  have hmeas1 : Measurable (fun ξ : ProbabilityMeasure Θ × (ℕ → Θ) =>
      ∏ i : Fin n, ENNReal.ofReal (k (ξ.2 (i : ℕ)) (x i))) := by
    refine Finset.measurable_prod (Finset.univ : Finset (Fin n)) (fun i _ => ?_)
    have hsnd : Measurable (fun ξ : ProbabilityMeasure Θ × (ℕ → Θ) => ξ.2 (i : ℕ)) :=
      (measurable_pi_apply (i : ℕ)).comp measurable_snd
    exact ENNReal.measurable_ofReal.comp (hk_meas.comp (hsnd.prodMk measurable_const))
  have hmeas2 : Measurable (fun ξ : ProbabilityMeasure Θ × (ℕ → Θ) =>
      ∏ i : Fin n, dpmDensity k ξ.1 (x i)) := by
    simpa using Finset.measurable_prod (Finset.univ : Finset (Fin n))
      (f := fun i (ξ : ProbabilityMeasure Θ × (ℕ → Θ)) => dpmDensity k ξ.1 (x i))
      (fun i _ => (measurable_pi_apply (x i)).comp hdens_meas)
  have key : ∀ P : ProbabilityMeasure Θ,
      (∫⁻ θ : ℕ → Θ, (∏ i : Fin n, ENNReal.ofReal (k (θ (i : ℕ)) (x i)))
        ∂Measure.infinitePi (fun _ : ℕ => P.toMeasure))
        = ∏ i : Fin n, dpmDensity k P (x i) := by
    intro P
    simpa [dpmDensity] using statopia_math_node_2140220276_60816db7 k hk_meas n x P
  have key_const : ∀ P : ProbabilityMeasure Θ,
      (∫⁻ _θ : ℕ → Θ, (∏ i : Fin n, dpmDensity k P (x i))
        ∂Measure.infinitePi (fun _ : ℕ => P.toMeasure))
        = ∏ i : Fin n, dpmDensity k P (x i) := by
    intro P
    simp
  have step_bind : ∀ (F : ProbabilityMeasure Θ × (ℕ → Θ) → ℝ≥0∞), Measurable F →
      (∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ), F ξ ∂M.latentLaw)
        = ∫⁻ a, ∫⁻ P : ProbabilityMeasure Θ,
            (∫⁻ θ : ℕ → Θ, F (P, θ)
              ∂Measure.infinitePi (fun _ : ℕ => P.toMeasure)) ∂M.dpLaw a ∂M.π := by
    intro F hF
    refine (MeasureTheory.Measure.lintegral_bind
      (μ := fun a : ℝ => (M.dpLaw a).bind (fun P : ProbabilityMeasure Θ =>
        (Measure.dirac P).prod (Measure.infinitePi (fun _ : ℕ => P.toMeasure))))
      (m := M.π) (f := F) hae_outer hF.aemeasurable).trans ?_
    apply MeasureTheory.lintegral_congr_ae
    filter_upwards with a
    refine (MeasureTheory.Measure.lintegral_bind
      (μ := fun P : ProbabilityMeasure Θ =>
        (Measure.dirac P).prod (Measure.infinitePi (fun _ : ℕ => P.toMeasure)))
      (m := M.dpLaw a) (f := F) hkern.aemeasurable hF.aemeasurable).trans ?_
    apply MeasureTheory.lintegral_congr_ae
    filter_upwards with P
    show (∫⁻ ξ : ProbabilityMeasure Θ × (ℕ → Θ), F ξ
        ∂((Measure.dirac P).prod (Measure.infinitePi (fun _ : ℕ => P.toMeasure))))
      = ∫⁻ θ : ℕ → Θ, F (P, θ) ∂Measure.infinitePi (fun _ : ℕ => P.toMeasure)
    rw [Measure.dirac_prod]
    exact MeasureTheory.lintegral_map hF measurable_prodMk_left
  have hL := step_bind (fun ξ : ProbabilityMeasure Θ × (ℕ → Θ) =>
      ∏ i : Fin n, ENNReal.ofReal (k (ξ.2 (i : ℕ)) (x i))) hmeas1
  have hR := step_bind (fun ξ : ProbabilityMeasure Θ × (ℕ → Θ) =>
      ∏ i : Fin n, dpmDensity k ξ.1 (x i)) hmeas2
  have hkey :
      (∫⁻ a, ∫⁻ P : ProbabilityMeasure Θ,
          (∫⁻ θ : ℕ → Θ, (∏ i : Fin n, ENNReal.ofReal (k (θ (i : ℕ)) (x i)))
            ∂Measure.infinitePi (fun _ : ℕ => P.toMeasure)) ∂M.dpLaw a ∂M.π)
        = (∫⁻ a, ∫⁻ P : ProbabilityMeasure Θ,
          (∫⁻ θ : ℕ → Θ, (∏ i : Fin n, dpmDensity k P (x i))
            ∂Measure.infinitePi (fun _ : ℕ => P.toMeasure)) ∂M.dpLaw a ∂M.π) := by
    apply MeasureTheory.lintegral_congr_ae
    filter_upwards with a
    apply MeasureTheory.lintegral_congr_ae
    filter_upwards with P
    exact (key P).trans (key_const P).symm
  rw [MeasureTheory.lintegral_map hprod_meas hdens_meas]
  exact (hL.trans hkey).trans hR.symm
  /- @proof-region region.target-node.session.0a6ab78166d11d35 end -/

end Statlib.Imported
