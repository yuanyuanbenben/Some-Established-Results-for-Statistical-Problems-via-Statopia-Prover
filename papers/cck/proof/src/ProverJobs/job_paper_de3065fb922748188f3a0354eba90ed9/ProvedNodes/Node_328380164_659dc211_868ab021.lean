import Statlib.StatFoundation.Statistics.Asymptotic.ScoreCLT
import Statlib.StatFoundation.Convergence.Resampling.GaussianMaxComparison
import Statlib.StatFoundation.Convergence.AnalysisTools.GaussianMaxAnticoncentration
import Statlib.StatFoundation.Statistics.Asymptotic.LAN
import Statlib.StatFoundation.Convergence.AnalysisTools.SmoothMax
import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.Vocabulary
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.Base

namespace PaperProofTasks.job_paper_de3065fb922748188f3a0354eba90ed9

open _root_.PaperProofTasks.job_paper_de3065fb922748188f3a0354eba90ed9.Statlib.Imported
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

set_option autoImplicit false in
theorem statopia_math_node_328380164_659dc211 : ∀ {ι : Type*} [Fintype ι]
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (R : Ω → (ι → ℝ)) (f : ℝ → (ι → ℝ))
    (hX : Measurable X)
    (hR : Measurable R)
    (hf : Measurable (fun p : ℝ × (ι → ℝ) => (p.1, f p.1 + p.2)))
    (hindep : Measure.map (fun ω => (X ω, R ω)) P
      = (Measure.map X P).prod (Measure.map R P)),
    ∀ᵐ z ∂(Measure.map X P),
      (Measure.map (fun ω => (X ω, f (X ω) + R ω)) P).condKernel z
        = Measure.map (fun r : ι → ℝ => f z + r) (Measure.map R P) := by
  /- @proof-region region.target-node.session.3c804ef5276a49a9 begin -/
  intro ι _ Ω _ P _ X R f hX hR hf hindep
  have hpair : Measurable (fun ω => (X ω, R ω)) := Measurable.prodMk hX hR
  have hgm : Measurable (fun p : ℝ × (ι → ℝ) => f p.1 + p.2) := measurable_snd.comp hf
  have hfm : Measurable f := by
    have hcomp : Measurable ((fun p : ℝ × (ι → ℝ) => f p.1 + p.2) ∘ fun a : ℝ => (a, 0)) :=
      hgm.comp (Measurable.prodMk measurable_id
        (measurable_const : Measurable fun _ : ℝ => (0 : ι → ℝ)))
    have hfun : ((fun p : ℝ × (ι → ℝ) => f p.1 + p.2) ∘ fun a : ℝ => (a, 0)) = f := by
      funext z
      exact add_zero (f z)
    rwa [hfun] at hcomp
  have hadd : Measurable (fun p : (ι → ℝ) × (ι → ℝ) => p.1 + p.2) :=
    measurable_fst.add measurable_snd
  set κ : Kernel ℝ (ι → ℝ) :=
    Kernel.map (Kernel.prod (Kernel.deterministic f hfm) (Kernel.const ℝ (Measure.map R P)))
      (fun p : (ι → ℝ) × (ι → ℝ) => p.1 + p.2) with hκ
  have hκval : ∀ z : ℝ, κ z = Measure.map (fun r : ι → ℝ => f z + r) (Measure.map R P) := by
    intro z
    rw [hκ]
    rw [Kernel.map_apply (Kernel.prod (Kernel.deterministic f hfm)
      (Kernel.const ℝ (Measure.map R P))) hadd z]
    rw [Kernel.prod_apply]
    rw [Kernel.deterministic_apply, Kernel.const_apply]
    rw [Measure.dirac_prod]
    have hmk : Measurable (Prod.mk (f z) : (ι → ℝ) → (ι → ℝ) × (ι → ℝ)) :=
      measurable_prodMk_left
    have hfunz : ((fun p : (ι → ℝ) × (ι → ℝ) => p.1 + p.2) ∘ Prod.mk (f z))
        = fun r : ι → ℝ => f z + r := rfl
    rw [Measure.map_map hadd hmk, hfunz]
  have hmap1 : Measure.map (fun ω => (X ω, f (X ω) + R ω)) P
      = Measure.map (fun p : ℝ × (ι → ℝ) => (p.1, f p.1 + p.2))
          (Measure.map (fun ω => (X ω, R ω)) P) := by
    have hfun : ((fun p : ℝ × (ι → ℝ) => (p.1, f p.1 + p.2)) ∘ fun ω => (X ω, R ω))
        = fun ω => (X ω, f (X ω) + R ω) := rfl
    rw [Measure.map_map hf hpair, hfun]
  have hpush : Measure.map (fun p : ℝ × (ι → ℝ) => (p.1, f p.1 + p.2))
        (Measure.compProd (Measure.map X P) (Kernel.const ℝ (Measure.map R P)))
      = Measure.compProd (Measure.map X P) κ := by
    ext s hs
    rw [Measure.map_apply hf hs]
    rw [Measure.compProd_apply (hs.preimage hf)]
    rw [Measure.compProd_apply hs]
    refine lintegral_congr fun z => ?_
    rw [Kernel.const_apply, hκval z]
    have hmk : Measurable (fun r : ι → ℝ => (z, r)) :=
      Measurable.prodMk (measurable_const : Measurable fun _ : ι → ℝ => z) measurable_id
    have hmz : Measurable (fun r : ι → ℝ => f z + r) := hgm.comp hmk
    rw [Measure.map_apply hmz (hs.preimage hmk)]
    have hset : (Prod.mk z ⁻¹' ((fun p : ℝ × (ι → ℝ) => (p.1, f p.1 + p.2)) ⁻¹' s))
        = ((fun r : ι → ℝ => f z + r) ⁻¹' ((fun r : ι → ℝ => (z, r)) ⁻¹' s)) := by
      ext x
      simp
    rw [hset]
  have hρκ : Measure.map (fun ω => (X ω, f (X ω) + R ω)) P
      = Measure.compProd (Measure.map X P) κ := by
    rw [hmap1, hindep, ← Measure.compProd_const (α := ℝ)]
    exact hpush
  have hfst : (Measure.map (fun ω => (X ω, f (X ω) + R ω)) P).fst = Measure.map X P := by
    have hW : Measurable (fun ω => (X ω, f (X ω) + R ω)) := hf.comp hpair
    have hfun : (Prod.fst ∘ fun ω => (X ω, f (X ω) + R ω)) = X := rfl
    show Measure.map Prod.fst (Measure.map (fun ω => (X ω, f (X ω) + R ω)) P)
      = Measure.map X P
    rw [Measure.map_map measurable_fst hW, hfun]
  have hcomp : Measure.map (fun ω => (X ω, f (X ω) + R ω)) P
      = Measure.compProd ((Measure.map (fun ω => (X ω, f (X ω) + R ω)) P).fst) κ := by
    rw [hfst]
    exact hρκ
  have hmain := eq_condKernel_of_measure_eq_compProd
    (ρ := Measure.map (fun ω => (X ω, f (X ω) + R ω)) P) κ hcomp
  rw [hfst] at hmain
  filter_upwards [hmain] with z hz
  rw [← hz]
  exact hκval z
  /- @proof-region region.target-node.session.3c804ef5276a49a9 end -/

end Statlib.Imported

