import ProverJobs.paper_fresh_20261028t224543381z_hmc_22.Vocabulary
import ProverJobs.paper_fresh_20261028t224543381z_hmc_22.Base

namespace PaperProofTasks.paper_fresh_20261028t224543381z_hmc_22

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
open _root_.PaperProofTasks.paper_fresh_20261028t224543381z_hmc_22.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
namespace Statlib.Imported
open _root_.Statlib

set_option autoImplicit false in
theorem statopia_math_node_60244864_4d03ea71 : ∀ (d : ℕ) (hd : 0 < d)
    (U : HMCState d → ℝ) (hU_diff : Differentiable ℝ U)
    (ε : ℝ) (hε : 0 < ε) (𝔏 : Measure ℕ) [IsProbabilityMeasure 𝔏],
    ((∀ (x : HMCState d), ∀ A : Set (HMCState d), MeasurableSet A →
        hmcKernel U ε 𝔏 x A
          = ∫⁻ (L : ℕ),
              (((gaussianMomentum d).prod (volume.restrict (Set.Icc (0 : ℝ) 1))).map
                (fun w : HMCState d × ℝ => hmcStep U ε L x w.1 w.2)) A ∂𝔏)
      ∧ (∀ (x : HMCState d), IsProbabilityMeasure (hmcKernel U ε 𝔏 x))
      ∧ (∀ A : Set (HMCState d), MeasurableSet A →
          Measurable fun y : HMCState d => hmcKernel U ε 𝔏 y A)) := by
  /- @proof-region region.target-node.session.afb866fd7da31268 begin -/
  intro d hd U hU_diff ε hε 𝔏 h𝔏
  classical
  haveI h𝔏' : IsProbabilityMeasure 𝔏 := h𝔏
  have hgrad : Measurable (gradient U) := by
    have h1 : Measurable (fun x : HMCState d =>
        (InnerProductSpace.toDual ℝ (HMCState d)).symm (fderiv ℝ U x)) :=
      (((InnerProductSpace.toDual ℝ (HMCState d)).symm).continuous).measurable.comp
        (measurable_fderiv (𝕜 := ℝ) U)
    simpa [gradient] using h1
  have hham : Measurable (hamiltonian U) := by
    have hEq : hamiltonian U = fun z : HMCState d × HMCState d =>
        U z.1 + (1 / 2) * ‖z.2‖ ^ 2 := rfl
    rw [hEq]
    exact (hU_diff.continuous.measurable.comp measurable_fst).add
      ((continuous_const.mul ((continuous_norm.comp continuous_snd).pow 2))).measurable
  have hstep : Measurable (leapfrogStep U ε) := by
    have hpHalf : Measurable (fun z : HMCState d × HMCState d =>
        z.2 - (ε / 2) • gradient U z.1) :=
      measurable_snd.sub (measurable_const.smul (hgrad.comp measurable_fst))
    have hx' : Measurable (fun z : HMCState d × HMCState d =>
        z.1 + ε • (z.2 - (ε / 2) • gradient U z.1)) :=
      measurable_fst.add (measurable_const.smul hpHalf)
    have hp' : Measurable (fun z : HMCState d × HMCState d =>
        (z.2 - (ε / 2) • gradient U z.1) -
          (ε / 2) • gradient U (z.1 + ε • (z.2 - (ε / 2) • gradient U z.1))) :=
      hpHalf.sub (measurable_const.smul (hgrad.comp hx'))
    unfold leapfrogStep
    exact hx'.prod hp'
  have hiterL : ∀ L : ℕ, Measurable ((leapfrogStep U ε)^[L]) := by
    intro L
    induction L with
    | zero => exact measurable_id
    | succ n ih => exact ih.comp hstep
  have hsec : Measurable (fun v : ℕ × (HMCState d × HMCState d) =>
      (leapfrogStep U ε)^[v.1] v.2) := by
    intro s hs
    have hset : (fun v : ℕ × (HMCState d × HMCState d) =>
        (leapfrogStep U ε)^[v.1] v.2) ⁻¹' s
        = ⋃ L, ({L} : Set ℕ) ×ˢ ((leapfrogStep U ε)^[L] ⁻¹' s) := by
      ext v
      obtain ⟨L, z⟩ := v
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff]
      constructor
      · intro h
        exact ⟨L, rfl, h⟩
      · rintro ⟨L', rfl, h⟩
        exact h
    rw [hset]
    exact MeasurableSet.iUnion fun L => (measurableSet_singleton L).prod (hiterL L hs)
  have hT : Measurable (fun v : HMCState d × ℕ × HMCState d × ℝ =>
      (v.2.1, (v.1, v.2.2.1))) := by
    have h1 : Measurable (fun v : HMCState d × ℕ × HMCState d × ℝ => v.2.1) :=
      measurable_fst.comp measurable_snd
    have h2 : Measurable (fun v : HMCState d × ℕ × HMCState d × ℝ => v.1) := measurable_fst
    have h3 : Measurable (fun v : HMCState d × ℕ × HMCState d × ℝ => v.2.2.1) :=
      measurable_fst.comp (measurable_snd.comp measurable_snd)
    exact Measurable.prod h1 (Measurable.prod h2 h3)
  have hflow : Measurable (fun v : HMCState d × ℕ × HMCState d × ℝ =>
      leapfrogFlow U ε v.2.1 (v.1, v.2.2.1)) := hsec.comp hT
  have harg : Measurable (fun v : HMCState d × ℕ × HMCState d × ℝ => (v.1, v.2.2.1)) := by
    have h2 : Measurable (fun v : HMCState d × ℕ × HMCState d × ℝ => v.1) := measurable_fst
    have h3 : Measurable (fun v : HMCState d × ℕ × HMCState d × ℝ => v.2.2.1) :=
      measurable_fst.comp (measurable_snd.comp measurable_snd)
    exact Measurable.prod h2 h3
  have hcond : MeasurableSet {v : HMCState d × ℕ × HMCState d × ℝ |
      Real.log v.2.2.2 < hamiltonian U (v.1, v.2.2.1) -
        hamiltonian U (leapfrogFlow U ε v.2.1 (v.1, v.2.2.1))} := by
    apply measurableSet_lt
    · exact Real.measurable_log.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
    · exact (hham.comp harg).sub (hham.comp hflow)
  have hcore : Measurable (fun v : HMCState d × ℕ × HMCState d × ℝ =>
      hmcStep U ε v.2.1 v.1 v.2.2.1 v.2.2.2) := by
    have hfun : (fun v : HMCState d × ℕ × HMCState d × ℝ =>
        hmcStep U ε v.2.1 v.1 v.2.2.1 v.2.2.2)
        = fun v => if Real.log v.2.2.2 < hamiltonian U (v.1, v.2.2.1) -
              hamiltonian U (leapfrogFlow U ε v.2.1 (v.1, v.2.2.1))
            then (leapfrogFlow U ε v.2.1 (v.1, v.2.2.1)).1 else v.1 := by
      funext v
      simp only [hmcStep]
    rw [hfun]
    exact Measurable.ite hcond (measurable_fst.comp hflow) measurable_fst
  haveI hgauss : IsProbabilityMeasure (gaussianMomentum d) := by
    haveI : IsProbabilityMeasure (Measure.pi (fun _ : Fin d => gaussianReal (0 : ℝ) 1)) :=
      MeasureTheory.Measure.pi.instIsProbabilityMeasure _
    have hae : AEMeasurable ((EuclideanSpace.equiv (Fin d) ℝ).symm)
        (Measure.pi (fun _ : Fin d => gaussianReal (0 : ℝ) 1)) :=
      (((EuclideanSpace.equiv (Fin d) ℝ).symm).continuous).measurable.aemeasurable
    exact Measure.isProbabilityMeasure_map hae
  haveI hvol : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    ⟨by
      rw [Measure.restrict_apply_univ, Real.volume_Icc]
      norm_num⟩
  have hΦx : ∀ x : HMCState d,
      Measurable (fun w : (ℕ × HMCState d) × ℝ => hmcStep U ε w.1.1 x w.1.2 w.2) := by
    intro x
    have hc : Measurable (fun _ : (ℕ × HMCState d) × ℝ => x) := measurable_const
    have h1 : Measurable (fun w : (ℕ × HMCState d) × ℝ => w.1.1) :=
      measurable_fst.comp measurable_fst
    have h2 : Measurable (fun w : (ℕ × HMCState d) × ℝ => w.1.2) :=
      measurable_snd.comp measurable_fst
    have h3 : Measurable (fun w : (ℕ × HMCState d) × ℝ => w.2) := measurable_snd
    exact hcore.comp (f := fun w : (ℕ × HMCState d) × ℝ => (x, w.1.1, w.1.2, w.2))
      (Measurable.prod hc (Measurable.prod h1 (Measurable.prod h2 h3)))
  have key1 : ∀ (x : HMCState d) (A : Set (HMCState d)), MeasurableSet A →
      hmcKernel U ε 𝔏 x A
        = ∫⁻ (L : ℕ), (((gaussianMomentum d).prod (volume.restrict (Set.Icc (0 : ℝ) 1))).map
            (fun w : HMCState d × ℝ => hmcStep U ε L x w.1 w.2)) A ∂𝔏 := by
    intro x A hA
    have hpre : MeasurableSet ((fun w : (ℕ × HMCState d) × ℝ =>
        hmcStep U ε w.1.1 x w.1.2 w.2) ⁻¹' A) :=
      hΦx x hA
    have hf : Measurable (fun a : ℕ × HMCState d =>
        (volume.restrict (Set.Icc (0 : ℝ) 1)) (Prod.mk a ⁻¹' ((fun w : (ℕ × HMCState d) × ℝ =>
          hmcStep U ε w.1.1 x w.1.2 w.2) ⁻¹' A))) :=
      measurable_measure_prodMk_left hpre
    have hsecL : ∀ L : ℕ, Measurable (fun w : HMCState d × ℝ => hmcStep U ε L x w.1 w.2) := by
      intro L
      have hcx : Measurable (fun _ : HMCState d × ℝ => x) := measurable_const
      have hcL : Measurable (fun _ : HMCState d × ℝ => L) := measurable_const
      have hp : Measurable (fun w : HMCState d × ℝ => w.1) := measurable_fst
      have hu : Measurable (fun w : HMCState d × ℝ => w.2) := measurable_snd
      exact hcore.comp (f := fun w : HMCState d × ℝ => (x, L, w.1, w.2))
        (Measurable.prod hcx (Measurable.prod hcL (Measurable.prod hp hu)))
    have hL_eq : ∀ L : ℕ, ∫⁻ (p : HMCState d),
          (volume.restrict (Set.Icc (0 : ℝ) 1)) (Prod.mk (L, p) ⁻¹'
            ((fun w : (ℕ × HMCState d) × ℝ => hmcStep U ε w.1.1 x w.1.2 w.2) ⁻¹' A))
          ∂(gaussianMomentum d)
        = (((gaussianMomentum d).prod (volume.restrict (Set.Icc (0 : ℝ) 1))).map
            (fun w : HMCState d × ℝ => hmcStep U ε L x w.1 w.2)) A := by
      intro L
      have hpreL : MeasurableSet ((fun w : HMCState d × ℝ => hmcStep U ε L x w.1 w.2) ⁻¹' A) :=
        hsecL L hA
      calc ∫⁻ (p : HMCState d),
            (volume.restrict (Set.Icc (0 : ℝ) 1)) (Prod.mk (L, p) ⁻¹'
              ((fun w : (ℕ × HMCState d) × ℝ => hmcStep U ε w.1.1 x w.1.2 w.2) ⁻¹' A))
            ∂(gaussianMomentum d)
          = ∫⁻ (p : HMCState d),
              (volume.restrict (Set.Icc (0 : ℝ) 1)) (Prod.mk p ⁻¹'
                ((fun w : HMCState d × ℝ => hmcStep U ε L x w.1 w.2) ⁻¹' A))
              ∂(gaussianMomentum d) := rfl
        _ = ((gaussianMomentum d).prod (volume.restrict (Set.Icc (0 : ℝ) 1)))
              ((fun w : HMCState d × ℝ => hmcStep U ε L x w.1 w.2) ⁻¹' A) :=
            (Measure.prod_apply hpreL).symm
        _ = (((gaussianMomentum d).prod (volume.restrict (Set.Icc (0 : ℝ) 1))).map
              (fun w : HMCState d × ℝ => hmcStep U ε L x w.1 w.2)) A :=
            (Measure.map_apply (hsecL L) hA).symm
    have hFub : ∫⁻ (a : ℕ × HMCState d),
          (volume.restrict (Set.Icc (0 : ℝ) 1)) (Prod.mk a ⁻¹' ((fun w : (ℕ × HMCState d) × ℝ =>
            hmcStep U ε w.1.1 x w.1.2 w.2) ⁻¹' A)) ∂(𝔏.prod (gaussianMomentum d))
        = ∫⁻ (L : ℕ), ∫⁻ (p : HMCState d),
            (volume.restrict (Set.Icc (0 : ℝ) 1)) (Prod.mk (L, p) ⁻¹'
              ((fun w : (ℕ × HMCState d) × ℝ => hmcStep U ε w.1.1 x w.1.2 w.2) ⁻¹' A))
            ∂(gaussianMomentum d) ∂𝔏 :=
      MeasureTheory.lintegral_prod _ hf.aemeasurable
    rw [show hmcKernel U ε 𝔏 x A
        = ((𝔏.prod (gaussianMomentum d)).prod (volume.restrict (Set.Icc (0 : ℝ) 1)))
            ((fun w : (ℕ × HMCState d) × ℝ => hmcStep U ε w.1.1 x w.1.2 w.2) ⁻¹' A)
        from Measure.map_apply (hΦx x) hA]
    rw [Measure.prod_apply hpre, hFub]
    simp only [hL_eq]
  have hprob : ∀ x : HMCState d, IsProbabilityMeasure (hmcKernel U ε 𝔏 x) := by
    intro x
    have h := Measure.isProbabilityMeasure_map
      (μ := (𝔏.prod (gaussianMomentum d)).prod (volume.restrict (Set.Icc (0 : ℝ) 1)))
      (f := fun w : (ℕ × HMCState d) × ℝ => hmcStep U ε w.1.1 x w.1.2 w.2)
      ((hΦx x).aemeasurable)
    exact h
  have key3 : ∀ A : Set (HMCState d), MeasurableSet A →
      Measurable fun y : HMCState d => hmcKernel U ε 𝔏 y A := by
    intro A hA
    let S : Set (HMCState d × ((ℕ × HMCState d) × ℝ)) :=
      {p | hmcStep U ε p.2.1.1 p.1 p.2.1.2 p.2.2 ∈ A}
    have hj : Measurable (fun v : HMCState d × ((ℕ × HMCState d) × ℝ) =>
        hmcStep U ε v.2.1.1 v.1 v.2.1.2 v.2.2) := by
      have h1 : Measurable (fun v : HMCState d × ((ℕ × HMCState d) × ℝ) => v.1) :=
        measurable_fst
      have h2 : Measurable (fun v : HMCState d × ((ℕ × HMCState d) × ℝ) => v.2.1.1) :=
        measurable_fst.comp (measurable_fst.comp measurable_snd)
      have h3 : Measurable (fun v : HMCState d × ((ℕ × HMCState d) × ℝ) => v.2.1.2) :=
        measurable_snd.comp (measurable_fst.comp measurable_snd)
      have h4 : Measurable (fun v : HMCState d × ((ℕ × HMCState d) × ℝ) => v.2.2) :=
        measurable_snd.comp measurable_snd
      exact hcore.comp (f := fun v : HMCState d × ((ℕ × HMCState d) × ℝ) =>
          (v.1, v.2.1.1, v.2.1.2, v.2.2))
        (Measurable.prod h1 (Measurable.prod h2 (Measurable.prod h3 h4)))
    have hS : MeasurableSet S := hj hA
    have hmeas : Measurable (fun y : HMCState d =>
        ((𝔏.prod (gaussianMomentum d)).prod (volume.restrict (Set.Icc (0 : ℝ) 1)))
          (Prod.mk y ⁻¹' S)) := measurable_measure_prodMk_left hS
    have hfun : (fun y : HMCState d =>
        ((𝔏.prod (gaussianMomentum d)).prod (volume.restrict (Set.Icc (0 : ℝ) 1)))
          (Prod.mk y ⁻¹' S)) = fun y => hmcKernel U ε 𝔏 y A := by
      funext y
      exact (Measure.map_apply (hΦx y) hA).symm
    rw [hfun] at hmeas
    exact hmeas
  exact ⟨key1, hprob, key3⟩
  /- @proof-region region.target-node.session.afb866fd7da31268 end -/

end Statlib.Imported

end

