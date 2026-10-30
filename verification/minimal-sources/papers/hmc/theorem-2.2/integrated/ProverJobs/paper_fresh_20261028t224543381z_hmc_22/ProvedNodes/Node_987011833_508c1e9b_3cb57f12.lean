import ProverJobs.paper_fresh_20261028t224543381z_hmc_22.Vocabulary
import ProverJobs.paper_fresh_20261028t224543381z_hmc_22.Base
import ProverJobs.paper_fresh_20261028t224543381z_hmc_22.ProvedNodes.Node_2058725449_c65439c0_6cbfcedb
import ProverJobs.paper_fresh_20261028t224543381z_hmc_22.ProvedNodes.Node_3566158159_28810915_a20de882

namespace PaperProofTasks.paper_fresh_20261028t224543381z_hmc_22

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
open _root_.PaperProofTasks.paper_fresh_20261028t224543381z_hmc_22.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
namespace Statlib.Imported


set_option autoImplicit false in
theorem statopia_math_node_987011833_508c1e9b : ∀ (d : ℕ) (hd : 0 < d)
    (U : HMCState d → ℝ) (hU_diff : Differentiable ℝ U)
    (eps : ℝ) (heps : 0 < eps)
    (pi : Measure (HMCState d)) [IsProbabilityMeasure pi]
    (hpi : ∃ c : ℝ, 0 < c ∧
      pi = volume.withDensity (fun x => ENNReal.ofReal (c * Real.exp (-(U x)))))
    (L : ℕ) (A : Set (HMCState d)) (hA : MeasurableSet A),
    ∫⁻ x, hmcKernel U eps (Measure.dirac L) x A ∂pi = pi A := by
  /- @proof-region region.target-node.session.0a12c00dbefd2ff1 begin -/
  intro d hd U hU_diff ε hε π hprob hπ L A hA
  obtain ⟨c, hc, hπeq⟩ := hπ
  set ρ : Measure (HMCState d) :=
    volume.withDensity (fun x => ENNReal.ofReal (Real.exp (- U x))) with hρ
  have hU_cont : Continuous U := hU_diff.continuous
  have hU_meas : Measurable U := hU_cont.measurable
  have hgrad : Measurable (gradient U) := by
    have hfd : Measurable (fderiv ℝ U) := measurable_fderiv ℝ U
    have hcont := (InnerProductSpace.toDual ℝ (HMCState d)).symm.continuous.measurable
    simpa [gradient] using hcont.comp hfd
  have hstep : Measurable (fun z : HMCState d × HMCState d => leapfrogStep U ε z) := by
    unfold leapfrogStep
    measurability
  have hflow : Measurable (fun z : HMCState d × HMCState d => leapfrogFlow U ε L z) := by
    simpa [leapfrogFlow] using hstep.iterate L
  have hhmc : Measurable (fun w : (HMCState d × HMCState d) × ℝ =>
      hmcStep U ε L w.1.1 w.1.2 w.2) := by
    have hflow' : Measurable (fun w : (HMCState d × HMCState d) × ℝ =>
        leapfrogFlow U ε L w.1) := hflow.comp measurable_fst
    have hH : Measurable (fun w : (HMCState d × HMCState d) × ℝ => hamiltonian U w.1) := by
      unfold hamiltonian
      measurability
    have hH' : Measurable (fun w : (HMCState d × HMCState d) × ℝ =>
        hamiltonian U (leapfrogFlow U ε L w.1)) := by
      unfold hamiltonian
      measurability
    have hlog : Measurable (fun w : (HMCState d × HMCState d) × ℝ => Real.log w.2) :=
      Real.measurable_log.comp measurable_snd
    have hcond : MeasurableSet {w : (HMCState d × HMCState d) × ℝ |
        Real.log w.2 < hamiltonian U w.1 - hamiltonian U (leapfrogFlow U ε L w.1)} :=
      measurableSet_lt hlog (hH.sub hH')
    have hz : Measurable (fun w : (HMCState d × HMCState d) × ℝ =>
        (leapfrogFlow U ε L w.1).1) := measurable_fst.comp hflow'
    have hx : Measurable (fun w : (HMCState d × HMCState d) × ℝ => w.1.1) :=
      measurable_fst.comp measurable_fst
    unfold hmcStep
    simpa using (Measurable.ite hcond hz hx)
  have hν : ((volume.prod volume : Measure (HMCState d × HMCState d)).withDensity
        (fun z => ENNReal.ofReal (Real.exp (-(hamiltonian U z)))))
      = ρ.prod ((volume : Measure (HMCState d)).withDensity
          (fun p => ENNReal.ofReal (Real.exp (-(1/2) * ‖p‖ ^ 2)))) := by
    rw [hρ, prod_withDensity (by measurability) (by measurability)]
    congr 1
    funext z
    show ENNReal.ofReal (Real.exp (-(hamiltonian U z)))
      = ENNReal.ofReal (Real.exp (- U z.1)) * ENNReal.ofReal (Real.exp (-(1/2) * ‖z.2‖ ^ 2))
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    have harg : -(hamiltonian U z) = -U z.1 + -(1/2) * ‖z.2‖ ^ 2 := by
      unfold hamiltonian
      ring
    rw [harg]
  have hstepN : Measurable (fun v : ℕ × (HMCState d × HMCState d) =>
      leapfrogFlow U ε v.1 v.2) := by
    intro t ht
    have hset : (fun v : ℕ × (HMCState d × HMCState d) => leapfrogFlow U ε v.1 v.2) ⁻¹' t
        = ⋃ n : ℕ, ({n} : Set ℕ) ×ˢ (leapfrogFlow U ε n ⁻¹' t) := by
      ext v
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff]
      constructor
      · rintro hv
        exact ⟨v.1, rfl, hv⟩
      · rintro ⟨n, rfl, hv⟩
        exact hv
    rw [hset]
    exact MeasurableSet.iUnion fun n => (MeasurableSet.singleton n).prod (hstep.iterate n ht)
  have hWmeas : ∀ x : HMCState d, Measurable (fun v : (ℕ × HMCState d) × ℝ =>
      hmcStep U ε v.1.1 x v.1.2 v.2) := by
    intro x
    have hι : Measurable (fun v : (ℕ × HMCState d) × ℝ => (v.1.1, (x, v.1.2))) := by
      measurability
    have hφ : Measurable (fun v : (ℕ × HMCState d) × ℝ => leapfrogFlow U ε v.1.1 (x, v.1.2)) :=
      hstepN.comp hι
    have hH1 : Measurable (fun v : (ℕ × HMCState d) × ℝ => hamiltonian U (x, v.1.2)) := by
      unfold hamiltonian
      measurability
    have hH2 : Measurable (fun v : (ℕ × HMCState d) × ℝ =>
        hamiltonian U (leapfrogFlow U ε v.1.1 (x, v.1.2))) := by
      unfold hamiltonian
      measurability
    have hlog : Measurable (fun v : (ℕ × HMCState d) × ℝ => Real.log v.2) :=
      Real.measurable_log.comp measurable_snd
    have hcond : MeasurableSet {v : (ℕ × HMCState d) × ℝ |
        Real.log v.2 < hamiltonian U (x, v.1.2) -
          hamiltonian U (leapfrogFlow U ε v.1.1 (x, v.1.2))} :=
      measurableSet_lt hlog (hH1.sub hH2)
    have hz : Measurable (fun v : (ℕ × HMCState d) × ℝ =>
        (leapfrogFlow U ε v.1.1 (x, v.1.2)).1) := measurable_fst.comp hφ
    have hx : Measurable (fun _ : (ℕ × HMCState d) × ℝ => x) := measurable_const
    unfold hmcStep
    simpa using (Measurable.ite hcond hz hx)
  haveI hgm_prob : IsProbabilityMeasure (gaussianMomentum d) := by
    unfold gaussianMomentum
    exact Measure.isProbabilityMeasure_map
      (EuclideanSpace.equiv (Fin d) ℝ).symm.continuous.measurable.aemeasurable
  have hcore : ∀ B : Set (HMCState d), MeasurableSet B →
      ∫⁻ x, hmcKernel U ε (Measure.dirac L) x B ∂ρ = ρ B := by
    intro B hB
    have hW2b : ∀ x : HMCState d, Measurable (fun w : HMCState d × ℝ =>
        hmcStep U ε L x w.1 w.2) := by
      intro x
      have hc : Measurable (fun w : HMCState d × ℝ => ((L, w.1), w.2)) := by measurability
      exact (hWmeas x).comp hc
    have hprobG : (ρ.prod (gaussianMomentum d)) (B ×ˢ (Set.univ : Set (HMCState d)))
        = ρ B := by
      rw [Measure.prod_apply_symm (hB.prod MeasurableSet.univ)]
      have hsec : ∀ p : HMCState d,
          ρ ((fun x : HMCState d => (x, p)) ⁻¹' (B ×ˢ (Set.univ : Set (HMCState d)))) = ρ B := by
        intro p
        congr 1
        ext x
        simp
      simp only [hsec, lintegral_const]
      simp
    have hdirac : ∀ x : HMCState d, hmcKernel U ε (Measure.dirac L) x B
        = ∫⁻ p, (Measure.restrict volume (Set.Icc (0 : ℝ) 1))
            {u : ℝ | hmcStep U ε L x p u ∈ B} ∂(gaussianMomentum d) := by
      intro x
      have hW : Measurable (fun v : (ℕ × HMCState d) × ℝ => hmcStep U ε v.1.1 x v.1.2 v.2) :=
        hWmeas x
      have hW2 : Measurable (fun w : HMCState d × ℝ => hmcStep U ε L x w.1 w.2) := by
        have hc : Measurable (fun w : HMCState d × ℝ => ((L, w.1), w.2)) := by measurability
        exact hW.comp hc
      have hpmap : Measurable (Prod.map (fun p : HMCState d => (L, p)) (id : ℝ → ℝ)) := by
        have h1 : Measurable (fun w : HMCState d × ℝ => ((L, w.1), w.2)) := by measurability
        simpa [Prod.map] using h1
      have hκ : (Measure.restrict volume (Set.Icc (0 : ℝ) 1) : Measure ℝ)
          = Measure.map id (Measure.restrict volume (Set.Icc (0 : ℝ) 1)) :=
        (Measure.map_id).symm
      conv_lhs =>
        rw [hmcKernel]
        rw [Measure.map_apply hW hB]
        rw [Measure.dirac_prod]
        rw [hκ]
        rw [Measure.map_prod_map (gaussianMomentum d)
          (Measure.restrict volume (Set.Icc (0 : ℝ) 1)) (by measurability) measurable_id]
        rw [Measure.map_apply hpmap (hW hB)]
        rw [show (Prod.map (fun p : HMCState d => (L, p)) (id : ℝ → ℝ)) ⁻¹'
              ((fun v : (ℕ × HMCState d) × ℝ => hmcStep U ε v.1.1 x v.1.2 v.2) ⁻¹' B)
            = (fun w : HMCState d × ℝ => hmcStep U ε L x w.1 w.2) ⁻¹' B from by
          ext w
          simp [Prod.map]]
        rw [Measure.prod_apply (hW2 hB)]
      refine lintegral_congr fun p => ?_
      rw [show Prod.mk p ⁻¹' ((fun w : HMCState d × ℝ => hmcStep U ε L x w.1 w.2) ⁻¹' B)
          = {u : ℝ | hmcStep U ε L x p u ∈ B} from by
        ext u
        simp]
    have hrest : ∫⁻ x, (∫⁻ p, (Measure.restrict volume (Set.Icc (0 : ℝ) 1))
            {u : ℝ | hmcStep U ε L x p u ∈ B} ∂(gaussianMomentum d)) ∂ρ = ρ B := by
      have hg := statopia_math_node_2058725449_c65439c0 d
      simp only [] at hg
      obtain ⟨hc0, hct, hcm⟩ := hg
      have hRHS : (ρ.prod ((volume : Measure (HMCState d)).withDensity
            (fun p : HMCState d => ENNReal.ofReal (Real.exp (-(1/2) * ‖p‖ ^ 2)))))
            (B ×ˢ (Set.univ : Set (HMCState d)))
          = ρ B * ((volume : Measure (HMCState d)).withDensity
              (fun p : HMCState d => ENNReal.ofReal (Real.exp (-(1/2) * ‖p‖ ^ 2)))) Set.univ := by
        rw [Measure.prod_apply_symm (hB.prod MeasurableSet.univ)]
        have hsec : ∀ p : HMCState d,
            ρ ((fun x : HMCState d => (x, p)) ⁻¹' (B ×ˢ (Set.univ : Set (HMCState d)))) = ρ B := by
          intro p
          congr 1
          ext x
          simp
        simp only [hsec, lintegral_const]
      have hstep_eq : ∀ z : HMCState d × HMCState d,
          (Measure.restrict volume (Set.Icc (0 : ℝ) 1))
            {u : ℝ | (if Real.log u < hamiltonian U z - hamiltonian U (leapfrogFlow U ε L z)
                      then leapfrogFlow U ε L z else z) ∈ B ×ˢ (Set.univ : Set (HMCState d))}
          = (Measure.restrict volume (Set.Icc (0 : ℝ) 1))
              {u : ℝ | hmcStep U ε L z.1 z.2 u ∈ B} := by
        intro z
        congr 1
        ext u
        have hz : ((z.1, z.2) : HMCState d × HMCState d) = z := by cases z; rfl
        have hpt : hmcStep U ε L z.1 z.2 u
            = (if Real.log u < hamiltonian U z - hamiltonian U (leapfrogFlow U ε L z)
                then leapfrogFlow U ε L z else z).1 := by
          simp only [hmcStep]
          rw [hz]
          by_cases h : Real.log u < hamiltonian U z - hamiltonian U (leapfrogFlow U ε L z)
          · simp only [if_pos h]
          · simp only [if_neg h]
        show ((if Real.log u < hamiltonian U z - hamiltonian U (leapfrogFlow U ε L z)
                then leapfrogFlow U ε L z else z) ∈ B ×ˢ (Set.univ : Set (HMCState d)))
            ↔ (hmcStep U ε L z.1 z.2 u ∈ B)
        simp only [Set.mem_prod, Set.mem_univ, and_true]
        rw [hpt]
      have hchild' : ∫⁻ z : HMCState d × HMCState d,
            (Measure.restrict volume (Set.Icc (0 : ℝ) 1))
              {u : ℝ | hmcStep U ε L z.1 z.2 u ∈ B}
            ∂(ρ.prod ((volume : Measure (HMCState d)).withDensity
              (fun p => ENNReal.ofReal (Real.exp (-(1/2) * ‖p‖ ^ 2)))))
          = (ρ.prod ((volume : Measure (HMCState d)).withDensity
              (fun p => ENNReal.ofReal (Real.exp (-(1/2) * ‖p‖ ^ 2))))) (B ×ˢ Set.univ) := by
        rw [← lintegral_congr hstep_eq, ← hν]
        exact statopia_math_node_3566158159_28810915 d U hU_diff ε hε L B hB
      have hSmeas : Measurable (fun q : HMCState d × (HMCState d × ℝ) =>
          hmcStep U ε L q.1 q.2.1 q.2.2) := by
        have hr : Measurable (fun q : HMCState d × (HMCState d × ℝ) =>
            ((q.1, q.2.1), q.2.2)) := by
          simpa using (MeasurableEquiv.prodAssoc).symm.measurable
        exact hhmc.comp hr
      have hS : MeasurableSet {q : HMCState d × (HMCState d × ℝ) |
          hmcStep U ε L q.1 q.2.1 q.2.2 ∈ B} := hSmeas hB
      have hcancel : ∀ (a b c : ℝ≥0∞), a ≠ 0 → a ≠ ⊤ → a * b = a * c → b = c := by
        intro a b c ha0 hat h
        have h2 := congrArg (fun t => a⁻¹ * t) h
        simpa [ENNReal.inv_mul_cancel_left ha0 hat] using h2
      have hS3 : MeasurableSet {q : (HMCState d × HMCState d) × ℝ |
          hmcStep U ε L q.1.1 q.1.2 q.2 ∈ B} := hhmc hB
      have hA1 : ((ρ.prod (gaussianMomentum d)).prod
            (Measure.restrict volume (Set.Icc (0 : ℝ) 1)))
            {q : (HMCState d × HMCState d) × ℝ | hmcStep U ε L q.1.1 q.1.2 q.2 ∈ B}
          = ∫⁻ z, (Measure.restrict volume (Set.Icc (0 : ℝ) 1))
              {u : ℝ | hmcStep U ε L z.1 z.2 u ∈ B} ∂(ρ.prod (gaussianMomentum d)) :=
        Measure.prod_apply hS3
      have hA2 : ((ρ.prod (gaussianMomentum d)).prod
            (Measure.restrict volume (Set.Icc (0 : ℝ) 1)))
            {q : (HMCState d × HMCState d) × ℝ | hmcStep U ε L q.1.1 q.1.2 q.2 ∈ B}
          = (ρ.prod ((gaussianMomentum d).prod (Measure.restrict volume (Set.Icc (0 : ℝ) 1))))
            {q : HMCState d × (HMCState d × ℝ) | hmcStep U ε L q.1 q.2.1 q.2.2 ∈ B} := by
        have hmp := measurePreserving_prodAssoc ρ (gaussianMomentum d)
          (Measure.restrict volume (Set.Icc (0 : ℝ) 1))
        rw [← hmp.map_eq, Measure.map_apply hmp.measurable hS]
        congr 1
      have hA3 : (ρ.prod ((gaussianMomentum d).prod (Measure.restrict volume (Set.Icc (0 : ℝ) 1))))
            {q : HMCState d × (HMCState d × ℝ) | hmcStep U ε L q.1 q.2.1 q.2.2 ∈ B}
          = ∫⁻ x, (∫⁻ p, (Measure.restrict volume (Set.Icc (0 : ℝ) 1))
              {u : ℝ | hmcStep U ε L x p u ∈ B} ∂(gaussianMomentum d)) ∂ρ := by
        rw [Measure.prod_apply hS]
        refine lintegral_congr fun x => ?_
        rw [Measure.prod_apply (μ := gaussianMomentum d)
          (ν := Measure.restrict volume (Set.Icc (0 : ℝ) 1))
          (s := Prod.mk x ⁻¹'
            {q : HMCState d × (HMCState d × ℝ) | hmcStep U ε L q.1 q.2.1 q.2.2 ∈ B})
          (hW2b x hB)]
        exact lintegral_congr fun p => rfl
      rw [← hA3, ← hA2, hA1]
      rw [hcm] at hchild'
      rw [Measure.prod_smul_right] at hchild'
      rw [lintegral_smul_measure] at hchild'
      rw [Measure.smul_apply, smul_eq_mul] at hchild'
      rw [hprobG] at hchild'
      exact hcancel _ _ _ hc0 hct hchild'
    simp only [hdirac]
    exact hrest
  have hπρ : π = ENNReal.ofReal c • ρ := by
    rw [hπeq, hρ]
    rw [show (fun x => ENNReal.ofReal (c * Real.exp (- U x)))
          = ENNReal.ofReal c • (fun x => ENNReal.ofReal (Real.exp (- U x))) from by
        funext x
        change ENNReal.ofReal (c * Real.exp (- U x))
          = ENNReal.ofReal c * ENNReal.ofReal (Real.exp (- U x))
        exact ENNReal.ofReal_mul (le_of_lt hc)]
    exact withDensity_smul' (ENNReal.ofReal c) _ ENNReal.ofReal_ne_top
  have hmain : ∫⁻ x, hmcKernel U ε (Measure.dirac L) x A ∂π
      = ENNReal.ofReal c * ∫⁻ x, hmcKernel U ε (Measure.dirac L) x A ∂ρ := by
    rw [hπρ, lintegral_smul_measure, smul_eq_mul]
  rw [hmain, hcore A hA]
  simp only [hπρ, Measure.smul_apply, smul_eq_mul]
  /- @proof-region region.target-node.session.0a12c00dbefd2ff1 end -/

end Statlib.Imported

end

