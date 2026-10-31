import ProverJobs.paper_fresh_20261028t224543381z_hmc_22.Vocabulary
import ProverJobs.paper_fresh_20261028t224543381z_hmc_22.Base
import ProverJobs.paper_fresh_20261028t224543381z_hmc_22.ProvedNodes.Node_1181402470_c76917d4_e33ecdfd

namespace PaperProofTasks.paper_fresh_20261028t224543381z_hmc_22
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
open _root_.PaperProofTasks.paper_fresh_20261028t224543381z_hmc_22.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
namespace Statlib.Imported


set_option autoImplicit false in
theorem statopia_math_node_1760066137_9d09a34f : ∀ (d : ℕ) (hd : 0 < d) (U : HMCState d → ℝ)
    (hU_diff : Differentiable ℝ U)
    (hgrad_meas : Measurable (fun x : HMCState d => gradient U x))
    (ε : ℝ) (hε : 0 < ε) (L : ℕ),
    let μg : Measure (HMCState d) := gaussianMomentum d
    let P : HMCState d → Measure (HMCState d) := fun x =>
      (μg.prod (volume.restrict (Set.Icc (0 : ℝ) 1))).map
        (fun w : HMCState d × ℝ => hmcStep U ε L x w.1 w.2)
    let Q : HMCState d → Measure (HMCState d) := fun x =>
      μg.map (fun p : HMCState d => (leapfrogFlow U ε L (x, p)).1)
    let r : HMCState d → ℝ := fun x =>
      ∫ p, (1 - acceptProb U ε L (x, p)) ∂μg
    (∀ x : HMCState d, IsProbabilityMeasure (P x)) ∧
      (∀ (x : HMCState d) (A : Set (HMCState d)), MeasurableSet A →
        P x A = ENNReal.ofReal
          ((∫ p, acceptProb U ε L (x, p) *
              (A.indicator (fun _ : HMCState d => (1 : ℝ)) (leapfrogFlow U ε L (x, p)).1) ∂μg)
            + r x * (A.indicator (fun _ : HMCState d => (1 : ℝ)) x))) ∧
      (∀ x : HMCState d, ENNReal.ofReal (r x) ≤ P x {x}) ∧
      (∀ (x : HMCState d) (B : Set (HMCState d)), MeasurableSet B → x ∈ B →
        Q x B ≤ P x B) ∧
      (L = 0 →
        (∀ z : HMCState d × HMCState d, acceptProb U ε 0 z = 1) ∧
          (∀ x : HMCState d, (∫ p, (1 - acceptProb U ε 0 (x, p)) ∂μg) = 0) ∧
            (∀ x : HMCState d,
              (μg.prod (volume.restrict (Set.Icc (0 : ℝ) 1))).map
                  (fun w : HMCState d × ℝ => hmcStep U ε 0 x w.1 w.2)
                = Measure.dirac x)) := by
  /- @proof-region region.target-node.session.274f3c2d6bcbd841 begin -/
  intro d hd U hU_diff hgrad_meas ε hε L
  dsimp only
  have hUmeas : Measurable U := hU_diff.continuous.measurable
  have hgrad : Measurable (fun x : HMCState d => gradient U x) := hgrad_meas
  have hham : Measurable (hamiltonian U) := by
    unfold hamiltonian
    fun_prop
  have hleapStep : Measurable (leapfrogStep U ε) := by
    unfold leapfrogStep
    fun_prop
  have hflow : Measurable (leapfrogFlow U ε L) := by
    unfold leapfrogFlow
    exact hleapStep.iterate L
  have hstep_meas : ∀ x : HMCState d,
      Measurable (fun w : HMCState d × ℝ => hmcStep U ε L x w.1 w.2) := by
    intro x
    have hpair : Measurable (fun w : HMCState d × ℝ => ((x : HMCState d), w.1)) := by fun_prop
    have hz : Measurable (fun w : HMCState d × ℝ => leapfrogFlow U ε L (x, w.1)) :=
      hflow.comp hpair
    have hcond : MeasurableSet {w : HMCState d × ℝ |
        Real.log w.2 < hamiltonian U (x, w.1) - hamiltonian U (leapfrogFlow U ε L (x, w.1))} := by
      apply measurableSet_lt
      · fun_prop
      · exact (hham.comp hpair).sub (hham.comp hz)
    have heq : (fun w : HMCState d × ℝ => hmcStep U ε L x w.1 w.2)
        = fun w => if Real.log w.2 < hamiltonian U (x, w.1) - hamiltonian U (leapfrogFlow U ε L (x, w.1))
            then (leapfrogFlow U ε L (x, w.1)).1 else x := by
      funext w
      simp only [hmcStep]
    rw [heq]
    exact Measurable.ite hcond (measurable_fst.comp hz) measurable_const
  have hνuniv : volume.restrict (Set.Icc (0 : ℝ) 1) Set.univ = 1 := by
    simp [Real.volume_Icc]
  haveI hν : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := ⟨hνuniv⟩
  haveI hμG : IsProbabilityMeasure (gaussianMomentum d) := by
    have hmeas : AEMeasurable (fun y : Fin d → ℝ => (EuclideanSpace.equiv (Fin d) ℝ).symm y)
        (Measure.pi (fun _ : Fin d => gaussianReal (0 : ℝ) 1)) :=
      (EuclideanSpace.measurableEquiv (Fin d)).symm.measurable.aemeasurable
    exact Measure.isProbabilityMeasure_map hmeas
  have key : ∀ (x : HMCState d) (A : Set (HMCState d)), MeasurableSet A →
      ((gaussianMomentum d).prod (volume.restrict (Set.Icc (0 : ℝ) 1))).map
          (fun w : HMCState d × ℝ => hmcStep U ε L x w.1 w.2) A
        = ENNReal.ofReal
            ((∫ p, acceptProb U ε L (x, p) *
                (A.indicator (fun _ : HMCState d => (1 : ℝ)) (leapfrogFlow U ε L (x, p)).1) ∂(gaussianMomentum d))
              + (∫ p, (1 - acceptProb U ε L (x, p)) ∂(gaussianMomentum d)) *
                (A.indicator (fun _ : HMCState d => (1 : ℝ)) x)) := by
    intro x A hA
    exact statopia_math_node_1181402470_c76917d4 d hd U hU_diff hgrad_meas ε hε L x A hA
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    exact Measure.isProbabilityMeasure_map (hstep_meas x).aemeasurable
  · exact key
  · intro x
    rw [key x {x} (MeasurableSet.singleton x)]
    apply ENNReal.ofReal_le_ofReal
    have hx : ({x} : Set (HMCState d)).indicator (fun _ : HMCState d => (1 : ℝ)) x = 1 := by simp
    rw [hx, mul_one]
    have hnn : 0 ≤ ∫ p, acceptProb U ε L (x, p) *
        ({x} : Set (HMCState d)).indicator (fun _ : HMCState d => (1 : ℝ)) (leapfrogFlow U ε L (x, p)).1 ∂(gaussianMomentum d) := by
      apply integral_nonneg
      intro p
      apply mul_nonneg
      · unfold acceptProb
        exact le_min zero_le_one (le_of_lt (Real.exp_pos _))
      · by_cases hmem : (leapfrogFlow U ε L (x, p)).1 ∈ ({x} : Set (HMCState d))
        · rw [Set.indicator_of_mem hmem]; simp
        · rw [Set.indicator_of_notMem hmem]
    linarith
  · intro x B hB hxB
    have hpair' : Measurable (fun p : HMCState d => ((x : HMCState d), p)) := by fun_prop
    have hg : Measurable (fun p : HMCState d => (leapfrogFlow U ε L (x, p)).1) :=
      measurable_fst.comp (hflow.comp hpair')
    haveI hPinst : IsProbabilityMeasure
        (((gaussianMomentum d).prod (volume.restrict (Set.Icc (0 : ℝ) 1))).map
          (fun w : HMCState d × ℝ => hmcStep U ε L x w.1 w.2)) :=
      Measure.isProbabilityMeasure_map (hstep_meas x).aemeasurable
    haveI hQinst : IsProbabilityMeasure
        ((gaussianMomentum d).map (fun p : HMCState d => (leapfrogFlow U ε L (x, p)).1)) :=
      Measure.isProbabilityMeasure_map hg.aemeasurable
    have hPc : ((gaussianMomentum d).prod (volume.restrict (Set.Icc (0 : ℝ) 1))).map
        (fun w : HMCState d × ℝ => hmcStep U ε L x w.1 w.2) Bᶜ
        = ENNReal.ofReal (∫ p, acceptProb U ε L (x, p) *
            (Bᶜ.indicator (fun _ : HMCState d => (1 : ℝ))) ((leapfrogFlow U ε L (x, p)).1) ∂(gaussianMomentum d)) := by
      rw [key x Bᶜ hB.compl]
      have hx : (Bᶜ.indicator (fun _ : HMCState d => (1 : ℝ))) x = 0 := by
        rw [Set.indicator_of_notMem (by simpa only [Set.mem_compl_iff, not_not] using hxB)]
      rw [hx, mul_zero, add_zero]
    have hPBcle : ((gaussianMomentum d).prod (volume.restrict (Set.Icc (0 : ℝ) 1))).map
        (fun w : HMCState d × ℝ => hmcStep U ε L x w.1 w.2) Bᶜ
        ≤ (gaussianMomentum d).map (fun p : HMCState d => (leapfrogFlow U ε L (x, p)).1) Bᶜ := by
      rw [hPc, Measure.map_apply hg hB.compl]
      have hαmeas : Measurable (fun p : HMCState d => acceptProb U ε L (x, p)) := by
        have hbase : Measurable (fun p : HMCState d =>
            hamiltonian U (x, p) - hamiltonian U (leapfrogFlow U ε L (x, p))) :=
          (hham.comp hpair').sub (hham.comp (hflow.comp hpair'))
        unfold acceptProb
        exact Measurable.min measurable_const (Real.measurable_exp.comp hbase)
      have ha0 : ∀ p : HMCState d, 0 ≤ acceptProb U ε L (x, p) := by
        intro p; unfold acceptProb; exact le_min zero_le_one (le_of_lt (Real.exp_pos _))
      have ha1 : ∀ p : HMCState d, acceptProb U ε L (x, p) ≤ 1 := by
        intro p; unfold acceptProb; exact min_le_left _ _
      have hind0 : ∀ p : HMCState d,
          0 ≤ (Bᶜ.indicator (fun _ : HMCState d => (1 : ℝ))) ((leapfrogFlow U ε L (x, p)).1) := by
        intro p
        by_cases hm : ((leapfrogFlow U ε L (x, p)).1) ∈ Bᶜ
        · rw [Set.indicator_of_mem hm]; norm_num
        · rw [Set.indicator_of_notMem hm]
      have hind1 : ∀ p : HMCState d,
          (Bᶜ.indicator (fun _ : HMCState d => (1 : ℝ))) ((leapfrogFlow U ε L (x, p)).1) ≤ 1 := by
        intro p
        by_cases hm : ((leapfrogFlow U ε L (x, p)).1) ∈ Bᶜ
        · rw [Set.indicator_of_mem hm]
        · rw [Set.indicator_of_notMem hm]; norm_num
      have hconv_ind : ∀ y : HMCState d,
          ENNReal.ofReal ((Bᶜ.indicator (fun _ : HMCState d => (1 : ℝ))) y)
            = (Bᶜ.indicator (fun _ : HMCState d => (1 : ENNReal))) y := by
        intro y
        by_cases hy : y ∈ Bᶜ
        · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]; exact ENNReal.ofReal_one
        · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]; exact ENNReal.ofReal_zero
      have hpt : ∀ p : HMCState d,
          ENNReal.ofReal (acceptProb U ε L (x, p) *
            (Bᶜ.indicator (fun _ : HMCState d => (1 : ℝ))) ((leapfrogFlow U ε L (x, p)).1))
            ≤ (Bᶜ.indicator (fun _ : HMCState d => (1 : ENNReal))) ((leapfrogFlow U ε L (x, p)).1) := by
        intro p
        rw [← hconv_ind]
        exact ENNReal.ofReal_le_ofReal (by simpa using mul_le_mul_of_nonneg_right (ha1 p) (hind0 p))
      have hind_eq : (fun p : HMCState d =>
            (Bᶜ.indicator (fun _ : HMCState d => (1 : ENNReal))) ((leapfrogFlow U ε L (x, p)).1))
          = fun p : HMCState d =>
              ((fun p : HMCState d => (leapfrogFlow U ε L (x, p)).1) ⁻¹' Bᶜ).indicator
                (fun _ => (1 : ENNReal)) p := by
        funext p
        by_cases hm : ((leapfrogFlow U ε L (x, p)).1) ∈ Bᶜ
        · rw [Set.indicator_of_mem hm, Set.indicator_of_mem
            (show p ∈ (fun p : HMCState d => (leapfrogFlow U ε L (x, p)).1) ⁻¹' Bᶜ from hm)]
        · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem
            (show p ∉ (fun p : HMCState d => (leapfrogFlow U ε L (x, p)).1) ⁻¹' Bᶜ from hm)]
      have hInt : Integrable (fun p : HMCState d => acceptProb U ε L (x, p) *
          (Bᶜ.indicator (fun _ : HMCState d => (1 : ℝ))) ((leapfrogFlow U ε L (x, p)).1))
          (gaussianMomentum d) :=
        Integrable.of_bound
          (hαmeas.mul
            (((measurable_const : Measurable (fun _ : HMCState d => (1 : ℝ))).indicator hB.compl).comp hg)).aestronglyMeasurable
          1
          (Filter.Eventually.of_forall (fun p => by
            rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (ha0 p) (hind0 p))]
            exact le_trans (by simpa using mul_le_mul_of_nonneg_right (ha1 p) (hind0 p)) (hind1 p)))
      have hNonneg : 0 ≤ᶠ[ae (gaussianMomentum d)] (fun p : HMCState d => acceptProb U ε L (x, p) *
          (Bᶜ.indicator (fun _ : HMCState d => (1 : ℝ))) ((leapfrogFlow U ε L (x, p)).1)) :=
        Filter.Eventually.of_forall (fun p => mul_nonneg (ha0 p) (hind0 p))
      rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hNonneg]
      calc ∫⁻ p, ENNReal.ofReal (acceptProb U ε L (x, p) *
              (Bᶜ.indicator (fun _ : HMCState d => (1 : ℝ))) ((leapfrogFlow U ε L (x, p)).1))
              ∂(gaussianMomentum d)
          ≤ ∫⁻ p, (Bᶜ.indicator (fun _ : HMCState d => (1 : ENNReal)))
              ((leapfrogFlow U ε L (x, p)).1) ∂(gaussianMomentum d) :=
            lintegral_mono hpt
        _ = ∫⁻ p, ((fun p : HMCState d => (leapfrogFlow U ε L (x, p)).1) ⁻¹' Bᶜ).indicator
              (fun _ => (1 : ENNReal)) p ∂(gaussianMomentum d) := by
            rw [hind_eq]
        _ = (gaussianMomentum d) ((fun p : HMCState d => (leapfrogFlow U ε L (x, p)).1) ⁻¹' Bᶜ) := by
            rw [lintegral_indicator_const (c := (1 : ENNReal)), one_mul]
            exact hg hB.compl
    have hPadd : ((gaussianMomentum d).prod (volume.restrict (Set.Icc (0 : ℝ) 1))).map
        (fun w : HMCState d × ℝ => hmcStep U ε L x w.1 w.2) B
        + ((gaussianMomentum d).prod (volume.restrict (Set.Icc (0 : ℝ) 1))).map
          (fun w : HMCState d × ℝ => hmcStep U ε L x w.1 w.2) Bᶜ = 1 := by
      rw [← measure_union (disjoint_compl_right : Disjoint B Bᶜ) hB.compl,
        Set.union_compl_self, measure_univ]
    have hQadd : (gaussianMomentum d).map (fun p : HMCState d => (leapfrogFlow U ε L (x, p)).1) B
        + (gaussianMomentum d).map (fun p : HMCState d => (leapfrogFlow U ε L (x, p)).1) Bᶜ = 1 := by
      rw [← measure_union (disjoint_compl_right : Disjoint B Bᶜ) hB.compl,
        Set.union_compl_self, measure_univ]
    have hPfin : ((gaussianMomentum d).prod (volume.restrict (Set.Icc (0 : ℝ) 1))).map
        (fun w : HMCState d × ℝ => hmcStep U ε L x w.1 w.2) Bᶜ ≠ ⊤ := measure_ne_top _ _
    refine (ENNReal.add_le_add_iff_right hPfin).1 ?_
    calc (gaussianMomentum d).map (fun p : HMCState d => (leapfrogFlow U ε L (x, p)).1) B
          + ((gaussianMomentum d).prod (volume.restrict (Set.Icc (0 : ℝ) 1))).map
            (fun w : HMCState d × ℝ => hmcStep U ε L x w.1 w.2) Bᶜ
        ≤ (gaussianMomentum d).map (fun p : HMCState d => (leapfrogFlow U ε L (x, p)).1) B
          + (gaussianMomentum d).map (fun p : HMCState d => (leapfrogFlow U ε L (x, p)).1) Bᶜ :=
          add_le_add (le_refl _) hPBcle
      _ = 1 := hQadd
      _ = ((gaussianMomentum d).prod (volume.restrict (Set.Icc (0 : ℝ) 1))).map
            (fun w : HMCState d × ℝ => hmcStep U ε L x w.1 w.2) B
          + ((gaussianMomentum d).prod (volume.restrict (Set.Icc (0 : ℝ) 1))).map
            (fun w : HMCState d × ℝ => hmcStep U ε L x w.1 w.2) Bᶜ := by rw [hPadd]
  · intro hL
    refine ⟨?_, ?_, ?_⟩
    · intro z
      simp [acceptProb, leapfrogFlow]
    · intro x
      simp [acceptProb, leapfrogFlow]
    · intro x
      have hfun : (fun w : HMCState d × ℝ => hmcStep U ε 0 x w.1 w.2) = (fun _ => x) := by
        funext w
        simp [hmcStep, leapfrogFlow]
      rw [hfun, Measure.map_const]
      have hprod : (gaussianMomentum d).prod (volume.restrict (Set.Icc (0 : ℝ) 1)) Set.univ = 1 :=
        measure_univ
      rw [hprod, one_smul]
  /- @proof-region region.target-node.session.274f3c2d6bcbd841 end -/

end Statlib.Imported

end

