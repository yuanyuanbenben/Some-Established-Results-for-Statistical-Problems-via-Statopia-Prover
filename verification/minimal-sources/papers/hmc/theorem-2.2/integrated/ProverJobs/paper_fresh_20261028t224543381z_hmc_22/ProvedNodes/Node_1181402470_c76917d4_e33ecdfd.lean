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


set_option autoImplicit false in
theorem statopia_math_node_1181402470_c76917d4 : ∀ (d : ℕ) (hd : 0 < d) (U : HMCState d → ℝ) (hU_diff : Differentiable ℝ U)
    (hU_grad_meas : Measurable (fun y : HMCState d => gradient U y))
    (ε : ℝ) (hε : 0 < ε) (L : ℕ) (x : HMCState d) (A : Set (HMCState d))
    (hA : MeasurableSet A),
    ((gaussianMomentum d).prod (volume.restrict (Set.Icc (0 : ℝ) 1))).map
        (fun w : HMCState d × ℝ => hmcStep U ε L x w.1 w.2) A
      = ENNReal.ofReal
          ((∫ p : HMCState d, acceptProb U ε L (x, p) *
              (A.indicator (fun _ : HMCState d => (1 : ℝ)) (leapfrogFlow U ε L (x, p)).1)
                ∂(gaussianMomentum d))
            + (∫ p : HMCState d, (1 - acceptProb U ε L (x, p)) ∂(gaussianMomentum d)) *
                (A.indicator (fun _ : HMCState d => (1 : ℝ)) x)) := by
  /- @proof-region region.target-node.session.0d32ea829af86076 begin -/
  intro d hd U hU_diff hU_grad_meas ε hε L x A hA
  haveI hprob : IsProbabilityMeasure (gaussianMomentum d) := by
    haveI hpi : IsProbabilityMeasure (Measure.pi (fun _ : Fin d => gaussianReal (0 : ℝ) 1)) :=
      MeasureTheory.Measure.pi.instIsProbabilityMeasure _
    unfold gaussianMomentum
    exact MeasureTheory.Measure.isProbabilityMeasure_map
      (EuclideanSpace.equiv (Fin d) ℝ).symm.continuous.measurable.aemeasurable
  set ind : HMCState d → ℝ := A.indicator (fun _ : HMCState d => (1 : ℝ)) with hind
  have hind_nonneg : ∀ y : HMCState d, 0 ≤ ind y := by
    intro y
    rw [hind]
    by_cases hy : y ∈ A <;> simp [Set.indicator_apply, hy]
  have hind_le_one : ∀ y : HMCState d, ind y ≤ 1 := by
    intro y
    rw [hind]
    by_cases hy : y ∈ A <;> simp [Set.indicator_apply, hy]
  have hα_nonneg : ∀ p : HMCState d, 0 ≤ acceptProb U ε L (x, p) := by
    intro p
    simp only [acceptProb]
    exact le_min zero_le_one (Real.exp_pos _).le
  have hα_le_one : ∀ p : HMCState d, acceptProb U ε L (x, p) ≤ 1 := by
    intro p
    simp only [acceptProb]
    exact min_le_left _ _
  have hU_meas : Measurable U := hU_diff.continuous.measurable
  have hham : Measurable (fun z : HMCState d × HMCState d => hamiltonian U z) := by
    unfold hamiltonian
    measurability
  have hstepm : Measurable (leapfrogStep U ε) := by
    unfold leapfrogStep
    measurability
  have hflowm : Measurable (leapfrogFlow U ε L) := hstepm.iterate L
  have hpairx : Measurable (fun p : HMCState d => (x, p)) := by measurability
  have hflowx : Measurable (fun p : HMCState d => leapfrogFlow U ε L (x, p)) :=
    hflowm.comp hpairx
  have hf : Measurable (fun w : HMCState d × ℝ => hmcStep U ε L x w.1 w.2) := by
    have hlog : Measurable (fun w : HMCState d × ℝ => Real.log w.2) :=
      Real.measurable_log.comp measurable_snd
    have hpairw : Measurable (fun w : HMCState d × ℝ => (x, w.1)) := by measurability
    have h1 : Measurable (fun w : HMCState d × ℝ => hamiltonian U (x, w.1)) :=
      hham.comp hpairw
    have h2 : Measurable (fun w : HMCState d × ℝ =>
        hamiltonian U (leapfrogFlow U ε L (x, w.1))) :=
      hham.comp (hflowx.comp measurable_fst)
    have h3 : Measurable (fun w : HMCState d × ℝ => (leapfrogFlow U ε L (x, w.1)).1) :=
      (hflowx.comp measurable_fst).fst
    set S : Set (HMCState d × ℝ) :=
      {w | Real.log w.2 < hamiltonian U (x, w.1) - hamiltonian U (leapfrogFlow U ε L (x, w.1))}
      with hSdef
    have hS : MeasurableSet S := by
      rw [hSdef]
      exact measurableSet_lt hlog (h1.sub h2)
    have hEq : (fun w : HMCState d × ℝ => hmcStep U ε L x w.1 w.2)
        = fun w => S.indicator (fun w => (leapfrogFlow U ε L (x, w.1)).1) w
            + Sᶜ.indicator (fun _ => x) w := by
      funext w
      simp only [hmcStep, hSdef, Set.mem_setOf_eq]
      by_cases hw : Real.log w.2 <
          hamiltonian U (x, w.1) - hamiltonian U (leapfrogFlow U ε L (x, w.1))
      · simp [Set.indicator, hw]
      · simp [Set.indicator, hw]
    rw [hEq]
    have hind1 : Measurable (S.indicator (fun w : HMCState d × ℝ =>
        (leapfrogFlow U ε L (x, w.1)).1)) := by measurability
    have hind2 : Measurable (Sᶜ.indicator (fun _ : HMCState d × ℝ => x)) := by measurability
    exact hind1.add hind2
  have hα_meas : Measurable (fun p : HMCState d => acceptProb U ε L (x, p)) := by
    have h1 : Measurable (fun p : HMCState d => hamiltonian U (x, p)) :=
      hham.comp hpairx
    have h2 : Measurable (fun p : HMCState d =>
        hamiltonian U (leapfrogFlow U ε L (x, p))) := hham.comp hflowx
    simp only [acceptProb]
    measurability
  have hind_meas : Measurable ind := by
    rw [hind]
    measurability
  have hΦ1 : Measurable (fun p : HMCState d => (leapfrogFlow U ε L (x, p)).1) := hflowx.fst
  have hm1 : Measurable (fun p : HMCState d =>
      acceptProb U ε L (x, p) * ind (leapfrogFlow U ε L (x, p)).1) :=
    hα_meas.mul (hind_meas.comp hΦ1)
  have hm2 : Measurable (fun p : HMCState d => (1 - acceptProb U ε L (x, p)) * ind x) :=
    (measurable_const.sub hα_meas).mul measurable_const
  have hin : ∀ p : HMCState d,
      ∫⁻ u in Set.Icc (0 : ℝ) 1,
          (A.indicator (fun _ : HMCState d => (1 : ENNReal)) (hmcStep U ε L x p u))
        = ENNReal.ofReal (acceptProb U ε L (x, p) * ind (leapfrogFlow U ε L (x, p)).1
            + (1 - acceptProb U ε L (x, p)) * ind x) := by
    intro p
    set cΦ : ENNReal := A.indicator (fun _ : HMCState d => (1 : ENNReal)) (leapfrogFlow U ε L (x, p)).1
      with hcΦ
    set cX : ENNReal := A.indicator (fun _ : HMCState d => (1 : ENNReal)) x with hcX
    set S : Set ℝ :=
      {u : ℝ | Real.log u < hamiltonian U (x, p) - hamiltonian U (leapfrogFlow U ε L (x, p))}
      with hSdef
    have hS : MeasurableSet S := by
      rw [hSdef]
      exact measurableSet_lt Real.measurable_log (measurable_const.sub measurable_const)
    have hsplit : ∀ u : ℝ,
        A.indicator (fun _ : HMCState d => (1 : ENNReal)) (hmcStep U ε L x p u)
          = S.indicator (fun _ => cΦ) u + Sᶜ.indicator (fun _ => cX) u := by
      intro u
      have hstep : hmcStep U ε L x p u
          = if u ∈ S then (leapfrogFlow U ε L (x, p)).1 else x := by
        simp only [hmcStep, hSdef, Set.mem_setOf_eq]
      rw [hstep, hcΦ, hcX]
      by_cases hu : u ∈ S <;> simp [Set.indicator_apply, hu]
    have hkey : ∀ (T : Set ℝ), MeasurableSet T → ∀ c : ENNReal,
        ∫⁻ u in Set.Icc (0 : ℝ) 1, T.indicator (fun _ => c) u ∂volume
          = c * volume (T ∩ Set.Icc (0 : ℝ) 1) := by
      intro T hT c
      rw [← MeasureTheory.lintegral_indicator measurableSet_Icc]
      have hfun : (Set.Icc (0 : ℝ) 1).indicator (T.indicator (fun _ => c))
          = (T ∩ Set.Icc (0 : ℝ) 1).indicator (fun _ => c) := by
        funext u
        by_cases h1 : u ∈ Set.Icc (0 : ℝ) 1 <;> by_cases h2 : u ∈ T <;>
          simp [Set.indicator_apply, h1, h2]
      rw [hfun, MeasureTheory.lintegral_indicator_const (hT.inter measurableSet_Icc) c]
    have hInt1 : ∫⁻ u in Set.Icc (0 : ℝ) 1,
          (A.indicator (fun _ : HMCState d => (1 : ENNReal)) (hmcStep U ε L x p u)) ∂volume
        = ∫⁻ u in Set.Icc (0 : ℝ) 1,
          (S.indicator (fun _ => cΦ) u + Sᶜ.indicator (fun _ => cX) u) ∂volume :=
      MeasureTheory.lintegral_congr hsplit
    have hInt2 : ∫⁻ u in Set.Icc (0 : ℝ) 1,
          (S.indicator (fun _ => cΦ) u + Sᶜ.indicator (fun _ => cX) u) ∂volume
        = cΦ * volume (S ∩ Set.Icc (0 : ℝ) 1)
          + cX * volume (Sᶜ ∩ Set.Icc (0 : ℝ) 1) := by
      rw [MeasureTheory.lintegral_add_left
          (show Measurable (S.indicator (fun _ : ℝ => cΦ)) from by measurability),
        hkey S hS cΦ, hkey Sᶜ hS.compl cX]
    have hvol1 : volume (S ∩ Set.Icc (0 : ℝ) 1) = ENNReal.ofReal (acceptProb U ε L (x, p)) := by
      by_cases ht : 0 < hamiltonian U (x, p) - hamiltonian U (leapfrogFlow U ε L (x, p))
      · have hexp_ge : 1 < Real.exp (hamiltonian U (x, p) -
            hamiltonian U (leapfrogFlow U ε L (x, p))) := by
          simpa using (Real.exp_lt_exp.mpr ht : Real.exp 0 < Real.exp (hamiltonian U (x, p) -
            hamiltonian U (leapfrogFlow U ε L (x, p))))
        have hset : S ∩ Set.Icc (0 : ℝ) 1 = Set.Icc (0 : ℝ) 1 := by
          ext u
          rw [Set.mem_inter_iff, hSdef, Set.mem_setOf_eq, Set.mem_Icc]
          constructor
          · rintro ⟨-, h⟩
            exact h
          · rintro ⟨h0, h1⟩
            refine ⟨?_, h0, h1⟩
            by_cases hu : 0 < u
            · have h : Real.exp (Real.log u) < Real.exp (hamiltonian U (x, p) -
                  hamiltonian U (leapfrogFlow U ε L (x, p))) := by
                rw [Real.exp_log hu]
                exact lt_of_le_of_lt h1 hexp_ge
              exact Real.exp_lt_exp.mp h
            · push_neg at hu
              have hu0 : u = 0 := le_antisymm hu h0
              rw [hu0, Real.log_zero]
              exact ht
        rw [hset, Real.volume_Icc]
        have hmin : acceptProb U ε L (x, p) = 1 := by
          simp only [acceptProb]
          exact min_eq_left hexp_ge.le
        rw [hmin]
        norm_num
      · push_neg at ht
        have hexp_le : Real.exp (hamiltonian U (x, p) -
            hamiltonian U (leapfrogFlow U ε L (x, p))) ≤ 1 := by
          simpa using (Real.exp_le_exp.mpr ht : Real.exp (hamiltonian U (x, p) -
            hamiltonian U (leapfrogFlow U ε L (x, p))) ≤ Real.exp 0)
        have hset : S ∩ Set.Icc (0 : ℝ) 1 = Set.Ioo (0 : ℝ)
            (Real.exp (hamiltonian U (x, p) - hamiltonian U (leapfrogFlow U ε L (x, p)))) := by
          ext u
          rw [Set.mem_inter_iff, hSdef, Set.mem_setOf_eq, Set.mem_Ioo, Set.mem_Icc]
          constructor
          · rintro ⟨hlog, h0, h1⟩
            have hu : 0 < u := by
              by_contra hle
              push_neg at hle
              have hle0 : u = 0 := le_antisymm hle h0
              rw [hle0, Real.log_zero] at hlog
              linarith
            refine ⟨hu, ?_⟩
            have h := Real.exp_lt_exp.mpr hlog
            rwa [Real.exp_log hu] at h
          · rintro ⟨h0, hexp⟩
            refine ⟨?_, le_of_lt h0, ?_⟩
            · have h : Real.exp (Real.log u) < Real.exp (hamiltonian U (x, p) -
                  hamiltonian U (leapfrogFlow U ε L (x, p))) := by
                rwa [Real.exp_log h0]
              exact Real.exp_lt_exp.mp h
            · exact le_of_lt (lt_of_lt_of_le hexp hexp_le)
        rw [hset, Real.volume_Ioo]
        have hmin : acceptProb U ε L (x, p) =
            Real.exp (hamiltonian U (x, p) - hamiltonian U (leapfrogFlow U ε L (x, p))) := by
          simp only [acceptProb]
          exact min_eq_right hexp_le
        rw [hmin, sub_zero]
    have hvol2 : volume (Sᶜ ∩ Set.Icc (0 : ℝ) 1)
        = ENNReal.ofReal (1 - acceptProb U ε L (x, p)) := by
      have hsub : Sᶜ ∩ Set.Icc (0 : ℝ) 1
          = Set.Icc (0 : ℝ) 1 \ (S ∩ Set.Icc (0 : ℝ) 1) := by
        ext u
        simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_diff]
        tauto
      have hne : volume (S ∩ Set.Icc (0 : ℝ) 1) ≠ ⊤ := by
        rw [hvol1]
        exact ENNReal.ofReal_ne_top
      rw [hsub, MeasureTheory.measure_diff Set.inter_subset_right
        (hS.inter measurableSet_Icc).nullMeasurableSet hne,
        hvol1, Real.volume_Icc, show (1 : ℝ) - 0 = 1 by norm_num]
      exact (ENNReal.ofReal_sub (1 : ℝ) (hα_nonneg p)).symm
    have hcΦ' : cΦ = ENNReal.ofReal (ind (leapfrogFlow U ε L (x, p)).1) := by
      rw [hcΦ, hind]
      by_cases hy : (leapfrogFlow U ε L (x, p)).1 ∈ A <;> simp [Set.indicator_apply, hy]
    have hcX' : cX = ENNReal.ofReal (ind x) := by
      rw [hcX, hind]
      by_cases hy : x ∈ A <;> simp [Set.indicator_apply, hy]
    have hfin : cΦ * ENNReal.ofReal (acceptProb U ε L (x, p))
          + cX * ENNReal.ofReal (1 - acceptProb U ε L (x, p))
        = ENNReal.ofReal (acceptProb U ε L (x, p) * ind (leapfrogFlow U ε L (x, p)).1
            + (1 - acceptProb U ε L (x, p)) * ind x) := by
      rw [hcΦ', hcX']
      rw [← ENNReal.ofReal_mul (hind_nonneg (leapfrogFlow U ε L (x, p)).1),
        ← ENNReal.ofReal_mul (hind_nonneg x)]
      rw [← ENNReal.ofReal_add
        (mul_nonneg (hind_nonneg (leapfrogFlow U ε L (x, p)).1) (hα_nonneg p))
        (mul_nonneg (hind_nonneg x) (by linarith [hα_le_one p]))]
      congr 1
      ring
    calc ∫⁻ u in Set.Icc (0 : ℝ) 1,
          (A.indicator (fun _ : HMCState d => (1 : ENNReal)) (hmcStep U ε L x p u)) ∂volume
        = cΦ * volume (S ∩ Set.Icc (0 : ℝ) 1)
            + cX * volume (Sᶜ ∩ Set.Icc (0 : ℝ) 1) := hInt1.trans hInt2
      _ = cΦ * ENNReal.ofReal (acceptProb U ε L (x, p))
            + cX * ENNReal.ofReal (1 - acceptProb U ε L (x, p)) := by rw [hvol1, hvol2]
      _ = ENNReal.ofReal (acceptProb U ε L (x, p) * ind (leapfrogFlow U ε L (x, p)).1
            + (1 - acceptProb U ε L (x, p)) * ind x) := hfin
  have hb1 : Integrable (fun p : HMCState d =>
      acceptProb U ε L (x, p) * ind (leapfrogFlow U ε L (x, p)).1) (gaussianMomentum d) := by
    refine MeasureTheory.Integrable.of_bound hm1.aestronglyMeasurable 1 ?_
    filter_upwards with p
    have h1 := hα_nonneg p
    have h2 := hα_le_one p
    have h3 := hind_nonneg (leapfrogFlow U ε L (x, p)).1
    have h4 := hind_le_one (leapfrogFlow U ε L (x, p)).1
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h1, abs_of_nonneg h3]
    nlinarith
  have hb2 : Integrable (fun p : HMCState d =>
      (1 - acceptProb U ε L (x, p)) * ind x) (gaussianMomentum d) := by
    refine MeasureTheory.Integrable.of_bound hm2.aestronglyMeasurable 1 ?_
    filter_upwards with p
    have h1 := hα_nonneg p
    have h2 := hα_le_one p
    have h3 := hind_nonneg x
    have h4 := hind_le_one x
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - acceptProb U ε L (x, p)), abs_of_nonneg h3]
    nlinarith
  have hnn : 0 ≤ᵐ[gaussianMomentum d] (fun p : HMCState d =>
      acceptProb U ε L (x, p) * ind (leapfrogFlow U ε L (x, p)).1
        + (1 - acceptProb U ε L (x, p)) * ind x) := by
    filter_upwards with p
    have h1 : 0 ≤ acceptProb U ε L (x, p) * ind (leapfrogFlow U ε L (x, p)).1 :=
      mul_nonneg (hα_nonneg p) (hind_nonneg _)
    have h2 : 0 ≤ (1 - acceptProb U ε L (x, p)) * ind x :=
      mul_nonneg (by linarith [hα_le_one p]) (hind_nonneg x)
    exact add_nonneg h1 h2
  have hpre : MeasurableSet ((fun w : HMCState d × ℝ => hmcStep U ε L x w.1 w.2) ⁻¹' A) :=
    hA.preimage hf
  calc ((gaussianMomentum d).prod (volume.restrict (Set.Icc (0 : ℝ) 1))).map
        (fun w : HMCState d × ℝ => hmcStep U ε L x w.1 w.2) A
      = ((gaussianMomentum d).prod (volume.restrict (Set.Icc (0 : ℝ) 1)))
          ((fun w : HMCState d × ℝ => hmcStep U ε L x w.1 w.2) ⁻¹' A) :=
        MeasureTheory.Measure.map_apply hf hA
    _ = ∫⁻ w, ((fun w : HMCState d × ℝ => hmcStep U ε L x w.1 w.2) ⁻¹' A).indicator
          (fun _ => (1 : ENNReal)) w
          ∂((gaussianMomentum d).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
        rw [MeasureTheory.lintegral_indicator_const hpre (1 : ENNReal), one_mul]
    _ = ∫⁻ p, ∫⁻ u, (((fun w : HMCState d × ℝ => hmcStep U ε L x w.1 w.2) ⁻¹' A).indicator
          (fun _ => (1 : ENNReal))) (p, u)
          ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) ∂(gaussianMomentum d) := by
        refine MeasureTheory.lintegral_prod (μ := gaussianMomentum d)
          (ν := volume.restrict (Set.Icc (0 : ℝ) 1))
          (f := ((fun w : HMCState d × ℝ => hmcStep U ε L x w.1 w.2) ⁻¹' A).indicator
            (fun _ => (1 : ENNReal))) ?_
        measurability
    _ = ∫⁻ p, ∫⁻ u in Set.Icc (0 : ℝ) 1,
          (A.indicator (fun _ : HMCState d => (1 : ENNReal)) (hmcStep U ε L x p u)) ∂volume
          ∂(gaussianMomentum d) := by
        refine MeasureTheory.lintegral_congr (fun p => ?_)
        refine MeasureTheory.lintegral_congr (fun u => ?_)
        by_cases h : hmcStep U ε L x p u ∈ A <;> simp [Set.mem_preimage, h]
    _ = ∫⁻ p, ENNReal.ofReal (acceptProb U ε L (x, p) * ind (leapfrogFlow U ε L (x, p)).1
            + (1 - acceptProb U ε L (x, p)) * ind x) ∂(gaussianMomentum d) :=
        MeasureTheory.lintegral_congr hin
    _ = ENNReal.ofReal (∫ p, (acceptProb U ε L (x, p) * ind (leapfrogFlow U ε L (x, p)).1
            + (1 - acceptProb U ε L (x, p)) * ind x) ∂(gaussianMomentum d)) :=
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hb1.add hb2) hnn).symm
    _ = ENNReal.ofReal ((∫ p, acceptProb U ε L (x, p) * ind (leapfrogFlow U ε L (x, p)).1
            ∂(gaussianMomentum d))
          + (∫ p, (1 - acceptProb U ε L (x, p)) ∂(gaussianMomentum d)) * ind x) := by
        rw [MeasureTheory.integral_add hb1 hb2, MeasureTheory.integral_mul_const]
  /- @proof-region region.target-node.session.0d32ea829af86076 end -/

end Statlib.Imported

end

