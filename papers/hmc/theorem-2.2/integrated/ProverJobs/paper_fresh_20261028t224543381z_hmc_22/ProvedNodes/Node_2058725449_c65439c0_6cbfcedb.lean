import ProverJobs.paper_fresh_20261028t224543381z_hmc_22.Vocabulary
import ProverJobs.paper_fresh_20261028t224543381z_hmc_22.Base
import ProverJobs.paper_fresh_20261028t224543381z_hmc_22.ProvedNodes.Node_4216601107_b295b242_d686ddc2

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
theorem statopia_math_node_2058725449_c65439c0 : ∀ (d : ℕ),
    let m : Measure (HMCState d) := (volume : Measure (HMCState d)).withDensity
      (fun p : HMCState d => ENNReal.ofReal (Real.exp (-(1 / 2) * ‖p‖ ^ 2)))
    m Set.univ ≠ 0 ∧ m Set.univ ≠ ⊤ ∧ m = m Set.univ • gaussianMomentum d := by
  /- @proof-region region.target-node.session.9a1b304e9fedfb89 begin -/
  intro d
  let m : Measure (HMCState d) := (volume : Measure (HMCState d)).withDensity
    (fun p : HMCState d => ENNReal.ofReal (Real.exp (-(1 / 2) * ‖p‖ ^ 2)))
  change m Set.univ ≠ 0 ∧ m Set.univ ≠ ⊤ ∧ m = m Set.univ • gaussianMomentum d
  have hguniv : gaussianMomentum d Set.univ = 1 := by
    rw [gaussianMomentum, Measure.map_apply (by measurability) MeasurableSet.univ,
      Set.preimage_univ, Measure.pi_univ]
    simp
  have hmass : m = ENNReal.ofReal ((Real.sqrt (2 * Real.pi)) ^ d) • gaussianMomentum d := by
    have hmeas : Measurable (WithLp.toLp 2 : (Fin d → ℝ) → HMCState d) := by
      rw [← MeasurableEquiv.coe_toLp (2 : ENNReal) (Fin d → ℝ)]
      exact (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable
    have hmp : MeasurePreserving (WithLp.toLp 2) (volume : Measure (Fin d → ℝ))
        (volume : Measure (HMCState d)) := PiLp.volume_preserving_toLp (Fin d)
    have hcoe : ⇑(EuclideanSpace.equiv (Fin d) ℝ).symm
        = (WithLp.toLp 2 : (Fin d → ℝ) → HMCState d) := rfl
    have hnorm : ∀ x : Fin d → ℝ, ‖WithLp.toLp 2 x‖ ^ 2 = ∑ i : Fin d, (x i) ^ 2 := by
      intro x
      rw [EuclideanSpace.norm_sq_eq]
      simp
    have hF2 : Measure.map (WithLp.toLp 2)
        ((volume : Measure (Fin d → ℝ)).withDensity
          (fun x : Fin d → ℝ => ENNReal.ofReal (Real.exp (-(1 / 2) * ∑ i : Fin d, (x i) ^ 2))))
        = (volume : Measure (HMCState d)).withDensity
          (fun p : HMCState d => ENNReal.ofReal (Real.exp (-(1 / 2) * ‖p‖ ^ 2))) := by
      refine Measure.ext fun t ht => ?_
      rw [Measure.map_apply hmeas ht,
        withDensity_apply (fun x : Fin d → ℝ =>
          ENNReal.ofReal (Real.exp (-(1 / 2) * ∑ i : Fin d, (x i) ^ 2))) (ht.preimage hmeas),
        withDensity_apply (fun p : HMCState d =>
          ENNReal.ofReal (Real.exp (-(1 / 2) * ‖p‖ ^ 2))) ht]
      have hind : ∀ x : Fin d → ℝ,
          t.indicator (fun q : HMCState d => ENNReal.ofReal (Real.exp (-(1 / 2) * ‖q‖ ^ 2)))
              ((MeasurableEquiv.toLp 2 (Fin d → ℝ)) x)
            = (WithLp.toLp 2 ⁻¹' t).indicator
                (fun x : Fin d → ℝ =>
                  ENNReal.ofReal (Real.exp (-(1 / 2) * ∑ i : Fin d, (x i) ^ 2))) x := by
        intro x
        rw [MeasurableEquiv.toLp_apply]
        by_cases hx : WithLp.toLp 2 x ∈ t
        · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show x ∈ WithLp.toLp 2 ⁻¹' t from hx)]
          rw [hnorm x]
        · simp [hx]
      rw [← MeasureTheory.lintegral_indicator (f := fun q : HMCState d =>
          ENNReal.ofReal (Real.exp (-(1 / 2) * ‖q‖ ^ 2))) ht,
        MeasurePreserving.lintegral_map_equiv
          (fun p : HMCState d =>
            t.indicator (fun q : HMCState d => ENNReal.ofReal (Real.exp (-(1 / 2) * ‖q‖ ^ 2))) p)
          (MeasurableEquiv.toLp 2 (Fin d → ℝ))
          (by simpa only [MeasurableEquiv.coe_toLp] using hmp)]
      simp only [hind]
      rw [MeasureTheory.lintegral_indicator (f := fun x : Fin d → ℝ =>
        ENNReal.ofReal (Real.exp (-(1 / 2) * ∑ i : Fin d, (x i) ^ 2))) (ht.preimage hmeas)]
    have hmap_smul : ∀ (r : ENNReal) (μ : Measure (Fin d → ℝ)),
        Measure.map (WithLp.toLp 2) (r • μ) = r • Measure.map (WithLp.toLp 2) μ := by
      intro r μ
      refine Measure.ext fun t ht => ?_
      rw [Measure.map_apply hmeas ht, Measure.smul_apply, Measure.smul_apply,
        Measure.map_apply hmeas ht]
    have hchild := statopia_math_node_4216601107_b295b242 d
    have hgm : gaussianMomentum d
        = ENNReal.ofReal (((Real.sqrt (2 * Real.pi)) ^ d))⁻¹ • m := by
      rw [gaussianMomentum, hcoe, hchild, hmap_smul, hF2]
    have hpos' : (0 : ℝ) < (Real.sqrt (2 * Real.pi)) ^ d :=
      pow_pos (Real.sqrt_pos.2 (by positivity)) d
    have hkey : ENNReal.ofReal ((Real.sqrt (2 * Real.pi)) ^ d)
        * ENNReal.ofReal (((Real.sqrt (2 * Real.pi)) ^ d))⁻¹ = 1 := by
      rw [← ENNReal.ofReal_mul (le_of_lt hpos'),
        mul_inv_cancel₀ (pow_ne_zero d (Real.sqrt_pos.2 (by positivity)).ne'),
        ENNReal.ofReal_one]

    refine Measure.ext fun s hs => ?_
    rw [Measure.smul_apply, hgm, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
      ← mul_assoc, hkey, one_mul]


  have hmuniv : m Set.univ = ENNReal.ofReal ((Real.sqrt (2 * Real.pi)) ^ d) := by
    rw [hmass, Measure.smul_apply, hguniv, smul_eq_mul, mul_one]
  have hpos : (0 : ℝ) < (Real.sqrt (2 * Real.pi)) ^ d :=
    pow_pos (Real.sqrt_pos.2 (by positivity)) d
  refine ⟨?_, ?_, ?_⟩
  · rw [hmuniv]
    exact (ENNReal.ofReal_pos.2 hpos).ne'
  · rw [hmuniv]
    exact ENNReal.ofReal_ne_top
  · rw [hmuniv]
    exact hmass
  /- @proof-region region.target-node.session.9a1b304e9fedfb89 end -/

end Statlib.Imported

end

