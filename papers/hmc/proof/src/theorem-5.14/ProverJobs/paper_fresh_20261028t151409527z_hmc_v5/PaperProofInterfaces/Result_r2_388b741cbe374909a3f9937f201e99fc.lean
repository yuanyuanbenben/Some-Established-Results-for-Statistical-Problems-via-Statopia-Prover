import ProverJobs.paper_fresh_20261028t151409527z_hmc_v5.ExternalNodes.Node_cfbcd4bc5578482b8771
import ProverJobs.paper_fresh_20261028t151409527z_hmc_v5.Vocabulary
import ProverJobs.paper_fresh_20261028t151409527z_hmc_v5.ProvedNodes
import ProverJobs.paper_fresh_20261028t151409527z_hmc_v5.Base

namespace PaperProofTasks.paper_fresh_20261028t151409527z_hmc_v5

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal
namespace Statlib.Imported


theorem Theorem_5_14_corrected_statement_and_replacement_proof_in_the_v5_corrigendum_Appendix_D_original_label_thm_light_Use_the
    (d : ℕ) (U : HMCState d → ℝ) (π : Measure (HMCState d)) (L : ℕ) (ε : ℝ)
    (hd : 0 < d)
    (hU_nonneg : ∀ x, 0 ≤ U x)
    (hU_diff : Differentiable ℝ U)
    (hπ_finite : IsFiniteMeasure π)
    (hπ_density : ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      π = c • volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-(U x)))))
    (h_17 : ∀ A : ℝ, ∃ R : ℝ, ∀ x : HMCState d, R < ‖x‖ → A < ‖gradient U x‖ / ‖x‖)
    (h_18 : ∃ C : ℝ, ∀ x y : HMCState d,
      3 * ‖x‖ ≤ ‖y‖ → C ≤ 3 * ‖x‖ → 3 * ‖gradient U x‖ ≤ ‖gradient U y‖)
    (h_19 : ∀ A : ℝ, ∃ R : ℝ, ∀ x y : HMCState d,
      R < ‖x‖ → (2 : ℝ) ^ L * ‖x‖ ≤ ‖y‖ →
        U x - U y - (1 / 2) * ‖x‖ ^ 2 < -A)
    (hL : 0 < L) (hε : 0 < ε) :
    ¬ GeometricallyErgodic (hmcKernel U L ε) π
:= by
  /- @proof-region region.root.fcaeb5e5ac3a begin -/
  have h_17' : ∀ M : ℝ, ∃ R, ∀ x : HMCState d, R ≤ ‖x‖ → M ≤ ‖gradient U x‖ / ‖x‖ := by
    intro M
    obtain ⟨R, hR⟩ := h_17 M
    refine ⟨R + 1, fun x hx => ?_⟩
    exact le_of_lt (hR x (lt_of_lt_of_le (by linarith) hx))
  have h_18' : ∃ C, ∀ x y : HMCState d, C ≤ 3 * ‖x‖ → 3 * ‖x‖ ≤ ‖y‖ → 3 * ‖gradient U x‖ ≤ ‖gradient U y‖ := by
    obtain ⟨C, hC⟩ := h_18
    exact ⟨C, fun x y hCx hxy => hC x y hxy hCx⟩
  have h_19' : ∀ B : ℝ, ∃ R, ∀ x y : HMCState d, R ≤ ‖x‖ → (2 : ℝ) ^ L * ‖x‖ ≤ ‖y‖ → U x - U y - (1 / 2) * ‖x‖ ^ 2 ≤ B := by
    intro B
    obtain ⟨R, hR⟩ := h_19 (-B)
    refine ⟨R + 1, fun x y hx hy => ?_⟩
    have hlt : U x - U y - (1 / 2) * ‖x‖ ^ 2 < B := by
      have h := hR x y (by linarith) hy
      simpa using h
    linarith
  have hleaf := PaperProofTasks.job_paper_53e951f48c854f4db91e6ecda697ee2b.Statlib.Imported.paper_53e951f48c854f4db91e6ecda697ee2b d U hU_nonneg hU_diff h_17' h_18' ε hε L (by omega) h_19' (1/2) (by norm_num)
  have hαeq : ∀ x p, PaperProofTasks.job_paper_53e951f48c854f4db91e6ecda697ee2b.Statlib.Imported.hmcAcceptance U ε L x p = hmcAlpha U L ε x p := by
    intro x p
    have hpos : PaperProofTasks.job_paper_53e951f48c854f4db91e6ecda697ee2b.Statlib.Imported.leapfrogPosition U ε L x p = (leapFlow U ε L (x, p)).1 := by
      unfold leapFlow PaperProofTasks.job_paper_53e951f48c854f4db91e6ecda697ee2b.Statlib.Imported.leapfrogPosition PaperProofTasks.job_paper_53e951f48c854f4db91e6ecda697ee2b.Statlib.Imported.leapfrogStep
      rfl
    have hmom : PaperProofTasks.job_paper_53e951f48c854f4db91e6ecda697ee2b.Statlib.Imported.leapfrogMomentum U ε L x p = (leapFlow U ε L (x, p)).2 := by
      unfold leapFlow PaperProofTasks.job_paper_53e951f48c854f4db91e6ecda697ee2b.Statlib.Imported.leapfrogMomentum PaperProofTasks.job_paper_53e951f48c854f4db91e6ecda697ee2b.Statlib.Imported.leapfrogStep
      rfl
    unfold hmcAlpha PaperProofTasks.job_paper_53e951f48c854f4db91e6ecda697ee2b.Statlib.Imported.hmcAcceptance
      PaperProofTasks.job_paper_53e951f48c854f4db91e6ecda697ee2b.Statlib.Imported.hmcDensity
      PaperProofTasks.job_paper_53e951f48c854f4db91e6ecda697ee2b.Statlib.Imported.kineticEnergy
    dsimp only
    rw [hpos, hmom]
    congr 1
    rw [← Real.exp_sub, ← Real.exp_add]
    congr 1
    ring
  have hα_nonneg : ∀ x p, 0 ≤ hmcAlpha U L ε x p := by
    intro x p
    unfold hmcAlpha
    exact le_min (by norm_num) (le_of_lt (Real.exp_pos _))
  have hα_le_one : ∀ x p, hmcAlpha U L ε x p ≤ 1 := by
    intro x p
    unfold hmcAlpha
    exact min_le_left _ _
  have hα_meas : ∀ x, Measurable (fun p => hmcAlpha U L ε x p) :=
    (statopia_math_node_2575820610_02f1cc53 d U L ε hU_diff).1
  have hsup : ∀ η, 0 < η → ∃ R1, ∀ x, R1 < ‖x‖ → ∀ p, ‖p‖ ≤ Real.sqrt ‖x‖ → hmcAlpha U L ε x p ≤ η := by
    intro η hη
    obtain ⟨R, hR⟩ := hleaf.2 η hη
    refine ⟨R, fun x hx p hp => ?_⟩
    rw [← hαeq x p]
    exact hR x (le_of_lt hx) p (by simpa [Real.sqrt_eq_rpow] using hp)
  rintro ⟨ρ, hρ_lt_one, M, hM_ae, hM_bound⟩
  have hρ_lt_one_real : (ρ : ℝ) < 1 := by exact_mod_cast hρ_lt_one
  have hρ_nonneg : (0 : ℝ) ≤ (ρ : ℝ) := by positivity
  obtain ⟨γ, hγ_pos, hγ_lt_one, hγ_gt⟩ : ∃ γ : ℝ, 0 < γ ∧ γ < 1 ∧ (ρ : ℝ) < 1 - γ := by
    refine ⟨(1 - (ρ : ℝ)) / 2, by linarith, by linarith, by linarith⟩
  obtain ⟨R, hR⟩ := statopia_math_node_760579675_5c0b5f8c d U L ε hα_nonneg hα_le_one hα_meas hsup γ hγ_pos hγ_lt_one
  let Rej : HMCState d → ℝ := fun x => 1 - ∫ p, hmcAlpha U L ε x p ∂(standardGaussianMomentum d)
  have hμG_prob : IsProbabilityMeasure (standardGaussianMomentum d) := by
    unfold standardGaussianMomentum
    apply MeasureTheory.Measure.isProbabilityMeasure_map
    exact (EuclideanSpace.measurableEquiv (Fin d)).symm.measurable.aemeasurable
  have hRej_range : ∀ x, 0 ≤ Rej x ∧ Rej x ≤ 1 := by
    intro x
    have hα_int : Integrable (fun p => hmcAlpha U L ε x p) (standardGaussianMomentum d) := by
      apply MeasureTheory.Integrable.of_bound (hα_meas x).aemeasurable.aestronglyMeasurable 1
      filter_upwards with p
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [hα_nonneg x p], hα_le_one x p⟩
    have h_acc_nonneg : 0 ≤ ∫ p, hmcAlpha U L ε x p ∂(standardGaussianMomentum d) :=
      MeasureTheory.integral_nonneg (fun p => hα_nonneg x p)
    have h_acc_le_one : ∫ p, hmcAlpha U L ε x p ∂(standardGaussianMomentum d) ≤ 1 := by
      have hle : ∫ p, hmcAlpha U L ε x p ∂(standardGaussianMomentum d) ≤ ∫ p, (1 : ℝ) ∂(standardGaussianMomentum d) := by
        apply MeasureTheory.integral_mono
        · exact hα_int
        · exact integrable_const 1
        · intro p
          exact hα_le_one x p
      simpa [hμG_prob.measure_univ] using hle
    exact ⟨by dsimp [Rej]; linarith, by dsimp [Rej]; linarith⟩
  have hRej_nonneg : ∀ x, 0 ≤ Rej x := fun x => (hRej_range x).1
  have hRej_le_one : ∀ x, Rej x ≤ 1 := fun x => (hRej_range x).2
  have hatom : ∀ x, π {x} = 0 := by
    intro x
    obtain ⟨c, hc0, hctop, hπeq⟩ := hπ_density
    rw [hπeq]
    haveI : NeZero d := ⟨by omega⟩
    haveI : NoAtoms (volume : Measure (HMCState d)) := by infer_instance
    simp [MeasureTheory.withDensity_apply, measure_singleton]
  obtain ⟨hP_kernel, hdom⟩ := statopia_math_node_170196137_a4c2281b d U L ε hU_diff
  have hiter : ∀ n x, ENNReal.ofReal ((Rej x) ^ n) • Measure.dirac x ≤ kernelPow (hmcKernel U L ε) n x := by
    intro n x
    have h := statopia_math_node_2756182807_18c8f00c d U L ε hdom hRej_nonneg hRej_le_one hP_kernel n x
    simpa only [Rej] using h
  have hP_prob : ∀ x, IsProbabilityMeasure (hmcKernel U L ε x) :=
    (statopia_math_node_2575820610_02f1cc53 d U L ε hU_diff).2
  have hsingleton : ∀ x, MeasurableSet ({x} : Set (HMCState d)) := by
    intro x
    exact measurableSet_singleton x
  have hTV : ∀ n x, tvDist (kernelPow (hmcKernel U L ε) n x) π ≥ (Rej x) ^ n :=
    statopia_math_node_858392357_8c0dfbe1 d U π L ε Rej hatom hiter hRej_nonneg hRej_le_one hP_prob hπ_finite hsingleton
  have hπS_pos : π {x | R < ‖x‖} > 0 := by
    obtain ⟨c, hc0, hcTop, hπeq⟩ := hπ_density
    exact statopia_math_node_2488397496_e86e6104 d hd U hU_diff.continuous.measurable π c R hc0 hcTop hπeq
  have h_inter : π ({x | R < ‖x‖} ∩ {x | M x < ⊤}) > 0 := by
    have hM_ae' : π ({x | M x < ⊤})ᶜ = 0 := by
      rw [Set.compl_setOf]
      exact MeasureTheory.ae_iff.mp hM_ae
    have h_eq := MeasureTheory.measure_inter_conull (s := {x | R < ‖x‖}) (t := {x | M x < ⊤}) hM_ae'
    rwa [h_eq]
  have h_nonempty : ({x | R < ‖x‖} ∩ {x | M x < ⊤}).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h] at h_inter
    simp at h_inter
  obtain ⟨x, hxR, hxM⟩ := h_nonempty
  have hRej_gt : (1 : ℝ) - γ ≤ Rej x := hR x hxR
  have hTV_lb : ∀ n, ENNReal.ofReal ((1 - γ) ^ n) ≤ ENNReal.ofReal (tvDist (kernelPow (hmcKernel U L ε) n x) π) := by
    intro n
    apply ENNReal.ofReal_mono
    have h1 : (1 - γ) ^ n ≤ (Rej x) ^ n := by
      gcongr
      linarith
    exact le_trans h1 (hTV n x)
  have hM_bound_x : ∀ n, ENNReal.ofReal (tvDist (kernelPow (hmcKernel U L ε) n x) π) ≤ M x * (ρ : ℝ≥0∞) ^ n := fun n => hM_bound n x
  by_cases hρ0 : (ρ : ℝ) = 0
  · have hpos : (0 : ℝ) < 1 - γ := by linarith [hγ_lt_one]
    have hρ0_nn : ρ = 0 := by exact_mod_cast hρ0
    have hρ0' : (ρ : ℝ≥0∞) = 0 := by simp [hρ0_nn]
    have hle : ENNReal.ofReal (1 - γ) ≤ 0 := by
      have h := hM_bound_x 1
      have h' := hTV_lb 1
      have hchain : ENNReal.ofReal ((1 - γ) ^ 1) ≤ M x * (ρ : ℝ≥0∞) ^ 1 := le_trans h' h
      simp only [hρ0', pow_one] at hchain
      simpa using hchain
    have hpos' : (0 : ENNReal) < ENNReal.ofReal (1 - γ) := ENNReal.ofReal_pos.mpr hpos
    exact (not_le_of_gt hpos') hle
  · have hpos : (0 : ℝ) < 1 - γ := by linarith [hγ_lt_one]
    have hρpos : (0 : ℝ) < (ρ : ℝ) := lt_of_le_of_ne (by positivity) (Ne.symm hρ0)
    let c : ℝ := (1 - γ) / (ρ : ℝ)
    have hc : 1 < c := by
      dsimp [c]
      rw [lt_div_iff₀ hρpos]
      linarith [hγ_gt]
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (M x).toReal < c ^ n := by
      have hc_tendsto : Tendsto (fun n : ℕ => c ^ n) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt hc
      have h_eventually : ∀ᶠ n in atTop, (M x).toReal < c ^ n :=
        hc_tendsto.eventually (Ioi_mem_atTop _)
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h_eventually
      exact ⟨N, hN N le_rfl⟩
    have hρn_lt_top : (ρ : ℝ≥0∞) ^ n < ⊤ := by
      rw [← ENNReal.coe_pow]
      exact ENNReal.coe_lt_top
    have hb_lt_top : M x * (ρ : ℝ≥0∞) ^ n < ⊤ := ENNReal.mul_lt_top hxM hρn_lt_top
    have hchain : ENNReal.ofReal ((1 - γ) ^ n) ≤ M x * (ρ : ℝ≥0∞) ^ n :=
      le_trans (hTV_lb n) (hM_bound_x n)
    have htoReal := ENNReal.toReal_mono (ne_of_lt hb_lt_top) hchain
    have htoReal' : (1 - γ) ^ n ≤ (M x).toReal * (ρ : ℝ) ^ n := by
      simpa [ENNReal.toReal_ofReal (pow_nonneg (le_of_lt hpos) n),
             ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hρ_nonneg] using htoReal
    have hreal : c ^ n ≤ (M x).toReal := by
      dsimp [c]
      rw [div_pow]
      rw [div_le_iff₀ (pow_pos hρpos n)]
      exact htoReal'
    linarith
  /- @proof-region region.root.fcaeb5e5ac3a end -/

end Statlib.Imported
end

-- Paper root revision 5645cc2a-40a6-41af-9d1e-317255c66daf

