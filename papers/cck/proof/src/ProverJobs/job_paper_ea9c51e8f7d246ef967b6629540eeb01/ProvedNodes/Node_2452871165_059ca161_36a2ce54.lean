import Statlib.StatFoundation.Statistics.Asymptotic.ScoreCLT
import Statlib.StatFoundation.Convergence.Resampling.GaussianMaxComparison
import Statlib.StatFoundation.Convergence.AnalysisTools.GaussianMaxAnticoncentration
import Statlib.StatFoundation.Statistics.Asymptotic.LAN
import Statlib.StatFoundation.Convergence.AnalysisTools.SmoothMax
import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import ProverJobs.job_paper_ea9c51e8f7d246ef967b6629540eeb01.Vocabulary
import ProverJobs.job_paper_ea9c51e8f7d246ef967b6629540eeb01.Base

namespace PaperProofTasks.job_paper_ea9c51e8f7d246ef967b6629540eeb01

open _root_.PaperProofTasks.job_paper_ea9c51e8f7d246ef967b6629540eeb01.Statlib.Imported
open MeasureTheory ProbabilityTheory
open Statlib.StatFoundation.Convergence Statlib.StatFoundation.Vocabulary

namespace Statlib.Imported

open MeasureTheory ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_2452871165_059ca161 : ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℕ) (hp : 0 < p)
    (X Y : Ω → Fin p → ℝ)
    (hX_meas : ∀ j : Fin p, Measurable fun ω => X ω j)
    (hX_int : ∀ j : Fin p, Integrable (fun ω => X ω j) μ)
    (hY_meas : ∀ j : Fin p, Measurable fun ω => Y ω j)
    (hY_int : ∀ j : Fin p, Integrable (fun ω => Y ω j) μ)
    (β : ℝ) (hβ : 0 < β)
    (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g)
    (hg1 : BddAbove (Set.range fun z : ℝ => |deriv g z|)),
    Integrable (fun ω =>
        g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 (X ω)))
          - g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 (Y ω)))) μ ∧
      Integrable (fun ω =>
        g (Statlib.StatFoundation.Vocabulary.maxCoord (WithLp.toLp 2 (X ω)))
          - g (Statlib.StatFoundation.Vocabulary.maxCoord (WithLp.toLp 2 (Y ω)))) μ ∧
        |expMaxCoordDiff μ X Y g - expSmoothMaxDiff μ X Y β g| ≤
          2 * β⁻¹ * supNormR (deriv g) * Real.log (p : ℝ) := by
  /- @proof-region region.target-node.session.8ffec5511dcdd0a5 begin -/
  intro Ω _ μ _ p hp X Y hX_meas hX_int hY_meas hY_int β hβ g hg hg1
  have hgc : Continuous g := hg.continuous
  have hM : ∀ z : ℝ, |deriv g z| ≤ supNormR (deriv g) := fun z => by
    simpa [supNormR] using le_ciSup hg1 z
  have hM0 : 0 ≤ supNormR (deriv g) := le_trans (abs_nonneg (deriv g 0)) (hM 0)
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
    have h : 1 ≤ p := Nat.succ_le_of_lt hp
    exact_mod_cast h
  have hlog0 : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg hp1
  have hL0 : 0 ≤ Real.log (p : ℝ) / β := div_nonneg hlog0 hβ.le
  have hdiff : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hlip : ∀ a b : ℝ, |g a - g b| ≤ supNormR (deriv g) * |a - b| := by
    intro a b
    have hint := Convex.norm_image_sub_le_of_norm_deriv_le (f := g) (s := Set.univ)
      (C := supNormR (deriv g))
      (fun z _ => hdiff.differentiableAt)
      (fun z _ => by simpa [Real.norm_eq_abs] using hM z)
      convex_univ (Set.mem_univ a) (Set.mem_univ b)
    simpa [Real.norm_eq_abs, abs_sub_comm] using hint
  have hgbd : ∀ x : ℝ, |g x| ≤ |g 0| + supNormR (deriv g) * |x| := by
    intro x
    have h1 : |g x - g 0| ≤ supNormR (deriv g) * |x| := by
      simpa using hlip x 0
    have e1 : g x - g 0 ≤ |g x - g 0| := le_abs_self _
    have e2 : -(g x - g 0) ≤ |g x - g 0| := by
      simpa only [abs_neg] using le_abs_self (-(g x - g 0))
    have e3 : g 0 ≤ |g 0| := le_abs_self _
    have e4 : -(g 0) ≤ |g 0| := by simpa only [abs_neg] using le_abs_self (-(g 0))
    have h3 : |g x| ≤ |g x - g 0| + |g 0| := by
      refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith
    linarith
  have hgap : ∀ z : EuclideanSpace ℝ (Fin p),
      0 ≤ smoothMax β z - maxCoord z ∧ smoothMax β z - maxCoord z ≤ Real.log (p : ℝ) / β := by
    intro z
    have h := smoothMax_bounds_max_log_card p hp β hβ z
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hmaxbd : ∀ z : EuclideanSpace ℝ (Fin p),
      |maxCoord z| ≤ ‖z‖ + |maxCoord (0 : EuclideanSpace ℝ (Fin p))| := by
    intro z
    have hz : |maxCoord z - maxCoord (0 : EuclideanSpace ℝ (Fin p))| ≤ ‖z - 0‖ :=
      maxCoord_lipschitz_ineq p z 0
    rw [sub_zero] at hz
    have e1 : maxCoord z - maxCoord (0 : EuclideanSpace ℝ (Fin p)) ≤
        |maxCoord z - maxCoord (0 : EuclideanSpace ℝ (Fin p))| := le_abs_self _
    have e2 : -(maxCoord z - maxCoord (0 : EuclideanSpace ℝ (Fin p))) ≤
        |maxCoord z - maxCoord (0 : EuclideanSpace ℝ (Fin p))| := by
      simpa only [abs_neg] using le_abs_self (-(maxCoord z - maxCoord (0 : EuclideanSpace ℝ (Fin p))))
    have e3 : maxCoord (0 : EuclideanSpace ℝ (Fin p)) ≤ |maxCoord (0 : EuclideanSpace ℝ (Fin p))| :=
      le_abs_self _
    have e4 : -(maxCoord (0 : EuclideanSpace ℝ (Fin p))) ≤ |maxCoord (0 : EuclideanSpace ℝ (Fin p))| := by
      simpa only [abs_neg] using le_abs_self (-(maxCoord (0 : EuclideanSpace ℝ (Fin p))))
    have h3 : |maxCoord z| ≤
        |maxCoord z - maxCoord (0 : EuclideanSpace ℝ (Fin p))| + |maxCoord (0 : EuclideanSpace ℝ (Fin p))| := by
      refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith
    linarith
  have hnormle : ∀ v : Fin p → ℝ,
      ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin p))‖ ≤ ∑ j : Fin p, ‖v j‖ := by
    intro v
    have hn : ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin p))‖ = √(∑ i : Fin p, ‖v i‖ ^ 2) := by
      rw [EuclideanSpace.norm_eq]
    have h2 : (0 : ℝ) ≤ ∑ i : Fin p, ‖v i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg (v i))
    have hsq : (∑ i : Fin p, ‖v i‖ ^ 2) ≤ (∑ i : Fin p, ‖v i‖) ^ 2 := by
      have h1 : ∀ i : Fin p, ‖v i‖ ^ 2 ≤ ‖v i‖ * (∑ j : Fin p, ‖v j‖) := by
        intro i
        have hi : ‖v i‖ ≤ ∑ j : Fin p, ‖v j‖ :=
          Finset.single_le_sum (f := fun j : Fin p => ‖v j‖) (fun j _ => norm_nonneg (v j)) (Finset.mem_univ i)
        have h0 : (0 : ℝ) ≤ ‖v i‖ := norm_nonneg (v i)
        nlinarith
      calc ∑ i : Fin p, ‖v i‖ ^ 2 ≤ ∑ i : Fin p, ‖v i‖ * (∑ j : Fin p, ‖v j‖) :=
            Finset.sum_le_sum (fun i _ => h1 i)
        _ = (∑ i : Fin p, ‖v i‖) * (∑ j : Fin p, ‖v j‖) := by
            rw [Finset.sum_mul]
        _ = (∑ i : Fin p, ‖v i‖) ^ 2 := by ring
    rw [hn]
    calc √(∑ i : Fin p, ‖v i‖ ^ 2) ≤ √((∑ i : Fin p, ‖v i‖) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = ∑ i : Fin p, ‖v i‖ := Real.sqrt_sq h2
  have hmaxbdv : ∀ v : Fin p → ℝ,
      |maxCoord (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin p))|
        ≤ (∑ j : Fin p, ‖v j‖) + |maxCoord (0 : EuclideanSpace ℝ (Fin p))| := by
    intro v
    have h1 := hmaxbd (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin p))
    have h2 := hnormle v
    linarith
  have hsmbd : ∀ v : Fin p → ℝ,
      |smoothMax β (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin p))|
        ≤ (∑ j : Fin p, ‖v j‖) + |maxCoord (0 : EuclideanSpace ℝ (Fin p))| + Real.log (p : ℝ) / β := by
    intro v
    obtain ⟨hb1, hb2⟩ := hgap (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin p))
    have hmax := hmaxbdv v
    have h3 := le_abs_self (maxCoord (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin p)))
    have h4 := neg_abs_le (maxCoord (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin p)))
    refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith
  have htoLp : Continuous fun v : Fin p → ℝ => (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin p)) := by
    fun_prop
  have hXtl : Measurable fun ω => (WithLp.toLp 2 (X ω) : EuclideanSpace ℝ (Fin p)) :=
    htoLp.measurable.comp (measurable_pi_iff.mpr hX_meas)
  have hYtl : Measurable fun ω => (WithLp.toLp 2 (Y ω) : EuclideanSpace ℝ (Fin p)) :=
    htoLp.measurable.comp (measurable_pi_iff.mpr hY_meas)
  have hXmax_meas : Measurable fun ω => maxCoord (WithLp.toLp 2 (X ω) : EuclideanSpace ℝ (Fin p)) :=
    (maxCoord_measurable p).comp hXtl
  have hYmax_meas : Measurable fun ω => maxCoord (WithLp.toLp 2 (Y ω) : EuclideanSpace ℝ (Fin p)) :=
    (maxCoord_measurable p).comp hYtl
  have hXsm_meas :
      Measurable fun ω => smoothMax β (WithLp.toLp 2 (X ω) : EuclideanSpace ℝ (Fin p)) :=
    ((smoothMax_def_measurable_continuous (p := p) (β := β) hp hβ).2).comp hXtl
  have hYsm_meas :
      Measurable fun ω => smoothMax β (WithLp.toLp 2 (Y ω) : EuclideanSpace ℝ (Fin p)) :=
    ((smoothMax_def_measurable_continuous (p := p) (β := β) hp hβ).2).comp hYtl
  have hXnorm : ∀ j : Fin p, Integrable (fun ω => ‖X ω j‖) μ := fun j => (hX_int j).norm
  have hYnorm : ∀ j : Fin p, Integrable (fun ω => ‖Y ω j‖) μ := fun j => (hY_int j).norm
  have hXsum : Integrable (fun ω => ∑ j : Fin p, ‖X ω j‖) μ := by
    simpa using
      integrable_finset_sum (s := Finset.univ) (f := fun j (ω : Ω) => ‖X ω j‖) (fun j _ => hXnorm j)
  have hYsum : Integrable (fun ω => ∑ j : Fin p, ‖Y ω j‖) μ := by
    simpa using
      integrable_finset_sum (s := Finset.univ) (f := fun j (ω : Ω) => ‖Y ω j‖) (fun j _ => hYnorm j)
  have hDX : Integrable (fun ω => (∑ j : Fin p, ‖X ω j‖)
      + (|maxCoord (0 : EuclideanSpace ℝ (Fin p))| + Real.log (p : ℝ) / β)) μ :=
    hXsum.add (integrable_const _)
  have hDY : Integrable (fun ω => (∑ j : Fin p, ‖Y ω j‖)
      + (|maxCoord (0 : EuclideanSpace ℝ (Fin p))| + Real.log (p : ℝ) / β)) μ :=
    hYsum.add (integrable_const _)
  have hXmax_int :
      Integrable (fun ω => ‖maxCoord (WithLp.toLp 2 (X ω) : EuclideanSpace ℝ (Fin p))‖) μ := by
    refine hDX.mono' hXmax_meas.norm.aestronglyMeasurable (Filter.Eventually.of_forall ?_)
    intro ω
    have h := hmaxbdv (X ω)
    have h1 : ‖‖maxCoord (WithLp.toLp 2 (X ω) : EuclideanSpace ℝ (Fin p))‖‖
        ≤ (∑ j : Fin p, ‖X ω j‖) + |maxCoord (0 : EuclideanSpace ℝ (Fin p))| := by
      simpa [Real.norm_eq_abs] using h
    linarith
  have hYmax_int :
      Integrable (fun ω => ‖maxCoord (WithLp.toLp 2 (Y ω) : EuclideanSpace ℝ (Fin p))‖) μ := by
    refine hDY.mono' hYmax_meas.norm.aestronglyMeasurable (Filter.Eventually.of_forall ?_)
    intro ω
    have h := hmaxbdv (Y ω)
    have h1 : ‖‖maxCoord (WithLp.toLp 2 (Y ω) : EuclideanSpace ℝ (Fin p))‖‖
        ≤ (∑ j : Fin p, ‖Y ω j‖) + |maxCoord (0 : EuclideanSpace ℝ (Fin p))| := by
      simpa [Real.norm_eq_abs] using h
    linarith
  have hXsm_int :
      Integrable (fun ω => ‖smoothMax β (WithLp.toLp 2 (X ω) : EuclideanSpace ℝ (Fin p))‖) μ := by
    refine hDX.mono' hXsm_meas.norm.aestronglyMeasurable (Filter.Eventually.of_forall ?_)
    intro ω
    have h := hsmbd (X ω)
    have h1 : ‖‖smoothMax β (WithLp.toLp 2 (X ω) : EuclideanSpace ℝ (Fin p))‖‖
        ≤ (∑ j : Fin p, ‖X ω j‖) + |maxCoord (0 : EuclideanSpace ℝ (Fin p))| + Real.log (p : ℝ) / β := by
      simpa [Real.norm_eq_abs] using h
    linarith
  have hYsm_int :
      Integrable (fun ω => ‖smoothMax β (WithLp.toLp 2 (Y ω) : EuclideanSpace ℝ (Fin p))‖) μ := by
    refine hDY.mono' hYsm_meas.norm.aestronglyMeasurable (Filter.Eventually.of_forall ?_)
    intro ω
    have h := hsmbd (Y ω)
    have h1 : ‖‖smoothMax β (WithLp.toLp 2 (Y ω) : EuclideanSpace ℝ (Fin p))‖‖
        ≤ (∑ j : Fin p, ‖Y ω j‖) + |maxCoord (0 : EuclideanSpace ℝ (Fin p))| + Real.log (p : ℝ) / β := by
      simpa [Real.norm_eq_abs] using h
    linarith
  have hInt_g : ∀ (h : Ω → ℝ), Measurable h → Integrable (fun ω => ‖h ω‖) μ →
      Integrable (fun ω => g (h ω)) μ := by
    intro h hh hhi
    have hdom : Integrable (fun ω => |g 0| + supNormR (deriv g) * ‖h ω‖) μ :=
      (integrable_const (|g 0|)).add (hhi.const_mul (supNormR (deriv g)))
    refine hdom.mono' ((hgc.measurable.comp hh).aestronglyMeasurable) (Filter.Eventually.of_forall ?_)
    intro ω
    simpa [Real.norm_eq_abs] using hgbd (h ω)
  have hXg_max :
      Integrable (fun ω => g (maxCoord (WithLp.toLp 2 (X ω) : EuclideanSpace ℝ (Fin p)))) μ :=
    hInt_g _ hXmax_meas hXmax_int
  have hYg_max :
      Integrable (fun ω => g (maxCoord (WithLp.toLp 2 (Y ω) : EuclideanSpace ℝ (Fin p)))) μ :=
    hInt_g _ hYmax_meas hYmax_int
  have hXg_sm :
      Integrable (fun ω => g (smoothMax β (WithLp.toLp 2 (X ω) : EuclideanSpace ℝ (Fin p)))) μ :=
    hInt_g _ hXsm_meas hXsm_int
  have hYg_sm :
      Integrable (fun ω => g (smoothMax β (WithLp.toLp 2 (Y ω) : EuclideanSpace ℝ (Fin p)))) μ :=
    hInt_g _ hYsm_meas hYsm_int
  have hz : ∀ z : EuclideanSpace ℝ (Fin p),
      |g (maxCoord z) - g (smoothMax β z)| ≤ supNormR (deriv g) * (Real.log (p : ℝ) / β) := by
    intro z
    obtain ⟨h1, h2⟩ := hgap z
    have hd : |maxCoord z - smoothMax β z| ≤ Real.log (p : ℝ) / β := by
      rw [abs_of_nonpos (by linarith)]
      linarith
    calc |g (maxCoord z) - g (smoothMax β z)|
        ≤ supNormR (deriv g) * |maxCoord z - smoothMax β z| := hlip _ _
      _ ≤ supNormR (deriv g) * (Real.log (p : ℝ) / β) := mul_le_mul_of_nonneg_left hd hM0
  refine ⟨hXg_sm.sub hYg_sm, hXg_max.sub hYg_max, ?_⟩
  have key : ∀ (A B C D : Ω → ℝ), Integrable A μ → Integrable B μ → Integrable C μ →
      Integrable D μ →
      (∀ ω, |A ω - B ω| ≤ supNormR (deriv g) * (Real.log (p : ℝ) / β)) →
      (∀ ω, |C ω - D ω| ≤ supNormR (deriv g) * (Real.log (p : ℝ) / β)) →
      |(∫ ω, (A ω - C ω) ∂μ) - ∫ ω, (B ω - D ω) ∂μ| ≤
        2 * (supNormR (deriv g) * (Real.log (p : ℝ) / β)) := by
    intro A B C D hA hB hC hD hAB hCD
    have hsub1 : ∫ ω, (A ω - C ω) ∂μ - ∫ ω, (B ω - D ω) ∂μ
        = ∫ ω, (A ω - B ω) - (C ω - D ω) ∂μ := by
      rw [← integral_sub (f := fun ω => A ω - C ω) (g := fun ω => B ω - D ω)
        (hA.sub hC) (hB.sub hD)]
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by
        ring)
    have h2 : Integrable (fun ω => (A ω - B ω) - (C ω - D ω)) μ := (hA.sub hB).sub (hC.sub hD)
    have h3 : Integrable (fun ω => |(A ω - B ω) - (C ω - D ω)|) μ := by
      simpa [Real.norm_eq_abs] using h2.norm
    have h4 : ∀ ω, |(A ω - B ω) - (C ω - D ω)| ≤
        2 * (supNormR (deriv g) * (Real.log (p : ℝ) / β)) := by
      intro ω
      have hx := hAB ω
      have hy := hCD ω
      have e1 : A ω - B ω ≤ |A ω - B ω| := le_abs_self _
      have e2 : -(A ω - B ω) ≤ |A ω - B ω| := by
        simpa only [abs_neg] using le_abs_self (-(A ω - B ω))
      have e3 : C ω - D ω ≤ |C ω - D ω| := le_abs_self _
      have e4 : -(C ω - D ω) ≤ |C ω - D ω| := by
        simpa only [abs_neg] using le_abs_self (-(C ω - D ω))
      have htri : |(A ω - B ω) - (C ω - D ω)| ≤ |A ω - B ω| + |C ω - D ω| := by
        refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith
      linarith
    rw [hsub1]
    calc |∫ ω, (A ω - B ω) - (C ω - D ω) ∂μ|
        ≤ ∫ ω, |(A ω - B ω) - (C ω - D ω)| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ ω, 2 * (supNormR (deriv g) * (Real.log (p : ℝ) / β)) ∂μ :=
          integral_mono h3 (integrable_const _) h4
      _ = 2 * (supNormR (deriv g) * (Real.log (p : ℝ) / β)) := by
          rw [integral_const]
          simp
  have keyapp := key (fun ω => g (maxCoord (WithLp.toLp 2 (X ω) : EuclideanSpace ℝ (Fin p))))
    (fun ω => g (smoothMax β (WithLp.toLp 2 (X ω) : EuclideanSpace ℝ (Fin p))))
    (fun ω => g (maxCoord (WithLp.toLp 2 (Y ω) : EuclideanSpace ℝ (Fin p))))
    (fun ω => g (smoothMax β (WithLp.toLp 2 (Y ω) : EuclideanSpace ℝ (Fin p))))
    hXg_max hXg_sm hYg_max hYg_sm
    (fun ω => hz (WithLp.toLp 2 (X ω) : EuclideanSpace ℝ (Fin p)))
    (fun ω => hz (WithLp.toLp 2 (Y ω) : EuclideanSpace ℝ (Fin p)))
  simp only [expMaxCoordDiff, expSmoothMaxDiff]
  refine le_trans keyapp (le_of_eq ?_)
  rw [div_eq_mul_inv]
  ring
  /- @proof-region region.target-node.session.8ffec5511dcdd0a5 end -/

end Statlib.Imported

