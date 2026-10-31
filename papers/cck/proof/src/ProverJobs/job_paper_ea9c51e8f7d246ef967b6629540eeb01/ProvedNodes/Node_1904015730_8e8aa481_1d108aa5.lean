import Statlib.StatFoundation.Statistics.Asymptotic.ScoreCLT
import Statlib.StatFoundation.Convergence.Resampling.GaussianMaxComparison
import Statlib.StatFoundation.Convergence.AnalysisTools.GaussianMaxAnticoncentration
import Statlib.StatFoundation.Statistics.Asymptotic.LAN
import Statlib.StatFoundation.Convergence.AnalysisTools.SmoothMax
import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import ProverJobs.job_paper_ea9c51e8f7d246ef967b6629540eeb01.Vocabulary
import ProverJobs.job_paper_ea9c51e8f7d246ef967b6629540eeb01.Base
import ProverJobs.job_paper_ea9c51e8f7d246ef967b6629540eeb01.ProvedNodes.Node_1520683596_810c9e3f_846f56fc
import ProverJobs.job_paper_ea9c51e8f7d246ef967b6629540eeb01.ExternalNodes.Node_2f43420c7b66475da0e6

namespace PaperProofTasks.job_paper_ea9c51e8f7d246ef967b6629540eeb01

open _root_.PaperProofTasks.job_paper_ea9c51e8f7d246ef967b6629540eeb01.Statlib.Imported
open MeasureTheory ProbabilityTheory

namespace Statlib.Imported

open MeasureTheory ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_1904015730_8e8aa481 : ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℕ) (hp : 0 < p)
    (X Y : Ω → Fin p → ℝ)
    (hX : Measurable X) (hY : Measurable Y)
    (hXint : ∀ j : Fin p, Integrable (fun ω => X ω j) μ)
    (hYint : ∀ j : Fin p, Integrable (fun ω => Y ω j) μ)
    (β : ℝ) (hβ : 0 < β)
    (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g)
    (hg_bdd : BddAbove (Set.range fun z : ℝ => |deriv g z|)),
    (let Fbeta : (Fin p → ℝ) → ℝ :=
        fun z => Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 z)
     let Z : ℝ → Ω → Fin p → ℝ :=
        fun t ω j => Real.sqrt t * X ω j + Real.sqrt (1 - t) * Y ω j
     let Psi : ℝ → ℝ := fun t => ∫ ω, g (Fbeta (Z t ω)) ∂μ
     let dPsi : ℝ → ℝ := fun t => (1 / 2 : ℝ) * ∑ j : Fin p,
        ∫ ω, (fderiv ℝ (fun z : Fin p → ℝ => g (Fbeta z)) (Z t ω)) (Pi.single j (1 : ℝ))
              * (t ^ (-(1 / 2) : ℝ) * X ω j - (1 - t) ^ (-(1 / 2) : ℝ) * Y ω j) ∂μ
     (∀ t ∈ Set.Icc (0 : ℝ) 1, Integrable (fun ω => g (Fbeta (Z t ω))) μ) ∧
       ContinuousOn Psi (Set.Icc (0 : ℝ) 1) ∧
         (∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt Psi (dPsi t) t) ∧
           (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ j : Fin p,
              Integrable (fun ω =>
                (fderiv ℝ (fun z : Fin p → ℝ => g (Fbeta z)) (Z t ω)) (Pi.single j (1 : ℝ))
                  * (t ^ (-(1 / 2) : ℝ) * X ω j - (1 - t) ^ (-(1 / 2) : ℝ) * Y ω j)) μ)) := by
  /- @proof-region region.target-node.session.ce20a895a0769a39 begin -/
  intro Ω _ μ _ p hp X Y hX hY hXint hYint β hβ g hg hg_bdd
  obtain ⟨C, hC⟩ := hg_bdd
  have hdiff : Differentiable ℝ g := hg.differentiable (by simp)
  have htri : ∀ a b : ℝ, |a + b| ≤ |a| + |b| := by
    intro a b
    rw [abs_le]
    exact ⟨by linarith [neg_abs_le a, neg_abs_le b], by linarith [le_abs_self a, le_abs_self b]⟩
  have hbound : ∀ x : ℝ, |g x| ≤ |g 0| + C * |x| := by
    intro x
    have hmain : |g x - g 0| ≤ C * |x| := by
      have hle : ‖g x - g 0‖ ≤ C * ‖x - 0‖ := by
        apply Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.univ)
        · intro y _
          exact hdiff.differentiableAt
        · intro y _
          rw [Real.norm_eq_abs]
          exact hC ⟨y, rfl⟩
        · exact convex_univ
        · trivial
        · trivial
      simpa [Real.norm_eq_abs, sub_zero] using hle
    rw [abs_le]
    exact ⟨by linarith [(abs_le.1 hmain).1, neg_abs_le (g 0)],
           by linarith [(abs_le.1 hmain).2, le_abs_self (g 0)]⟩
  have hnorm : ∀ z : Fin p → ℝ, ‖WithLp.toLp 2 z‖ ≤ ∑ j, |z j| := by
    intro z
    have heq : ‖WithLp.toLp 2 z‖ = Real.sqrt (∑ j, |z j| ^ 2) := by
      rw [EuclideanSpace.norm_eq]
      simp [WithLp.ofLp_toLp, Real.norm_eq_abs]
    rw [heq]
    have hS : 0 ≤ ∑ j, |z j| := Finset.sum_nonneg (fun j _ => abs_nonneg (z j))
    have hsq : ∑ j, |z j| ^ 2 ≤ (∑ j, |z j|) ^ 2 := by
      rw [pow_two, Finset.sum_mul_sum]
      apply Finset.sum_le_sum
      intro j _
      rw [pow_two]
      exact Finset.single_le_sum (f := fun k => |z j| * |z k|) (fun k _ => mul_nonneg (abs_nonneg (z j)) (abs_nonneg (z k))) (Finset.mem_univ j)
    calc Real.sqrt (∑ j, |z j| ^ 2) ≤ Real.sqrt ((∑ j, |z j|) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = ∑ j, |z j| := Real.sqrt_sq hS
  have hFbound : ∀ z : Fin p → ℝ,
      |Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 z)|
        ≤ (∑ j, |z j|) + (|Statlib.StatFoundation.Vocabulary.maxCoord (0 : EuclideanSpace ℝ (Fin p))| + |Real.log (p : ℝ) / β|) := by
    intro z
    set x : EuclideanSpace ℝ (Fin p) := WithLp.toLp 2 z with hxdef
    obtain ⟨h1, h2⟩ := Statlib.StatFoundation.Convergence.smoothMax_bounds_max_log_card p hp β hβ x
    have hcm1 : 0 ≤ Statlib.StatFoundation.Convergence.smoothMax β x - Statlib.StatFoundation.Vocabulary.maxCoord x := by linarith
    have hcm2 : Statlib.StatFoundation.Convergence.smoothMax β x - Statlib.StatFoundation.Vocabulary.maxCoord x ≤ Real.log (p : ℝ) / β := by linarith
    have hcmabs : |Statlib.StatFoundation.Convergence.smoothMax β x - Statlib.StatFoundation.Vocabulary.maxCoord x| ≤ |Real.log (p : ℝ) / β| := by
      rw [abs_of_nonneg hcm1]
      exact le_trans hcm2 (le_abs_self _)
    have hnx : ‖x‖ ≤ ∑ j, |z j| := by
      rw [hxdef]
      exact hnorm z
    have hlip : |Statlib.StatFoundation.Vocabulary.maxCoord x| ≤ ‖x‖ + |Statlib.StatFoundation.Vocabulary.maxCoord (0 : EuclideanSpace ℝ (Fin p))| := by
      have h := (lipschitzWith_iff_dist_le_mul.mp (Statlib.StatFoundation.Convergence.maxCoord_lipschitz p)) x (0 : EuclideanSpace ℝ (Fin p))
      simp only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_one, one_mul, sub_zero] at h
      calc |Statlib.StatFoundation.Vocabulary.maxCoord x|
          = |(Statlib.StatFoundation.Vocabulary.maxCoord x - Statlib.StatFoundation.Vocabulary.maxCoord (0 : EuclideanSpace ℝ (Fin p))) + Statlib.StatFoundation.Vocabulary.maxCoord (0 : EuclideanSpace ℝ (Fin p))| := by
              rw [show (Statlib.StatFoundation.Vocabulary.maxCoord x - Statlib.StatFoundation.Vocabulary.maxCoord (0 : EuclideanSpace ℝ (Fin p))) + Statlib.StatFoundation.Vocabulary.maxCoord (0 : EuclideanSpace ℝ (Fin p)) = Statlib.StatFoundation.Vocabulary.maxCoord x by ring]
        _ ≤ |Statlib.StatFoundation.Vocabulary.maxCoord x - Statlib.StatFoundation.Vocabulary.maxCoord (0 : EuclideanSpace ℝ (Fin p))| + |Statlib.StatFoundation.Vocabulary.maxCoord (0 : EuclideanSpace ℝ (Fin p))| := htri _ _
        _ ≤ ‖x‖ + |Statlib.StatFoundation.Vocabulary.maxCoord (0 : EuclideanSpace ℝ (Fin p))| := by linarith [h]
    calc |Statlib.StatFoundation.Convergence.smoothMax β x|
        = |Statlib.StatFoundation.Vocabulary.maxCoord x + (Statlib.StatFoundation.Convergence.smoothMax β x - Statlib.StatFoundation.Vocabulary.maxCoord x)| := by
            rw [show Statlib.StatFoundation.Vocabulary.maxCoord x + (Statlib.StatFoundation.Convergence.smoothMax β x - Statlib.StatFoundation.Vocabulary.maxCoord x) = Statlib.StatFoundation.Convergence.smoothMax β x by ring]
      _ ≤ |Statlib.StatFoundation.Vocabulary.maxCoord x| + |Statlib.StatFoundation.Convergence.smoothMax β x - Statlib.StatFoundation.Vocabulary.maxCoord x| := htri _ _
      _ ≤ (‖x‖ + |Statlib.StatFoundation.Vocabulary.maxCoord (0 : EuclideanSpace ℝ (Fin p))|) + |Real.log (p : ℝ) / β| := by linarith [hlip, hcmabs]
      _ ≤ ((∑ j, |z j|) + |Statlib.StatFoundation.Vocabulary.maxCoord (0 : EuclideanSpace ℝ (Fin p))|) + |Real.log (p : ℝ) / β| := by linarith [hnx]
      _ = (∑ j, |z j|) + (|Statlib.StatFoundation.Vocabulary.maxCoord (0 : EuclideanSpace ℝ (Fin p))| + |Real.log (p : ℝ) / β|) := by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht
    have hC0 : 0 ≤ C := le_trans (abs_nonneg (deriv g 0)) (hC ⟨0, rfl⟩)
    have hZle : ∀ (ω : Ω) (j : Fin p), |Real.sqrt t * X ω j + Real.sqrt (1 - t) * Y ω j| ≤ |X ω j| + |Y ω j| := by
      intro ω j
      have ht1 : Real.sqrt t ≤ 1 := by
        simpa using Real.sqrt_le_sqrt ht.2
      have h1t1 : Real.sqrt (1 - t) ≤ 1 := by
        simpa using Real.sqrt_le_sqrt (show 1 - t ≤ 1 by linarith [ht.1])
      calc |Real.sqrt t * X ω j + Real.sqrt (1 - t) * Y ω j|
          ≤ |Real.sqrt t * X ω j| + |Real.sqrt (1 - t) * Y ω j| := htri _ _
        _ = Real.sqrt t * |X ω j| + Real.sqrt (1 - t) * |Y ω j| := by
              simp only [abs_mul, abs_of_nonneg (Real.sqrt_nonneg t), abs_of_nonneg (Real.sqrt_nonneg (1 - t))]
        _ ≤ 1 * |X ω j| + 1 * |Y ω j| := by
              have h1 := mul_le_mul_of_nonneg_right ht1 (abs_nonneg (X ω j))
              have h2 := mul_le_mul_of_nonneg_right h1t1 (abs_nonneg (Y ω j))
              linarith
        _ = |X ω j| + |Y ω j| := by ring
    have hdom : ∀ (ω : Ω), |g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 (fun j => Real.sqrt t * X ω j + Real.sqrt (1 - t) * Y ω j)))|
        ≤ |g 0| + C * ((∑ j, (|X ω j| + |Y ω j|)) + (|Statlib.StatFoundation.Vocabulary.maxCoord (0 : EuclideanSpace ℝ (Fin p))| + |Real.log (p : ℝ) / β|)) := by
      intro ω
      have hF := hFbound (fun j => Real.sqrt t * X ω j + Real.sqrt (1 - t) * Y ω j)
      have hsum : (∑ j, |Real.sqrt t * X ω j + Real.sqrt (1 - t) * Y ω j|) ≤ ∑ j, (|X ω j| + |Y ω j|) :=
        Finset.sum_le_sum (fun j _ => hZle ω j)
      calc |g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 (fun j => Real.sqrt t * X ω j + Real.sqrt (1 - t) * Y ω j)))|
          ≤ |g 0| + C * |Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 (fun j => Real.sqrt t * X ω j + Real.sqrt (1 - t) * Y ω j))| := hbound _
        _ ≤ |g 0| + C * ((∑ j, |Real.sqrt t * X ω j + Real.sqrt (1 - t) * Y ω j|) + (|Statlib.StatFoundation.Vocabulary.maxCoord (0 : EuclideanSpace ℝ (Fin p))| + |Real.log (p : ℝ) / β|)) := by
              have hm := mul_le_mul_of_nonneg_left hF hC0
              linarith
        _ ≤ |g 0| + C * ((∑ j, (|X ω j| + |Y ω j|)) + (|Statlib.StatFoundation.Vocabulary.maxCoord (0 : EuclideanSpace ℝ (Fin p))| + |Real.log (p : ℝ) / β|)) := by
              have hsum' : (∑ j, |Real.sqrt t * X ω j + Real.sqrt (1 - t) * Y ω j|) + (|Statlib.StatFoundation.Vocabulary.maxCoord (0 : EuclideanSpace ℝ (Fin p))| + |Real.log (p : ℝ) / β|)
                  ≤ (∑ j, (|X ω j| + |Y ω j|)) + (|Statlib.StatFoundation.Vocabulary.maxCoord (0 : EuclideanSpace ℝ (Fin p))| + |Real.log (p : ℝ) / β|) := by linarith [hsum]
              have hm := mul_le_mul_of_nonneg_left hsum' hC0
              linarith
    have hmeas : AEStronglyMeasurable (fun ω => g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 (fun j => Real.sqrt t * X ω j + Real.sqrt (1 - t) * Y ω j)))) μ := by
      have hZw : Measurable (fun ω => fun j => Real.sqrt t * X ω j + Real.sqrt (1 - t) * Y ω j) := by
        fun_prop
      have hsm : Continuous (Statlib.StatFoundation.Convergence.smoothMax β) := (Statlib.StatFoundation.Convergence.smoothMax_def_measurable_continuous hp hβ).1
      have hgc : Measurable (fun z : Fin p → ℝ => g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 z))) := by
        have htoLp : Continuous (fun z : Fin p → ℝ => WithLp.toLp 2 z) := PiLp.continuous_toLp (2 : ENNReal) (fun _ : Fin p => ℝ)
        exact (hdiff.continuous.comp (hsm.comp htoLp)).measurable
      exact (hgc.comp hZw).aestronglyMeasurable
    have hKint : Integrable (fun ω => |g 0| + C * ((∑ j, (|X ω j| + |Y ω j|)) + (|Statlib.StatFoundation.Vocabulary.maxCoord (0 : EuclideanSpace ℝ (Fin p))| + |Real.log (p : ℝ) / β|))) μ := by
      have hXa : ∀ j : Fin p, Integrable (fun ω => |X ω j|) μ := fun j => by
        simpa [Real.norm_eq_abs] using (hXint j).norm
      have hYa : ∀ j : Fin p, Integrable (fun ω => |Y ω j|) μ := fun j => by
        simpa [Real.norm_eq_abs] using (hYint j).norm
      have hsum : Integrable (fun ω => ∑ j, (|X ω j| + |Y ω j|)) μ :=
        integrable_finset_sum Finset.univ (fun j _ => (hXa j).add (hYa j))
      have hinner : Integrable (fun ω => (∑ j, (|X ω j| + |Y ω j|)) + (|Statlib.StatFoundation.Vocabulary.maxCoord (0 : EuclideanSpace ℝ (Fin p))| + |Real.log (p : ℝ) / β|)) μ :=
        hsum.add (integrable_const _)
      have hmul : Integrable (fun ω => C * ((∑ j, (|X ω j| + |Y ω j|)) + (|Statlib.StatFoundation.Vocabulary.maxCoord (0 : EuclideanSpace ℝ (Fin p))| + |Real.log (p : ℝ) / β|))) μ :=
        hinner.const_mul C
      exact (integrable_const (|g 0|)).add hmul
    exact Integrable.mono' hKint hmeas (Filter.Eventually.of_forall (fun ω => by
      simpa [Real.norm_eq_abs] using hdom ω))
  · apply MeasureTheory.continuousOn_of_dominated (s := Set.Icc (0 : ℝ) 1)
      (bound := fun ω => |g 0| + C * ((∑ j, (|X ω j| + |Y ω j|)) + (|Statlib.StatFoundation.Vocabulary.maxCoord (0 : EuclideanSpace ℝ (Fin p))| + |Real.log (p : ℝ) / β|)))
    · intro t ht
      have hZw : Measurable (fun ω => fun j => Real.sqrt t * X ω j + Real.sqrt (1 - t) * Y ω j) := by
        fun_prop
      have hsm : Continuous (Statlib.StatFoundation.Convergence.smoothMax β) := (Statlib.StatFoundation.Convergence.smoothMax_def_measurable_continuous hp hβ).1
      have hgc : Measurable (fun z : Fin p → ℝ => g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 z))) := by
        have htoLp : Continuous (fun z : Fin p → ℝ => WithLp.toLp 2 z) := PiLp.continuous_toLp (2 : ENNReal) (fun _ : Fin p => ℝ)
        exact (hdiff.continuous.comp (hsm.comp htoLp)).measurable
      exact (hgc.comp hZw).aestronglyMeasurable
    · intro t ht
      filter_upwards with ω
      have hC0 : 0 ≤ C := le_trans (abs_nonneg (deriv g 0)) (hC ⟨0, rfl⟩)
      have ht1 : Real.sqrt t ≤ 1 := by simpa using Real.sqrt_le_sqrt ht.2
      have h1t1 : Real.sqrt (1 - t) ≤ 1 := by simpa using Real.sqrt_le_sqrt (show 1 - t ≤ 1 by linarith [ht.1])
      have hF := hFbound (fun j => Real.sqrt t * X ω j + Real.sqrt (1 - t) * Y ω j)
      have hsum : (∑ j, |Real.sqrt t * X ω j + Real.sqrt (1 - t) * Y ω j|) ≤ ∑ j, (|X ω j| + |Y ω j|) := by
        apply Finset.sum_le_sum
        intro j _
        calc |Real.sqrt t * X ω j + Real.sqrt (1 - t) * Y ω j|
            ≤ |Real.sqrt t * X ω j| + |Real.sqrt (1 - t) * Y ω j| := htri _ _
          _ = Real.sqrt t * |X ω j| + Real.sqrt (1 - t) * |Y ω j| := by
                simp only [abs_mul, abs_of_nonneg (Real.sqrt_nonneg t), abs_of_nonneg (Real.sqrt_nonneg (1 - t))]
          _ ≤ 1 * |X ω j| + 1 * |Y ω j| := by
                have h1 := mul_le_mul_of_nonneg_right ht1 (abs_nonneg (X ω j))
                have h2 := mul_le_mul_of_nonneg_right h1t1 (abs_nonneg (Y ω j))
                linarith
          _ = |X ω j| + |Y ω j| := by ring
      rw [Real.norm_eq_abs]
      calc |g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 (fun j => Real.sqrt t * X ω j + Real.sqrt (1 - t) * Y ω j)))|
          ≤ |g 0| + C * |Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 (fun j => Real.sqrt t * X ω j + Real.sqrt (1 - t) * Y ω j))| := hbound _
        _ ≤ |g 0| + C * ((∑ j, |Real.sqrt t * X ω j + Real.sqrt (1 - t) * Y ω j|) + (|Statlib.StatFoundation.Vocabulary.maxCoord (0 : EuclideanSpace ℝ (Fin p))| + |Real.log (p : ℝ) / β|)) := by
              have hm := mul_le_mul_of_nonneg_left hF hC0
              linarith
        _ ≤ |g 0| + C * ((∑ j, (|X ω j| + |Y ω j|)) + (|Statlib.StatFoundation.Vocabulary.maxCoord (0 : EuclideanSpace ℝ (Fin p))| + |Real.log (p : ℝ) / β|)) := by
              have hsum' : (∑ j, |Real.sqrt t * X ω j + Real.sqrt (1 - t) * Y ω j|) + (|Statlib.StatFoundation.Vocabulary.maxCoord (0 : EuclideanSpace ℝ (Fin p))| + |Real.log (p : ℝ) / β|) ≤ (∑ j, (|X ω j| + |Y ω j|)) + (|Statlib.StatFoundation.Vocabulary.maxCoord (0 : EuclideanSpace ℝ (Fin p))| + |Real.log (p : ℝ) / β|) := by linarith [hsum]
              have hm := mul_le_mul_of_nonneg_left hsum' hC0
              linarith
    · have hXa : ∀ j : Fin p, Integrable (fun ω => |X ω j|) μ := fun j => by
        simpa [Real.norm_eq_abs] using (hXint j).norm
      have hYa : ∀ j : Fin p, Integrable (fun ω => |Y ω j|) μ := fun j => by
        simpa [Real.norm_eq_abs] using (hYint j).norm
      have hsum : Integrable (fun ω => ∑ j, (|X ω j| + |Y ω j|)) μ :=
        integrable_finset_sum Finset.univ (fun j _ => (hXa j).add (hYa j))
      have hinner : Integrable (fun ω => (∑ j, (|X ω j| + |Y ω j|)) + (|Statlib.StatFoundation.Vocabulary.maxCoord (0 : EuclideanSpace ℝ (Fin p))| + |Real.log (p : ℝ) / β|)) μ :=
        hsum.add (integrable_const _)
      have hmul : Integrable (fun ω => C * ((∑ j, (|X ω j| + |Y ω j|)) + (|Statlib.StatFoundation.Vocabulary.maxCoord (0 : EuclideanSpace ℝ (Fin p))| + |Real.log (p : ℝ) / β|))) μ :=
        hinner.const_mul C
      exact (integrable_const (|g 0|)).add hmul
    · filter_upwards with ω
      have hsm : Continuous (Statlib.StatFoundation.Convergence.smoothMax β) := (Statlib.StatFoundation.Convergence.smoothMax_def_measurable_continuous hp hβ).1
      have hΦ : Continuous (fun z : Fin p → ℝ => g (Statlib.StatFoundation.Convergence.smoothMax β (WithLp.toLp 2 z))) := by
        have htoLp : Continuous (fun z : Fin p → ℝ => WithLp.toLp 2 z) := PiLp.continuous_toLp (2 : ENNReal) (fun _ : Fin p => ℝ)
        exact hdiff.continuous.comp (hsm.comp htoLp)
      have hZwcont : Continuous (fun t : ℝ => fun j => Real.sqrt t * X ω j + Real.sqrt (1 - t) * Y ω j) := by
        fun_prop
      exact (hΦ.comp hZwcont).continuousOn
  · intro t ht
    exact (statopia_math_node_1520683596_810c9e3f μ p hp X Y hX hY hXint hYint β hβ g hg ⟨C, hC⟩).1 t ht
  · intro t ht j
    exact (statopia_math_node_1520683596_810c9e3f μ p hp X Y hX hY hXint hYint β hβ g hg ⟨C, hC⟩).2 t ht j
  /- @proof-region region.target-node.session.ce20a895a0769a39 end -/

end Statlib.Imported

