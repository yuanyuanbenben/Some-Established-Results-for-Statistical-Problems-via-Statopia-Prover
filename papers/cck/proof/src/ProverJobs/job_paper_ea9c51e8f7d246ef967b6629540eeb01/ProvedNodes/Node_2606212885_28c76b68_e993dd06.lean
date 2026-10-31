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

namespace Statlib.Imported

open MeasureTheory ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_2606212885_28c76b68 : ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℕ) (hp : 0 < p)
    (X : Ω → Fin p → ℝ)
    (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (hX : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector μ X Sigma)
    (j k : Fin p),
    Integrable (fun ω => X ω j * X ω k) μ ∧
      ∫ ω, X ω j * X ω k ∂μ = (2 : ℝ)⁻¹ * (Sigma j k + Sigma k j) ∧
      covEntry μ X j k = (2 : ℝ)⁻¹ * (Sigma j k + Sigma k j) ∧
      (Sigma = Sigma.transpose → ∫ ω, X ω j * X ω k ∂μ = Sigma j k) := by
  /- @proof-region region.target-node.session.6a7a8464388e6748 begin -/
  intro Ω _ μ _ p hp X Sigma hX j k
  have hPSD : ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)).PosSemidef :=
    Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector.posSemidef_symmetrizedCovariance hX hp
  obtain ⟨hmeas, hint, hmgf⟩ := hX
  have hkey : ∀ u : Fin p → ℝ,
      ∑ i, ∑ j, u i * ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) i j * u j
        = ∑ i, ∑ j, u i * Sigma i j * u j := by
    intro u
    have hsym : ∑ i, ∑ j, u i * Sigma j i * u j = ∑ i, ∑ j, u i * Sigma i j * u j := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
    have hinner : ∀ i : Fin p,
        ∑ j, u i * ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) i j * u j
          = (2 : ℝ)⁻¹ * (∑ j, u i * Sigma i j * u j)
            + (2 : ℝ)⁻¹ * (∑ j, u i * Sigma j i * u j) := by
      intro i
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun j _ => by
        simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul]
        ring)
    have hout : ∑ i, ∑ j, u i * ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) i j * u j
        = (2 : ℝ)⁻¹ * (∑ i, ∑ j, u i * Sigma i j * u j)
          + (2 : ℝ)⁻¹ * (∑ i, ∑ j, u i * Sigma j i * u j) := by
      simp only [hinner]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [hout, hsym, ← add_mul]
    rw [show ((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) = 1 from by norm_num, one_mul]
  have hXsym : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector μ X
      ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) :=
    ⟨hmeas, hint, fun u => by rw [hmgf u, hkey u]⟩
  have hint2gen : ∀ v : NNReal, Integrable (fun x : ℝ => x ^ 2) (gaussianReal (0 : ℝ) v) := by
    intro v
    have h2 := Statlib.StatFoundation.RandomVariable.Gaussian.memLp_pow_id_gaussianReal
      (μ₀ := (0 : ℝ)) (v := v) 2 1 (by simp)
    simpa [MeasureTheory.memLp_one_iff_integrable] using h2
  have hpt : ∀ t : ℝ, ENNReal.ofReal (t ^ 2) = ‖t‖ₑ ^ 2 := by
    intro t
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow, sq_abs]
    positivity
  have hsq : ∀ v : NNReal, ∫ x : ℝ, x ^ 2 ∂(gaussianReal (0 : ℝ) v) = (v : ℝ) := by
    intro v
    have hmean : ∫ x : ℝ, id x ∂(gaussianReal (0 : ℝ) v) = 0 := by
      simpa using ProbabilityTheory.integral_id_gaussianReal (μ := (0 : ℝ)) (v := v)
    have h := ProbabilityTheory.variance_id_gaussianReal (μ := (0 : ℝ)) (v := v)
    simp only [ProbabilityTheory.variance, ProbabilityTheory.evariance] at h
    rw [hmean] at h
    have hcongr : (∫⁻ (ω : ℝ), ‖id ω - (0 : ℝ)‖ₑ ^ 2 ∂(gaussianReal (0 : ℝ) v))
        = ∫⁻ (x : ℝ), ENNReal.ofReal (x ^ 2) ∂(gaussianReal (0 : ℝ) v) := by
      apply MeasureTheory.lintegral_congr
      intro ω
      rw [hpt ω]
      simp only [id, sub_zero]
    rw [hcongr] at h
    rw [Statlib.StatFoundation.BasicAnalysis.ENNRealBridge.integral_eq_lintegral_toReal_of_nonneg
      (f := fun x : ℝ => x ^ 2) (by filter_upwards with x; positivity) (hint2gen v)]
    exact h
  have hsingleL : ∀ (a : Fin p) (c : ℝ) (f : Fin p → ℝ),
      ∑ i, (if i = a then c else 0) * f i = c * f a := by
    intro a c f
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hsingleR : ∀ (a : Fin p) (c : ℝ) (f : Fin p → ℝ),
      ∑ i, f i * (if i = a then c else 0) = f a * c := by
    intro a c f
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hφmeas : ∀ u : Fin p → ℝ, Measurable fun ω => ∑ j, u j * X ω j := by
    intro u
    have hL : Continuous fun z : Fin p → ℝ => ∑ j, u j * z j :=
      continuous_finset_sum Finset.univ
        (fun j _ => Continuous.mul continuous_const (continuous_apply j))
    exact hL.measurable.comp hmeas
  have hφs : ∀ (s : ℝ) (ω : Ω),
      ∑ i, ((if i = j then (1 : ℝ) else 0) + s * (if i = k then 1 else 0)) * X ω i
        = X ω j + s * X ω k := by
    intro s ω
    have hsplit : ∀ i : Fin p,
        ((if i = j then (1 : ℝ) else 0) + s * (if i = k then 1 else 0)) * X ω i
          = (if i = j then (1 : ℝ) else 0) * X ω i
            + s * ((if i = k then 1 else 0) * X ω i) := by
      intro i
      ring
    simp only [hsplit, Finset.sum_add_distrib]
    rw [hsingleL, ← Finset.mul_sum, hsingleL]
    ring
  have hIntSq : ∀ u : Fin p → ℝ, Integrable (fun ω => (∑ j, u j * X ω j) ^ 2) μ := by
    intro u
    have hmap := Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector.map_linearCombination
      μ X ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) hXsym hPSD u
    have hI : Integrable (fun x : ℝ => x ^ 2) (Measure.map (fun ω => ∑ j, u j * X ω j) μ) := by
      rw [hmap]
      exact hint2gen _
    have hcomp := hI.comp_measurable (hφmeas u)
    simpa only [Function.comp_apply] using hcomp
  have hsecond : ∀ u : Fin p → ℝ, ∫ ω, (∑ j, u j * X ω j) ^ 2 ∂μ
      = ∑ i, ∑ l, u i * ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) i l * u l := by
    intro u
    have hφ : Measurable fun ω => ∑ j, u j * X ω j := hφmeas u
    have hf : AEStronglyMeasurable (fun x : ℝ => x ^ 2)
        (Measure.map (fun ω => ∑ j, u j * X ω j) μ) :=
      ((continuous_id.pow 2).measurable.stronglyMeasurable).aestronglyMeasurable
    rw [← MeasureTheory.integral_map hφ.aemeasurable hf,
      Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector.map_linearCombination
        μ X ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) hXsym hPSD u, hsq]
    simp
  have hQs : ∀ s : ℝ,
      ∑ i, ∑ l, ((if i = j then (1 : ℝ) else 0) + s * (if i = k then 1 else 0))
          * ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) i l
          * ((if l = j then (1 : ℝ) else 0) + s * (if l = k then 1 else 0))
        = ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) j j
          + s * ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) j k
          + s * ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) k j
          + s ^ 2 * ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) k k := by
    intro s
    have hinner : ∀ i : Fin p,
        ∑ l, ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) i l
            * ((if l = j then (1 : ℝ) else 0) + s * (if l = k then 1 else 0))
          = ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) i j
            + s * ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) i k := by
      intro i
      have hsplit : ∀ l : Fin p,
          ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) i l
              * ((if l = j then (1 : ℝ) else 0) + s * (if l = k then 1 else 0))
            = ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) i l * (if l = j then (1 : ℝ) else 0)
              + s * (((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) i l
                * (if l = k then 1 else 0)) := by
        intro l
        ring
      simp only [hsplit, Finset.sum_add_distrib]
      rw [hsingleR, ← Finset.mul_sum, hsingleR]
      ring
    have houter : ∀ i : Fin p,
        ∑ l, ((if i = j then (1 : ℝ) else 0) + s * (if i = k then 1 else 0))
            * ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) i l
            * ((if l = j then (1 : ℝ) else 0) + s * (if l = k then 1 else 0))
          = ((if i = j then (1 : ℝ) else 0) + s * (if i = k then 1 else 0))
            * (((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) i j
              + s * ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) i k) := by
      intro i
      have hreassoc : ∀ l : Fin p,
          ((if i = j then (1 : ℝ) else 0) + s * (if i = k then 1 else 0))
              * ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) i l
              * ((if l = j then (1 : ℝ) else 0) + s * (if l = k then 1 else 0))
            = ((if i = j then (1 : ℝ) else 0) + s * (if i = k then 1 else 0))
              * (((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) i l
                * ((if l = j then (1 : ℝ) else 0) + s * (if l = k then 1 else 0))) := by
        intro l
        ring
      simp only [hreassoc]
      rw [← Finset.mul_sum, hinner i]
    have hcol : ∀ m : Fin p,
        ∑ i, ((if i = j then (1 : ℝ) else 0) + s * (if i = k then 1 else 0))
            * ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) i m
          = ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) j m
            + s * ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) k m := by
      intro m
      have hsplit : ∀ i : Fin p,
          ((if i = j then (1 : ℝ) else 0) + s * (if i = k then 1 else 0))
              * ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) i m
            = (if i = j then (1 : ℝ) else 0) * ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) i m
              + s * ((if i = k then 1 else 0)
                * ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) i m) := by
        intro i
        ring
      simp only [hsplit, Finset.sum_add_distrib]
      rw [hsingleL, ← Finset.mul_sum, hsingleL]
      ring
    have hexp : ∀ i : Fin p,
        ((if i = j then (1 : ℝ) else 0) + s * (if i = k then 1 else 0))
            * (((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) i j
              + s * ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) i k)
          = ((if i = j then (1 : ℝ) else 0) + s * (if i = k then 1 else 0))
              * ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) i j
            + s * (((if i = j then (1 : ℝ) else 0) + s * (if i = k then 1 else 0))
              * ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) i k) := by
      intro i
      ring
    simp only [houter, hexp, Finset.sum_add_distrib]
    rw [← Finset.mul_sum]
    simp only [hcol]
    ring
  have hQval : ∀ s : ℝ, ∫ ω, (X ω j + s * X ω k) ^ 2 ∂μ
      = ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) j j
        + s * ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) j k
        + s * ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) k j
        + s ^ 2 * ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) k k := by
    intro s
    have h := hsecond (fun i => (if i = j then (1 : ℝ) else 0) + s * (if i = k then 1 else 0))
    simp only [hφs s] at h
    rw [h, hQs s]
  have hSjk : ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) j k
      = (2 : ℝ)⁻¹ * (Sigma j k + Sigma k j) := by
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul]
  have hsymS : ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) k j
      = ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) j k := by
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul]
    ring
  have hφ1 : ∀ ω : Ω,
      ∑ i, ((if i = j then (1 : ℝ) else 0) + (if i = k then 1 else 0)) * X ω i
        = X ω j + X ω k := by
    intro ω
    simpa only [one_mul] using hφs 1 ω
  have hφm1 : ∀ ω : Ω,
      ∑ i, ((if i = j then (1 : ℝ) else 0) + -(if i = k then 1 else 0)) * X ω i
        = X ω j + -X ω k := by
    intro ω
    simpa only [neg_one_mul] using hφs (-1) ω
  have hInt1 : Integrable (fun ω => (X ω j + X ω k) ^ 2) μ := by
    have h := hIntSq (fun i => (if i = j then (1 : ℝ) else 0) + (if i = k then 1 else 0))
    simpa only [hφ1] using h
  have hIntm1 : Integrable (fun ω => (X ω j + -X ω k) ^ 2) μ := by
    have h := hIntSq (fun i => (if i = j then (1 : ℝ) else 0) + -(if i = k then 1 else 0))
    simpa only [hφm1] using h
  have hpt3 : ∀ ω : Ω, (X ω j + X ω k) ^ 2 - (X ω j + -X ω k) ^ 2
      = 4 * (X ω j * X ω k) := by
    intro ω
    ring
  have hdiff : ∫ ω, (X ω j + X ω k) ^ 2 ∂μ - ∫ ω, (X ω j + -X ω k) ^ 2 ∂μ
      = 4 * ∫ ω, X ω j * X ω k ∂μ := by
    rw [← MeasureTheory.integral_sub hInt1 hIntm1, ← MeasureTheory.integral_const_mul]
    simp only [hpt3]
  have hneg1sq : ((-1 : ℝ)) ^ 2 = 1 := by norm_num
  have hdiff2 : ∫ ω, (X ω j + X ω k) ^ 2 ∂μ - ∫ ω, (X ω j + -X ω k) ^ 2 ∂μ
      = 4 * ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) j k := by
    have hp := hQval 1
    have hm := hQval (-1)
    simp only [one_mul, one_pow, neg_one_mul, hneg1sq] at hp hm
    rw [hsymS] at hp hm
    rw [hp, hm]
    ring
  have hIntProd : Integrable (fun ω => X ω j * X ω k) μ := by
    have h1 : Integrable (fun ω => (X ω j + X ω k) ^ 2 - (X ω j + -X ω k) ^ 2) μ :=
      hInt1.sub hIntm1
    have h2 : Integrable
        (fun ω => (4 : ℝ)⁻¹ * ((X ω j + X ω k) ^ 2 - (X ω j + -X ω k) ^ 2)) μ :=
      h1.const_mul ((4 : ℝ)⁻¹)
    have h3 : (fun ω => X ω j * X ω k)
        = fun ω => (4 : ℝ)⁻¹ * ((X ω j + X ω k) ^ 2 - (X ω j + -X ω k) ^ 2) := by
      funext ω
      ring
    rw [h3]
    exact h2
  have hval : ∫ ω, X ω j * X ω k ∂μ = (2 : ℝ)⁻¹ * (Sigma j k + Sigma k j) := by
    have h4 : (4 : ℝ) * ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) j k
        = 4 * ∫ ω, X ω j * X ω k ∂μ := by
      rw [← hdiff2, hdiff]
    have hcancel : ((2 : ℝ)⁻¹ • (Sigma + Sigma.transpose)) j k
        = ∫ ω, X ω j * X ω k ∂μ := by
      linarith [h4]
    rw [← hcancel, hSjk]
  refine ⟨hIntProd, hval, ?_, ?_⟩
  · simpa only [covEntry] using hval
  · intro hsym
    have hkj : Sigma k j = Sigma j k := by
      simpa using congr_fun (congr_fun hsym k) j
    rw [hval, hkj]
    rw [show (2 : ℝ)⁻¹ * (Sigma j k + Sigma j k)
        = ((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) * Sigma j k from by ring]
    rw [show ((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) = 1 from by norm_num, one_mul]
  /- @proof-region region.target-node.session.6a7a8464388e6748 end -/

end Statlib.Imported

