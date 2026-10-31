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
theorem statopia_math_node_643971460_c175e112 : ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : ℕ) (hq : 1 ≤ q)
    (Y : Ω → Fin q → ℝ) (Sigma : Matrix (Fin q) (Fin q) ℝ)
    (hGauss : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector μ Y Sigma)
    (sigmaSq : ℝ) (hsigma : 0 < sigmaSq)
    (hvar : ∀ j : Fin q, ∫ ω, (Y ω j) ^ 2 ∂μ ≤ sigmaSq)
    (hInt : Integrable (fun ω => coordMax Y ω) μ)
    (r : ℝ) (hr : 0 < r),
    μ {ω | ∫ ω', coordMax Y ω' ∂μ + r ≤ coordMax Y ω} ≤
      ENNReal.ofReal (Real.exp (-(r ^ 2) / (2 * sigmaSq))) := by
  /- @proof-region region.external.ab4a2b5357422f2f33b0d52f46b2d46b begin -/
  intro Ω instΩ μ instμ q hq Y Sigma hGauss sigmaSq hsigma hvar hInt r hr
  obtain ⟨hmeas, h2, h3⟩ := hGauss
  have hInt' : Integrable (fun ω => ⨆ j, Y ω j) μ := by simpa [coordMax] using hInt
  set S : Matrix (Fin q) (Fin q) ℝ := (2 : ℝ)⁻¹ • (Sigma + Sigma.transpose) with hS
  have hqform : ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ),
      ∑ i, ∑ j, u i * ((2 : ℝ)⁻¹ • (M + M.transpose)) i j * u j
        = ∑ i, ∑ j, u i * M i j * u j := by
    intro n M u
    have hterm : ∀ i j : Fin n,
        u i * ((2 : ℝ)⁻¹ • (M + M.transpose)) i j * u j
          = (2 : ℝ)⁻¹ * (u i * M i j * u j) + (2 : ℝ)⁻¹ * (u i * M j i * u j) := by
      intro i j
      simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul]
      ring
    have hswap : ∑ i, ∑ j, u i * M j i * u j = ∑ i, ∑ j, u i * M i j * u j := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
    simp only [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hswap]
    ring
  have hSG : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector μ Y S := by
    refine ⟨hmeas, h2, ?_⟩
    intro u
    rw [h3 u]
    rw [hS, ← hqform Sigma u]
  have hSpsd : S.PosSemidef := by
    have h :=
      Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector.posSemidef_symmetrizedCovariance
        (P := μ) (Sigma := Sigma) (X := Y) ⟨hmeas, h2, h3⟩ hq
    rwa [hS]
  have hgauss_sq : ∀ (I : ℝ) (hI : 0 ≤ I), ∫ x, x ^ 2 ∂(gaussianReal 0 ⟨I, hI⟩) = I := by
    intro I hI
    set V : ℝ := Var[id; gaussianReal 0 ⟨I, hI⟩] with hVdef
    have hmean : ∫ x, id x ∂(gaussianReal 0 ⟨I, hI⟩) = 0 := by
      simpa using ProbabilityTheory.integral_id_gaussianReal (μ := (0 : ℝ)) (v := ⟨I, hI⟩)
    have hν : gaussianReal 0 ⟨I, hI⟩ = gaussianReal 0 V.toNNReal := by
      rw [ProbabilityTheory.IsGaussian.eq_gaussianReal _
        (ProbabilityTheory.isGaussian_gaussianReal 0 ⟨I, hI⟩)]
      rw [← hVdef, hmean]
    have hnn : 0 ≤ V := by
      rw [hVdef, ProbabilityTheory.variance_eq_integral measurable_id.aemeasurable]
      exact MeasureTheory.integral_nonneg (fun x => sq_nonneg _)
    have hmgf2 : ∫ x, Real.exp (1 * x) ∂(gaussianReal 0 V.toNNReal)
        = Real.exp (1 ^ 2 * (V.toNNReal : ℝ) / 2) :=
      Statlib.StatFoundation.Statistics.Asymptotic.gaussianReal_integral_exp 1
        (V.toNNReal : ℝ) (V.toNNReal).coe_nonneg
    have hexp : Real.exp (1 ^ 2 * I / 2) = Real.exp (1 ^ 2 * (V.toNNReal : ℝ) / 2) := by
      rw [← Statlib.StatFoundation.Statistics.Asymptotic.gaussianReal_integral_exp 1 I hI, hν]
      exact hmgf2
    have hVarEq : V = I := by
      have h1 := Real.exp_injective hexp
      rw [Real.coe_toNNReal _ hnn] at h1
      linarith
    rw [hVdef] at hVarEq
    rw [ProbabilityTheory.variance_eq_integral measurable_id.aemeasurable] at hVarEq
    rw [hmean] at hVarEq
    simpa using hVarEq
  have hSdiag : ∀ j : Fin q, S j j ≤ sigmaSq := by
    intro j
    set u : Fin q → ℝ := fun k => if k = j then (1 : ℝ) else 0 with hudef
    have hYfun : (fun ω : Ω => ∑ k, u k * Y ω k) = fun ω => Y ω j := by
      funext ω
      have h1 : (∑ k, u k * Y ω k) = u j * Y ω j :=
        Finset.sum_eq_single j (fun k _ hk => by simp [hudef, hk])
          (fun h => absurd (Finset.mem_univ j) h)
      rw [h1]
      simp [hudef]
    have hquad : (∑ i, ∑ k, u i * S i k * u k) = S j j := by
      have houter : (∑ i, ∑ k, u i * S i k * u k) = ∑ k, u j * S j k * u k :=
        Finset.sum_eq_single j
          (fun i _ hi => Finset.sum_eq_zero (fun k _ => by simp [hudef, hi]))
          (fun h => absurd (Finset.mem_univ j) h)
      have hinner : (∑ k, u j * S j k * u k) = u j * S j j * u j :=
        Finset.sum_eq_single j (fun k _ hk => by simp [hudef, hk])
          (fun h => absurd (Finset.mem_univ j) h)
      rw [houter, hinner]
      simp [hudef]
    have hmeasj : Measurable fun ω : Ω => Y ω j := ((continuous_apply j).measurable).comp hmeas
    have hsq : AEStronglyMeasurable (fun x : ℝ => x ^ 2)
        (Measure.map (fun ω : Ω => Y ω j) μ) := by
      simpa [pow_two] using (measurable_id.mul measurable_id).aestronglyMeasurable
    have hstep : ∫ x, x ^ 2 ∂(Measure.map (fun ω : Ω => Y ω j) μ) = ∫ ω, (Y ω j) ^ 2 ∂μ :=
      MeasureTheory.integral_map hmeasj.aemeasurable hsq
    have hlaw :=
      Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector.map_linearCombination
        μ Y S hSG hSpsd u
    have hsecondQ : ∫ ω, (Y ω j) ^ 2 ∂μ = ∑ i, ∑ k, u i * S i k * u k := by
      rw [← hstep, ← hYfun, hlaw]
      exact hgauss_sq _ _
    have hfin : S j j = ∫ ω, (Y ω j) ^ 2 ∂μ := by
      rw [← hquad, hsecondQ]
    rw [hfin]
    exact hvar j
  by_cases h2q : 2 ≤ q
  · have hkey := Statlib.StatFoundation.Convergence.gaussianVector_max_deviation_le_exp μ q h2q Y S hSG hSpsd sigmaSq hsigma hSdiag hInt' r hr
    simpa [coordMax] using hkey
  · have hq1 : q = 1 := by omega
    subst hq1
    set A : Matrix (Fin 2) (Fin 1) ℝ := fun _ _ => (1 : ℝ) with hA
    have hmulvec : ∀ (ω : Ω) (i : Fin 2), (A.mulVec (Y ω)) i = Y ω 0 := by
      intro ω i
      simp [hA, Matrix.mulVec, dotProduct, Fin.sum_univ_one]
    have hsup1 : ∀ ω : Ω, (⨆ j : Fin 1, Y ω j) = Y ω 0 := by
      intro ω
      have hc : (fun j : Fin 1 => Y ω j) = (fun _ => Y ω 0) := by
        funext j
        fin_cases j
        rfl
      rw [hc, ciSup_const]
    have hsup2 : ∀ ω : Ω, (⨆ i : Fin 2, (A.mulVec (Y ω)) i) = Y ω 0 := by
      intro ω
      have hc : (fun i : Fin 2 => (A.mulVec (Y ω)) i) = (fun _ => Y ω 0) := by
        funext i
        exact hmulvec ω i
      rw [hc, ciSup_const]
    have hInt2 : Integrable (fun ω => ⨆ i : Fin 2, (A.mulVec (Y ω)) i) μ := by
      have hfun : (fun ω => ⨆ i : Fin 2, (A.mulVec (Y ω)) i) = fun ω => coordMax Y ω := by
        funext ω
        rw [hsup2 ω]
        simp [coordMax, hsup1 ω]
      rw [hfun]
      exact hInt
    have hlin :=
      Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector.linearImage μ Y S hSG A
    have hX'G : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector μ
        (fun ω => A.mulVec (Y ω))
        ((2 : ℝ)⁻¹ • ((A * S * A.transpose) + (A * S * A.transpose).transpose)) := by
      refine ⟨hlin.measurable, hlin.integrable_exp, ?_⟩
      intro u
      rw [hlin.mgf_eq u, hqform (A * S * A.transpose) u]
    have hTentry : ∀ i k : Fin 2, (A * S * A.transpose) i k = S 0 0 := by
      intro i k
      simp [hA, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_one]
    have hTpsd :
        ((2 : ℝ)⁻¹ • ((A * S * A.transpose) + (A * S * A.transpose).transpose)).PosSemidef := by
      have h :=
        Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector.posSemidef_symmetrizedCovariance
          hX'G (by norm_num : 1 ≤ 2)
      have hMT : ((2 : ℝ)⁻¹ • ((A * S * A.transpose) + (A * S * A.transpose).transpose)).transpose
          = (2 : ℝ)⁻¹ • ((A * S * A.transpose) + (A * S * A.transpose).transpose) := by
        simp [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_transpose, add_comm]
      have hfix :
          (2 : ℝ)⁻¹ • (((2 : ℝ)⁻¹ • ((A * S * A.transpose) + (A * S * A.transpose).transpose)) +
              ((2 : ℝ)⁻¹ • ((A * S * A.transpose) + (A * S * A.transpose).transpose)).transpose)
            = (2 : ℝ)⁻¹ • ((A * S * A.transpose) + (A * S * A.transpose).transpose) := by
        rw [hMT, smul_add, ← add_smul,
          show (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ = 1 by norm_num, one_smul]
      rw [hfix] at h
      exact h
    have hTdiag : ∀ j : Fin 2,
        ((2 : ℝ)⁻¹ • ((A * S * A.transpose) + (A * S * A.transpose).transpose)) j j ≤ sigmaSq := by
      intro j
      have hentry :
          ((2 : ℝ)⁻¹ • ((A * S * A.transpose) + (A * S * A.transpose).transpose)) j j = S 0 0 := by
        simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, hTentry, smul_eq_mul]
        ring
      rw [hentry]
      exact hSdiag 0
    have hkey :=
      Statlib.StatFoundation.Convergence.gaussianVector_max_deviation_le_exp μ 2 (by norm_num)
        (fun ω => A.mulVec (Y ω))
        ((2 : ℝ)⁻¹ • ((A * S * A.transpose) + (A * S * A.transpose).transpose))
        hX'G hTpsd sigmaSq hsigma hTdiag hInt2 r hr
    simpa [coordMax, hmulvec, hsup1] using hkey
  /- @proof-region region.external.ab4a2b5357422f2f33b0d52f46b2d46b end -/

end Statlib.Imported

