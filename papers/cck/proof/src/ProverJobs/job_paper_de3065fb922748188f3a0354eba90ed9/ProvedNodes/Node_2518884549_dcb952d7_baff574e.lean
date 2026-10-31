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
theorem statopia_math_node_2518884549_dcb952d7 : ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : ℕ) (hq : 1 ≤ q)
    (V : Ω → Fin q → ℝ) (hV : Measurable V)
    (Sigma : Matrix (Fin q) (Fin q) ℝ) (nu : Fin q → ℝ)
    (hVar : ∀ k : Fin q, Sigma k k = 1)
    (hMean : ∀ k : Fin q, nu k = ∫ ω, V ω k ∂μ)
    (hCov : ∀ k l : Fin q, Sigma k l = ∫ ω, (V ω k - nu k) * (V ω l - nu l) ∂μ)
    (hGauss : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector μ
      (fun ω k => V ω k - nu k) Sigma)
    (hCorr : ∀ k l : Fin q, k ≠ l → Sigma k l < 1)
    (H_partition : ∀ (j : Fin q) (B : Set ℝ), MeasurableSet B →
      μ ({ω | V ω j ∈ B} ∩ {ω | ∀ k : {k : Fin q // k ≠ j}, V ω k.1 ≤ V ω j})
        = ∫⁻ z in B,
            (Statlib.Imported.gaussianVecMeasure
              (fun k : {k : Fin q // k ≠ j} => nu k.1 + (z - nu j) * Sigma k.1 j)
              (fun k l : {k : Fin q // k ≠ j} =>
                Sigma k.1 l.1 - Sigma k.1 j * Sigma l.1 j))
              {y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ z}
          ∂(Measure.map (fun ω => V ω j) μ)),
        (Measure.map (fun ω => coordMax V ω) μ) ≪ volume ∧
          Measurable (fun x : ℝ =>
            ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2)) *
              (∑ j : Fin q,
                Real.exp (nu j * x - nu j ^ 2 / 2) *
                  ENNReal.toReal
                    ((Statlib.Imported.gaussianVecMeasure
                        (fun k : {k : Fin q // k ≠ j} =>
                          nu k.1 + (x - nu j) * Sigma k.1 j)
                        (fun k l : {k : Fin q // k ≠ j} =>
                          Sigma k.1 l.1 - Sigma k.1 j * Sigma l.1 j))
                      {y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ x}))) ∧
          (∀ (s : Set ℝ), MeasurableSet s →
            (Measure.map (fun ω => coordMax V ω) μ) s =
              ∫⁻ x in s,
                ENNReal.ofReal
                  (((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2)) *
                    (∑ j : Fin q,
                      Real.exp (nu j * x - nu j ^ 2 / 2) *
                        ENNReal.toReal
                          ((Statlib.Imported.gaussianVecMeasure
                              (fun k : {k : Fin q // k ≠ j} =>
                                nu k.1 + (x - nu j) * Sigma k.1 j)
                              (fun k l : {k : Fin q // k ≠ j} =>
                                Sigma k.1 l.1 - Sigma k.1 j * Sigma l.1 j))
                            {y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ x})))
              ∂volume) := by
  /- @proof-region region.target-node.session.8754dbb9e34b2a0b begin -/
  intro Ω _instΩ μ _instμ q hq V hV Sigma nu hVar hMean hCov hGauss hCorr H_partition
  have hSigma_symm : ∀ k l : Fin q, Sigma k l = Sigma l k := by
    intro k l
    rw [hCov k l, hCov l k]
    simp only [mul_comm]
  have hsymm_mat : (2⁻¹ : ℝ) • (Sigma + Sigma.transpose) = Sigma := by
    ext k l
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, hSigma_symm l k,
      smul_eq_mul]
    ring_nf
  have hSigmaPSD : Sigma.PosSemidef := by
    have hPSD := hGauss.posSemidef_symmetrizedCovariance hq
    rw [hsymm_mat] at hPSD
    exact hPSD
  have hLaw : ∀ j : Fin q, Measure.map (fun ω => V ω j) μ = gaussianReal (nu j) 1 := by
    intro j
    let u : Fin q → ℝ := fun i => if i = j then 1 else 0
    have hvar_u : (∑ i : Fin q, ∑ l : Fin q, u i * Sigma i l * u l) = 1 := by
      rw [Finset.sum_eq_single j]
      · rw [Finset.sum_eq_single j]
        · simp [u, hVar j]
        · intro l _ hlj; simp [u, hlj]
        · intro hj; exact absurd (Finset.mem_univ j) hj
      · intro i _ hij; simp [u, hij]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    have hu : ∀ ω : Ω, V ω j - nu j = ∑ i : Fin q, u i * (V ω i - nu i) := by
      intro ω
      rw [Finset.sum_eq_single j]
      · simp [u]
      · intro i _ hij; simp [u, hij]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    have hmap := hGauss.map_linearCombination μ (fun ω k => V ω k - nu k) Sigma hSigmaPSD u
    have h0 : Measure.map (fun ω => V ω j - nu j) μ = gaussianReal 0 1 := by
      have hfe : (fun ω => V ω j - nu j) = fun ω => ∑ i : Fin q, u i * (V ω i - nu i) :=
        funext hu
      rw [hfe, hmap]
      congr 1
      exact Subtype.ext hvar_u
    have hcomp : (fun x : ℝ => x + nu j) ∘ (fun ω => V ω j - nu j) = fun ω => V ω j := by
      funext ω
      simp
    calc Measure.map (fun ω => V ω j) μ
        = Measure.map (fun x : ℝ => x + nu j) (Measure.map (fun ω => V ω j - nu j) μ) := by
          rw [Measure.map_map (by fun_prop) (by fun_prop), hcomp]
      _ = Measure.map (fun x : ℝ => x + nu j) (gaussianReal 0 1) := by rw [h0]
      _ = gaussianReal (nu j) 1 := by
            rw [ProbabilityTheory.gaussianReal_map_add_const, zero_add]
  have hPmeas : ∀ j : Fin q, Measurable (fun x : ℝ =>
        ENNReal.toReal ((gaussianVecMeasure
          (fun k : {k : Fin q // k ≠ j} => nu k.1 + (x - nu j) * Sigma k.1 j)
          (fun k l : {k : Fin q // k ≠ j} => Sigma k.1 l.1 - Sigma k.1 j * Sigma l.1 j))
          {y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ x})) := by
      intro j
      let S : Matrix {k : Fin q // k ≠ j} {k : Fin q // k ≠ j} ℝ :=
        fun k l => Sigma k.1 l.1 - Sigma k.1 j * Sigma l.1 j
      let m : ℝ → {k : Fin q // k ≠ j} → ℝ :=
        fun x k => nu k.1 + (x - nu j) * Sigma k.1 j
      change Measurable (fun x : ℝ =>
        ENNReal.toReal ((gaussianVecMeasure (m x) S) {y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ x}))
      by_cases hpsd : (((1 : ℝ) / 2) • (S + S.transpose)).PosSemidef
      · have hgm : Measurable (fun p : ℝ × ({k : Fin q // k ≠ j} → ℝ) =>
            m p.1 + Matrix.mulVec (Matrix.PosSemidef.sqrt hpsd) p.2) := by
          rw [measurable_pi_iff]
          intro k
          have h1 : Measurable (fun p : ℝ × ({k : Fin q // k ≠ j} → ℝ) => m p.1 k) := by
            simp only [m]
            exact measurable_const.add ((measurable_fst.sub measurable_const).mul measurable_const)
          have h2 : Measurable (fun p : ℝ × ({k : Fin q // k ≠ j} → ℝ) =>
              Matrix.mulVec (Matrix.PosSemidef.sqrt hpsd) p.2 k) := by
            simp only [Matrix.mulVec]
            exact Finset.measurable_sum (s := Finset.univ)
              (f := fun l (p : ℝ × ({k : Fin q // k ≠ j} → ℝ)) =>
                Matrix.PosSemidef.sqrt hpsd k l * p.2 l)
              (fun l _ => measurable_const.mul ((measurable_pi_apply l).comp measurable_snd))
          simpa only [Pi.add_apply] using h1.add h2
        set A : Set (ℝ × ({k : Fin q // k ≠ j} → ℝ)) :=
          {p | ∀ k, (m p.1 + Matrix.mulVec (Matrix.PosSemidef.sqrt hpsd) p.2) k ≤ p.1} with hAdef
        have hA : MeasurableSet A := by
          have hset : A = ⋂ k : {k : Fin q // k ≠ j},
              (fun p : ℝ × ({k : Fin q // k ≠ j} → ℝ) =>
                (m p.1 + Matrix.mulVec (Matrix.PosSemidef.sqrt hpsd) p.2) k - p.1) ⁻¹' Set.Iic 0 := by
            ext p
            simp [hAdef, Set.mem_Iic, sub_nonpos]
          rw [hset]
          exact MeasurableSet.iInter fun k =>
            MeasurableSet.preimage measurableSet_Iic
              (((measurable_pi_apply k).comp hgm).sub measurable_fst)
        have hAmeas : Measurable (fun p : ℝ × ({k : Fin q // k ≠ j} → ℝ) =>
            A.indicator (fun _ => (1 : ENNReal)) p) :=
          Measurable.indicator measurable_const hA
        haveI : SFinite (stdGaussianPi {k : Fin q // k ≠ j}) := by
          rw [show stdGaussianPi {k : Fin q // k ≠ j}
              = Measure.pi (fun _ : {k : Fin q // k ≠ j} => (gaussianReal 0 1 : Measure ℝ)) from rfl]
          infer_instance
        have hpt : ∀ x : ℝ,
            (gaussianVecMeasure (m x) S) {y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ x}
              = ∫⁻ y, A.indicator (fun _ => (1 : ENNReal)) (x, y)
                  ∂(stdGaussianPi {k : Fin q // k ≠ j}) := by
          intro x
          have hgx : Measurable (fun y : {k : Fin q // k ≠ j} → ℝ =>
              m x + Matrix.mulVec (Matrix.PosSemidef.sqrt hpsd) y) := by
            rw [measurable_pi_iff]
            intro k
            have h1 : Measurable (fun y : {k : Fin q // k ≠ j} → ℝ => m x k) :=
              measurable_const
            have h2 : Measurable (fun y : {k : Fin q // k ≠ j} → ℝ =>
                Matrix.mulVec (Matrix.PosSemidef.sqrt hpsd) y k) := by
              simp only [Matrix.mulVec]
              exact Finset.measurable_sum (s := Finset.univ)
                (f := fun l (y : {k : Fin q // k ≠ j} → ℝ) =>
                  Matrix.PosSemidef.sqrt hpsd k l * y l)
                (fun l _ => measurable_const.mul (measurable_pi_apply l))
            simpa only [Pi.add_apply] using h1.add h2
          have hsx : MeasurableSet {y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ x} := by
            have h : {y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ x}
                = ⋂ k, (fun y : {k : Fin q // k ≠ j} → ℝ => y k - x) ⁻¹' Set.Iic 0 := by
              ext y
              simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_Iic,
                sub_nonpos]
            rw [h]
            exact MeasurableSet.iInter fun k =>
              MeasurableSet.preimage measurableSet_Iic
                ((measurable_pi_apply k).sub measurable_const)
          have hsec : MeasurableSet ((fun y : {k : Fin q // k ≠ j} → ℝ =>
              m x + Matrix.mulVec (Matrix.PosSemidef.sqrt hpsd) y) ⁻¹'
                {y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ x}) :=
            MeasurableSet.preimage hsx hgx
          simp only [Statlib.Imported.gaussianVecMeasure]
          rw [dif_pos hpsd, MeasureTheory.Measure.map_apply hgx hsx,
            ← MeasureTheory.lintegral_indicator_one hsec]
          congr 1
        have hfun : (fun x : ℝ => ENNReal.toReal
              ((gaussianVecMeasure (m x) S) {y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ x}))
            = fun x => ENNReal.toReal (∫⁻ y, A.indicator (fun _ => (1 : ENNReal)) (x, y)
                ∂(stdGaussianPi {k : Fin q // k ≠ j})) := by
          funext x
          rw [hpt x]
        rw [hfun]
        exact (Measurable.lintegral_prod_right' hAmeas).ennreal_toReal
      · have hzero : ∀ x : ℝ,
            (gaussianVecMeasure (m x) S) {y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ x} = 0 := by
          intro x
          simp only [Statlib.Imported.gaussianVecMeasure]
          rw [dif_neg hpsd]
          simp
        have hfun : (fun x : ℝ => ENNReal.toReal
              ((gaussianVecMeasure (m x) S) {y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ x}))
            = fun _ => (0 : ℝ) := by
          funext x
          rw [hzero x]
          simp
        rw [hfun]
        exact measurable_const
  have hmeas : Measurable (fun x : ℝ =>
      ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2)) *
        (∑ j : Fin q,
          Real.exp (nu j * x - nu j ^ 2 / 2) *
            ENNReal.toReal
              ((Statlib.Imported.gaussianVecMeasure
                  (fun k : {k : Fin q // k ≠ j} =>
                    nu k.1 + (x - nu j) * Sigma k.1 j)
                  (fun k l : {k : Fin q // k ≠ j} =>
                    Sigma k.1 l.1 - Sigma k.1 j * Sigma l.1 j))
                {y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ x}))) := by
    have hsum : Measurable (fun x : ℝ =>
        ∑ j : Fin q,
          Real.exp (nu j * x - nu j ^ 2 / 2) *
            ENNReal.toReal
              ((gaussianVecMeasure
                  (fun k : {k : Fin q // k ≠ j} =>
                    nu k.1 + (x - nu j) * Sigma k.1 j)
                  (fun k l : {k : Fin q // k ≠ j} =>
                    Sigma k.1 l.1 - Sigma k.1 j * Sigma l.1 j))
                {y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ x})) := by
      exact Finset.measurable_sum (s := Finset.univ)
        (f := fun j x =>
          Real.exp (nu j * x - nu j ^ 2 / 2) *
            ENNReal.toReal
              ((gaussianVecMeasure
                  (fun k : {k : Fin q // k ≠ j} =>
                    nu k.1 + (x - nu j) * Sigma k.1 j)
                  (fun k l : {k : Fin q // k ≠ j} =>
                    Sigma k.1 l.1 - Sigma k.1 j * Sigma l.1 j))
                {y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ x}))
        (fun j _ => (Real.measurable_exp.comp (by fun_prop)).mul (hPmeas j))
    have hphi : Measurable (fun x : ℝ =>
        (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2)) := by
      have h1 : Measurable (fun x : ℝ => -(x ^ 2) / 2) := by fun_prop
      exact measurable_const.mul (Real.measurable_exp.comp h1)
    exact hphi.mul hsum
  have hTie : ∀ (j k : Fin q), j ≠ k → μ {ω : Ω | V ω j = V ω k} = 0 := by
    intro j k hjk
    let u : Fin q → ℝ := fun i => if i = j then 1 else if i = k then (-1 : ℝ) else 0
    have hL : ∀ f : Fin q → ℝ, (∑ i : Fin q, u i * f i) = f j - f k := by
      intro f
      have hzero : ∀ i ∈ (Finset.univ : Finset (Fin q)), i ∉ ({j, k} : Finset (Fin q)) →
          u i * f i = 0 := by
        intro i _ hi
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
        simp [u, hi.1, hi.2]
      rw [← Finset.sum_subset (Finset.subset_univ _) hzero]
      rw [Finset.sum_insert (by simp [hjk]), Finset.sum_singleton]
      simp only [u, if_true, hjk, Ne.symm hjk, if_false, one_mul, neg_mul]
      ring
    have hR : ∀ f : Fin q → ℝ, (∑ i : Fin q, f i * u i) = f j - f k := by
      intro f
      rw [← hL f]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have huvar : (∑ i : Fin q, ∑ l : Fin q, u i * Sigma i l * u l) = 2 - 2 * Sigma j k := by
      have hstep : ∀ i : Fin q, (∑ l : Fin q, u i * Sigma i l * u l)
          = u i * (Sigma i j - Sigma i k) := by
        intro i
        have e1 : (∑ l : Fin q, u i * Sigma i l * u l)
            = u i * (∑ l : Fin q, Sigma i l * u l) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun l _ => by ring
        rw [e1, hR (fun l => Sigma i l)]
      calc (∑ i : Fin q, ∑ l : Fin q, u i * Sigma i l * u l)
          = ∑ i : Fin q, u i * (Sigma i j - Sigma i k) :=
            Finset.sum_congr rfl fun i _ => hstep i
        _ = (Sigma j j - Sigma j k) - (Sigma k j - Sigma k k) := hL (fun i => Sigma i j - Sigma i k)
        _ = 2 - 2 * Sigma j k := by
            rw [hVar j, hVar k, hSigma_symm k j]
            ring
    have key : ∀ v : NNReal, 0 < (v : ℝ) → ∀ a : ℝ, gaussianReal (0 : ℝ) v {a} = 0 := by
      intro v hv a
      haveI : NoAtoms (gaussianReal (0 : ℝ) v) := by
        apply ProbabilityTheory.noAtoms_gaussianReal
        intro h0
        rw [h0] at hv
        simp at hv
      simp
    have hmap := hGauss.map_linearCombination μ (fun ω i => V ω i - nu i) Sigma hSigmaPSD u
    have hsingle : ∀ a : ℝ,
        (Measure.map (fun ω => ∑ i : Fin q, u i * (V ω i - nu i)) μ) {a} = 0 := by
      intro a
      rw [hmap]
      apply key
      show (0 : ℝ) < ∑ i : Fin q, ∑ l : Fin q, u i * Sigma i l * u l
      rw [huvar]
      have hlt := hCorr j k hjk
      linarith
    have hfmeas : Measurable (fun ω : Ω => ∑ i : Fin q, u i * (V ω i - nu i)) := by
      refine Finset.measurable_sum (s := Finset.univ)
        (f := fun i ω => u i * (V ω i - nu i)) ?_
      intro i _
      exact measurable_const.mul (((measurable_pi_apply i).comp hV).sub measurable_const)
    have hsub : {ω : Ω | V ω j = V ω k} ⊆
        (fun ω => ∑ i : Fin q, u i * (V ω i - nu i)) ⁻¹' {-(nu j - nu k)} := by
      intro ω hω
      have hω' : V ω j = V ω k := hω
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      rw [hL (fun i => V ω i - nu i), hω']
      ring
    refine MeasureTheory.Measure.mono_null hsub ?_
    rw [← MeasureTheory.Measure.map_apply hfmeas (measurableSet_singleton (-(nu j - nu k)))]
    exact hsingle _
  have hPtop : ∀ (j : Fin q) (z : ℝ),
      (gaussianVecMeasure
        (fun k : {k : Fin q // k ≠ j} => nu k.1 + (z - nu j) * Sigma k.1 j)
        (fun k l : {k : Fin q // k ≠ j} => Sigma k.1 l.1 - Sigma k.1 j * Sigma l.1 j))
        {y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ z} ≠ ⊤ := by
    intro j z
    let S : Matrix {k : Fin q // k ≠ j} {k : Fin q // k ≠ j} ℝ :=
      fun k l => Sigma k.1 l.1 - Sigma k.1 j * Sigma l.1 j
    let m : {k : Fin q // k ≠ j} → ℝ := fun k => nu k.1 + (z - nu j) * Sigma k.1 j
    change (gaussianVecMeasure m S) {y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ z} ≠ ⊤
    by_cases hpsd : (((1 : ℝ) / 2) • (S + S.transpose)).PosSemidef
    · have hmap : gaussianVecMeasure m S =
          Measure.map (fun y : {k : Fin q // k ≠ j} → ℝ =>
            m + Matrix.mulVec (Matrix.PosSemidef.sqrt hpsd) y)
            (stdGaussianPi {k : Fin q // k ≠ j}) := by
        simp only [Statlib.Imported.gaussianVecMeasure]
        rw [dif_pos hpsd]
      rw [hmap]
      have hgm : Measurable (fun y : {k : Fin q // k ≠ j} → ℝ =>
          m + Matrix.mulVec (Matrix.PosSemidef.sqrt hpsd) y) := by
        rw [measurable_pi_iff]
        intro k
        have h1 : Measurable (fun y : {k : Fin q // k ≠ j} → ℝ => m k) := measurable_const
        have h2 : Measurable (fun y : {k : Fin q // k ≠ j} → ℝ =>
            Matrix.mulVec (Matrix.PosSemidef.sqrt hpsd) y k) := by
          simp only [Matrix.mulVec]
          exact Finset.measurable_sum (s := Finset.univ)
            (f := fun l (y : {k : Fin q // k ≠ j} → ℝ) =>
              Matrix.PosSemidef.sqrt hpsd k l * y l)
            (fun l _ => measurable_const.mul (measurable_pi_apply l))
        simpa only [Pi.add_apply] using h1.add h2
      have hs : MeasurableSet {y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ z} := by
        have h : {y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ z}
            = ⋂ k, (fun y : {k : Fin q // k ≠ j} → ℝ => y k - z) ⁻¹' Set.Iic 0 := by
          ext y
          simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_Iic,
            sub_nonpos]
        rw [h]
        exact MeasurableSet.iInter fun k =>
          MeasurableSet.preimage measurableSet_Iic
            ((measurable_pi_apply k).sub measurable_const)
      rw [MeasureTheory.Measure.map_apply hgm hs]
      haveI : IsProbabilityMeasure (stdGaussianPi {k : Fin q // k ≠ j}) := by
        rw [show stdGaussianPi {k : Fin q // k ≠ j}
            = Measure.pi (fun _ : {k : Fin q // k ≠ j} => (gaussianReal 0 1 : Measure ℝ)) from rfl]
        infer_instance
      have hle : (stdGaussianPi {k : Fin q // k ≠ j})
            ((fun y : {k : Fin q // k ≠ j} → ℝ =>
              m + Matrix.mulVec (Matrix.PosSemidef.sqrt hpsd) y) ⁻¹'
                {y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ z}) ≤ 1 := by
        calc (stdGaussianPi {k : Fin q // k ≠ j})
              ((fun y : {k : Fin q // k ≠ j} → ℝ =>
                m + Matrix.mulVec (Matrix.PosSemidef.sqrt hpsd) y) ⁻¹'
                  {y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ z})
            ≤ (stdGaussianPi {k : Fin q // k ≠ j}) Set.univ :=
              MeasureTheory.measure_mono (Set.subset_univ _)
          _ = 1 := MeasureTheory.measure_univ
      exact ne_top_of_le_ne_top (by simp) hle
    · have hmap : gaussianVecMeasure m S = 0 := by
        simp only [Statlib.Imported.gaussianVecMeasure]
        rw [dif_neg hpsd]
      rw [hmap]
      simp

  have hint : ∀ (s : Set ℝ), MeasurableSet s →
      (Measure.map (fun ω => coordMax V ω) μ) s =
        ∫⁻ x in s,
          ENNReal.ofReal
            (((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2)) *
              (∑ j : Fin q,
                Real.exp (nu j * x - nu j ^ 2 / 2) *
                  ENNReal.toReal
                    ((Statlib.Imported.gaussianVecMeasure
                        (fun k : {k : Fin q // k ≠ j} =>
                          nu k.1 + (x - nu j) * Sigma k.1 j)
                        (fun k l : {k : Fin q // k ≠ j} =>
                          Sigma k.1 l.1 - Sigma k.1 j * Sigma l.1 j))
                      {y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ x})))
          ∂volume := by
    intro s hs
    have hpart : (Measure.map (fun ω => coordMax V ω) μ) s
        = ∑ j : Fin q,
            μ ({ω : Ω | V ω j ∈ s} ∩ {ω : Ω | ∀ k : {k : Fin q // k ≠ j}, V ω k.1 ≤ V ω j}) := by
      have hZmeas : Measurable (fun ω : Ω => coordMax V ω) := by
        have h : (fun ω : Ω => coordMax V ω) = fun ω => ⨆ j : Fin q, V ω j := by
          funext ω
          rfl
        rw [h]
        exact Measurable.iSup (fun j => (measurable_pi_apply j).comp hV)
      rw [MeasureTheory.Measure.map_apply hZmeas hs]
      set T : Set Ω := ⋃ (j : Fin q), ⋃ (k : {k : Fin q // k ≠ j}), {ω : Ω | V ω j = V ω k.1}
        with hTdef
      set A : Fin q → Set Ω := fun j =>
        {ω : Ω | V ω j ∈ s} ∩ {ω : Ω | ∀ k : {k : Fin q // k ≠ j}, V ω k.1 ≤ V ω j} with hAdef
      change μ ({ω : Ω | coordMax V ω ∈ s}) = ∑ j : Fin q, μ (A j)
      have hT : μ T = 0 := by
        rw [hTdef, MeasureTheory.measure_iUnion_null_iff]
        intro j
        rw [MeasureTheory.measure_iUnion_null_iff]
        intro k
        exact hTie j k.1 (Ne.symm k.2)
      have hTmeas : MeasurableSet T := by
        rw [hTdef]
        refine MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun k => ?_
        have h : {ω : Ω | V ω j = V ω k.1} = (fun ω : Ω => V ω j - V ω k.1) ⁻¹' {0} := by
          ext ω
          simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff, sub_eq_zero]
        rw [h]
        exact MeasurableSet.preimage (measurableSet_singleton 0)
          (((measurable_pi_apply j).comp hV).sub ((measurable_pi_apply k.1).comp hV))
      have hAmeas : ∀ j, MeasurableSet (A j) := by
        intro j
        rw [hAdef]
        refine MeasurableSet.inter ?_ ?_
        · exact hs.preimage ((measurable_pi_apply j).comp hV)
        · have h : {ω : Ω | ∀ k : {k : Fin q // k ≠ j}, V ω k.1 ≤ V ω j}
              = ⋂ k : {k : Fin q // k ≠ j},
                  (fun ω : Ω => V ω k.1 - V ω j) ⁻¹' Set.Iic 0 := by
            ext ω
            simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_Iic,
              sub_nonpos]
          rw [h]
          exact MeasurableSet.iInter fun k =>
            MeasurableSet.preimage measurableSet_Iic
              (((measurable_pi_apply k.1).comp hV).sub ((measurable_pi_apply j).comp hV))
      have hCdisj : Pairwise (Function.onFun Disjoint (fun j => A j \ T)) := by
        intro j l hjl
        show Disjoint (A j \ T) (A l \ T)
        rw [Set.disjoint_left]
        intro ω h1 h2
        obtain ⟨h1A, h1T⟩ := h1
        obtain ⟨h2A, _⟩ := h2
        rw [hAdef] at h1A h2A
        obtain ⟨-, h1le⟩ := h1A
        obtain ⟨-, h2le⟩ := h2A
        have h1' : V ω l ≤ V ω j := h1le ⟨l, Ne.symm hjl⟩
        have h2' : V ω j ≤ V ω l := h2le ⟨j, hjl⟩
        apply h1T
        rw [hTdef]
        exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨⟨l, Ne.symm hjl⟩, le_antisymm h2' h1'⟩⟩
      have hU : (⋃ j, A j \ T) = {ω : Ω | coordMax V ω ∈ s} \ T := by
        ext ω
        constructor
        · intro hω
          obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hω
          obtain ⟨hjA, hjT⟩ := hj
          rw [hAdef] at hjA
          obtain ⟨hj1, hj2⟩ := hjA
          refine ⟨?_, hjT⟩
          have hmax : coordMax V ω = V ω j := by
            haveI : Nonempty (Fin q) := ⟨⟨0, by omega⟩⟩
            have hbdd : BddAbove (Set.range fun i : Fin q => V ω i) := Finite.bddAbove_range _
            have hupper : coordMax V ω ≤ V ω j := by
              rw [show coordMax V ω = ⨆ i : Fin q, V ω i from rfl]
              exact ciSup_le (fun i => by
                by_cases hi : i = j
                · subst hi
                  exact le_rfl
                · exact hj2 ⟨i, hi⟩)
            have hlower : V ω j ≤ coordMax V ω := by
              rw [show coordMax V ω = ⨆ i : Fin q, V ω i from rfl]
              exact le_ciSup hbdd j
            exact le_antisymm hupper hlower
          show coordMax V ω ∈ s
          rw [hmax]
          exact hj1
        · intro hωT'
          obtain ⟨hω1, hωT⟩ := hωT'
          have hne : (Finset.univ : Finset (Fin q)).Nonempty :=
            ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
          obtain ⟨j, -, hjmax⟩ :=
            Finset.exists_max_image Finset.univ (fun j : Fin q => V ω j) hne
          have hmax : coordMax V ω = V ω j := by
            haveI : Nonempty (Fin q) := ⟨⟨0, by omega⟩⟩
            have hbdd : BddAbove (Set.range fun i : Fin q => V ω i) := Finite.bddAbove_range _
            have hupper : coordMax V ω ≤ V ω j := by
              rw [show coordMax V ω = ⨆ i : Fin q, V ω i from rfl]
              exact ciSup_le (fun i => hjmax i (Finset.mem_univ i))
            have hlower : V ω j ≤ coordMax V ω := by
              rw [show coordMax V ω = ⨆ i : Fin q, V ω i from rfl]
              exact le_ciSup hbdd j
            exact le_antisymm hupper hlower
          refine Set.mem_iUnion.mpr ⟨j, ⟨?_, hωT⟩⟩
          rw [hAdef]
          refine ⟨?_, ?_⟩
          · show V ω j ∈ s
            rw [← hmax]
            exact hω1
          · intro k
            exact hjmax k.1 (Finset.mem_univ k.1)
      calc μ ({ω : Ω | coordMax V ω ∈ s})
          = μ ({ω : Ω | coordMax V ω ∈ s} \ T) := (MeasureTheory.measure_diff_null hT).symm
        _ = μ (⋃ j, A j \ T) := by rw [hU]
        _ = ∑' j : Fin q, μ (A j \ T) :=
            MeasureTheory.measure_iUnion hCdisj (fun j => (hAmeas j).diff hTmeas)
        _ = ∑ j : Fin q, μ (A j \ T) := tsum_fintype (fun j : Fin q => μ (A j \ T))
        _ = ∑ j : Fin q, μ (A j) :=
            Finset.sum_congr rfl fun j _ => MeasureTheory.measure_diff_null hT
    have hcv : ∀ j : Fin q,
        (∫⁻ z in s,
            (Statlib.Imported.gaussianVecMeasure
              (fun k : {k : Fin q // k ≠ j} => nu k.1 + (z - nu j) * Sigma k.1 j)
              (fun k l : {k : Fin q // k ≠ j} => Sigma k.1 l.1 - Sigma k.1 j * Sigma l.1 j))
              {y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ z}
          ∂(Measure.map (fun ω => V ω j) μ))
          = ∫⁻ z in s,
              ENNReal.ofReal
                (ENNReal.toReal
                    ((Statlib.Imported.gaussianVecMeasure
                        (fun k : {k : Fin q // k ≠ j} => nu k.1 + (z - nu j) * Sigma k.1 j)
                        (fun k l : {k : Fin q // k ≠ j} =>
                          Sigma k.1 l.1 - Sigma k.1 j * Sigma l.1 j))
                      {y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ z}) *
                  gaussianPDFReal (nu j) 1 z)
              ∂volume := by
      intro j
      have hconv : (∫⁻ z in s, (Statlib.Imported.gaussianVecMeasure
            (fun k : {k : Fin q // k ≠ j} => nu k.1 + (z - nu j) * Sigma k.1 j)
            (fun k l : {k : Fin q // k ≠ j} => Sigma k.1 l.1 - Sigma k.1 j * Sigma l.1 j))
            {y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ z}
          ∂(gaussianReal (nu j) 1))
          = ∫⁻ z in s, ENNReal.ofReal (ENNReal.toReal ((Statlib.Imported.gaussianVecMeasure
            (fun k : {k : Fin q // k ≠ j} => nu k.1 + (z - nu j) * Sigma k.1 j)
            (fun k l : {k : Fin q // k ≠ j} => Sigma k.1 l.1 - Sigma k.1 j * Sigma l.1 j))
            {y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ z}))
          ∂(gaussianReal (nu j) 1) :=
        MeasureTheory.setLIntegral_congr_fun hs
          (fun z _ => (ENNReal.ofReal_toReal (hPtop j z)).symm)
      rw [hLaw j, hconv,
        ProbabilityTheory.gaussianReal_of_var_ne_zero (nu j) (by norm_num : (1 : NNReal) ≠ 0)]
      rw [MeasureTheory.setLIntegral_withDensity_eq_lintegral_mul₀ ?_ ?_ hs]
      · refine MeasureTheory.lintegral_congr (fun z => ?_)
        simp only [Pi.mul_apply]
        have hg : (0 : ℝ) < gaussianPDFReal (nu j) 1 z := by
          rw [ProbabilityTheory.gaussianPDFReal_def]
          simp only [NNReal.coe_one, mul_one]
          positivity
        rw [show gaussianPDF (nu j) 1 z = ENNReal.ofReal (gaussianPDFReal (nu j) 1 z) from rfl]
        refine Eq.trans (ENNReal.ofReal_mul hg.le).symm ?_
        congr 1
        ring
      · exact (ENNReal.measurable_ofReal.comp (measurable_gaussianPDFReal _ _)).aemeasurable
      · exact (ENNReal.measurable_ofReal.comp (hPmeas j)).aemeasurable
    have hdens : ∀ z : ℝ,
        ENNReal.ofReal
            (((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(z ^ 2) / 2)) *
              (∑ j : Fin q,
                Real.exp (nu j * z - nu j ^ 2 / 2) *
                  ENNReal.toReal
                    ((Statlib.Imported.gaussianVecMeasure
                        (fun k : {k : Fin q // k ≠ j} => nu k.1 + (z - nu j) * Sigma k.1 j)
                        (fun k l : {k : Fin q // k ≠ j} =>
                          Sigma k.1 l.1 - Sigma k.1 j * Sigma l.1 j))
                      {y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ z})))
          = ∑ j : Fin q,
              ENNReal.ofReal
                (ENNReal.toReal
                    ((Statlib.Imported.gaussianVecMeasure
                        (fun k : {k : Fin q // k ≠ j} => nu k.1 + (z - nu j) * Sigma k.1 j)
                        (fun k l : {k : Fin q // k ≠ j} =>
                          Sigma k.1 l.1 - Sigma k.1 j * Sigma l.1 j))
                      {y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ z}) *
                  gaussianPDFReal (nu j) 1 z) := by
      intro z
      have hreal : ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(z ^ 2) / 2)) *
          (∑ j : Fin q,
            Real.exp (nu j * z - nu j ^ 2 / 2) *
              ENNReal.toReal
                ((gaussianVecMeasure
                    (fun k : {k : Fin q // k ≠ j} => nu k.1 + (z - nu j) * Sigma k.1 j)
                    (fun k l : {k : Fin q // k ≠ j} =>
                      Sigma k.1 l.1 - Sigma k.1 j * Sigma l.1 j))
                  {y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ z}))
          = ∑ j : Fin q,
              ENNReal.toReal
                ((gaussianVecMeasure
                    (fun k : {k : Fin q // k ≠ j} => nu k.1 + (z - nu j) * Sigma k.1 j)
                    (fun k l : {k : Fin q // k ≠ j} =>
                      Sigma k.1 l.1 - Sigma k.1 j * Sigma l.1 j))
                  {y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ z}) *
                gaussianPDFReal (nu j) 1 z := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        simp only [ProbabilityTheory.gaussianPDFReal_def, NNReal.coe_one, mul_one]
        have hE : Real.exp (-(z ^ 2) / 2) * Real.exp (nu j * z - nu j ^ 2 / 2)
            = Real.exp (-(z - nu j) ^ 2 / 2) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [← hE]
        ring
      rw [hreal, ENNReal.ofReal_sum_of_nonneg]
      intro j _
      have h2 : (0 : ℝ) < gaussianPDFReal (nu j) 1 z := by
        rw [ProbabilityTheory.gaussianPDFReal_def]
        simp only [NNReal.coe_one, mul_one]
        positivity
      exact mul_nonneg ENNReal.toReal_nonneg h2.le
    rw [hpart, Finset.sum_congr rfl (fun j _ => by rw [H_partition j s hs, hcv j])]
    have hsumint : (∑ j : Fin q,
          ∫⁻ z in s,
            ENNReal.ofReal
              (ENNReal.toReal
                  ((Statlib.Imported.gaussianVecMeasure
                      (fun k : {k : Fin q // k ≠ j} => nu k.1 + (z - nu j) * Sigma k.1 j)
                      (fun k l : {k : Fin q // k ≠ j} =>
                        Sigma k.1 l.1 - Sigma k.1 j * Sigma l.1 j))
                    {y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ z}) *
                gaussianPDFReal (nu j) 1 z)
            ∂volume)
        = ∫⁻ z in s,
            ∑ j : Fin q,
              ENNReal.ofReal
                (ENNReal.toReal
                    ((Statlib.Imported.gaussianVecMeasure
                        (fun k : {k : Fin q // k ≠ j} => nu k.1 + (z - nu j) * Sigma k.1 j)
                        (fun k l : {k : Fin q // k ≠ j} =>
                          Sigma k.1 l.1 - Sigma k.1 j * Sigma l.1 j))
                      {y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ z}) *
                  gaussianPDFReal (nu j) 1 z)
            ∂volume := by
      rw [← MeasureTheory.lintegral_finset_sum]
      intro j _
      have h1 : Measurable (fun z : ℝ => ENNReal.toReal
          ((Statlib.Imported.gaussianVecMeasure
              (fun k : {k : Fin q // k ≠ j} => nu k.1 + (z - nu j) * Sigma k.1 j)
              (fun k l : {k : Fin q // k ≠ j} =>
                Sigma k.1 l.1 - Sigma k.1 j * Sigma l.1 j))
            {y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ z})) := hPmeas j
      have h2 : Measurable (fun z : ℝ => gaussianPDFReal (nu j) 1 z) :=
        measurable_gaussianPDFReal _ _
      exact ENNReal.measurable_ofReal.comp (h1.mul h2)
    rw [hsumint]
    refine MeasureTheory.lintegral_congr (fun z => ?_)
    exact (hdens z).symm
  have hac : Measure.map (fun ω => coordMax V ω) μ ≪ volume := by
    have hw : Measure.map (fun ω => coordMax V ω) μ
        = volume.withDensity (fun x : ℝ =>
            ENNReal.ofReal
              (((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2)) *
                (∑ j : Fin q,
                  Real.exp (nu j * x - nu j ^ 2 / 2) *
                    ENNReal.toReal
                      ((Statlib.Imported.gaussianVecMeasure
                          (fun k : {k : Fin q // k ≠ j} =>
                            nu k.1 + (x - nu j) * Sigma k.1 j)
                          (fun k l : {k : Fin q // k ≠ j} =>
                            Sigma k.1 l.1 - Sigma k.1 j * Sigma l.1 j))
                        {y : {k : Fin q // k ≠ j} → ℝ | ∀ k, y k ≤ x})))) := by
      ext s hs
      rw [hint s hs, MeasureTheory.withDensity_apply]
      exact hs
    rw [hw]
    exact MeasureTheory.withDensity_absolutelyContinuous volume _
  exact ⟨hac, hmeas, hint⟩
  /- @proof-region region.target-node.session.8754dbb9e34b2a0b end -/

end Statlib.Imported

