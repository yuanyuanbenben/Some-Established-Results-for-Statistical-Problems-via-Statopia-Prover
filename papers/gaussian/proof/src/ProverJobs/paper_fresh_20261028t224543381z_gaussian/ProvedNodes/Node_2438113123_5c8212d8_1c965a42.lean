import Statlib.HighDim.MatrixAnalysis.AndoVocabulary
import ProverJobs.paper_fresh_20261028t224543381z_gaussian.Vocabulary
import ProverJobs.paper_fresh_20261028t224543381z_gaussian.Base
import ProverJobs.paper_fresh_20261028t224543381z_gaussian.ProvedNodes.Node_4002638969_66ac1fc1_fade728f

namespace PaperProofTasks.paper_fresh_20261028t224543381z_gaussian
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open _root_.PaperProofTasks.paper_fresh_20261028t224543381z_gaussian.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace Statlib.Imported


set_option autoImplicit false in
theorem statopia_math_node_2438113123_5c8212d8 : ∀ (m : ℕ)
    (Sigma : Matrix (Fin m) (Fin m) ℝ) (hSigma : Sigma.PosSemidef)
    (nu : Measure (Fin m → ℝ))
    (hprob : IsProbabilityMeasure nu) (hgauss : IsGaussian nu)
    (hint1 : ∀ j : Fin m, Integrable (fun s : Fin m → ℝ => s j) nu)
    (hmean : ∀ j : Fin m, ∫ s, s j ∂nu = 0)
    (hint2 : ∀ k l : Fin m, Integrable (fun s : Fin m → ℝ => s k * s l) nu)
    (hcov : ∀ k l : Fin m, ∫ s, s k * s l ∂nu = Sigma k l),
    nu = (Measure.pi (fun _ : Fin m => gaussianReal 0 1)).map
      (fun w => Matrix.mulVec (Matrix.PosSemidef.sqrt hSigma) w) := by
  /- @proof-region region.target-node.session.535f29bc7b80d23f begin -/
  intro m Sigma hSigma nu hprob hgauss hint1 hmean hint2 hcov
  haveI := hprob
  haveI := hgauss
  rcases Nat.eq_zero_or_pos m with hm0 | hm
  · subst hm0
    haveI hsubI : Subsingleton (Fin 0 → ℝ) := ⟨fun x _ => by funext i; exact i.elim0⟩
    have key : ∀ μ ν : Measure (Fin 0 → ℝ), μ Set.univ = 1 → ν Set.univ = 1 → μ = ν := by
      intro μ ν hμ hν
      refine MeasureTheory.Measure.ext (fun s _ => ?_)
      by_cases hs : s.Nonempty
      · obtain ⟨x, hx⟩ := hs
        have hsu : s = Set.univ := Set.eq_univ_of_forall (fun y => by
          have hxy : y = x := Subsingleton.elim y x
          rw [hxy]
          exact hx)
        rw [hsu, hμ, hν]
      · rw [Set.not_nonempty_iff_eq_empty.mp hs, measure_empty, measure_empty]
    have htarget : ((Measure.pi (fun _ : Fin 0 => gaussianReal 0 1)).map
        (fun w => Matrix.mulVec (Matrix.PosSemidef.sqrt hSigma) w)) Set.univ = 1 := by
      have hf : (fun w : Fin 0 → ℝ => Matrix.mulVec (Matrix.PosSemidef.sqrt hSigma) w)
          = fun _ => (fun i : Fin 0 => i.elim0) := by
        funext w
        exact Subsingleton.elim _ _
      rw [hf, MeasureTheory.Measure.map_apply measurable_const MeasurableSet.univ,
        Set.preimage_univ]
      simp
    exact key nu _ hprob.measure_univ htarget
  · have hPSD1 : (1 : Matrix (Fin m) (Fin m) ℝ).PosSemidef := Matrix.PosSemidef.one
    have hICGV1 : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector
        (Measure.pi (fun _ : Fin m => gaussianReal 0 1)) (fun ω => ω)
        (1 : Matrix (Fin m) (Fin m) ℝ) := by
      have h := Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector_isCenteredGaussianVector
        hm (1 : Matrix (Fin m) (Fin m) ℝ) hPSD1
      convert h using 2
      simp [Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector]
    have p1 : (Matrix.PosSemidef.sqrt hSigma : Matrix (Fin m) (Fin m) ℝ) = hSigma.left.cfc Real.sqrt := by
      first
        | rfl
        | simp [Matrix.PosSemidef.sqrt, Matrix.IsHermitian.cfc]
    have hB2 : CFC.sqrt Sigma * CFC.sqrt Sigma = Sigma := Matrix.PosSemidef.sqrt_mul_self hSigma
    have hAform : (Matrix.PosSemidef.sqrt hSigma : Matrix (Fin m) (Fin m) ℝ) =
        (hSigma.left.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ) *
          Matrix.diagonal (Real.sqrt ∘ hSigma.left.eigenvalues) *
          star (hSigma.left.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ) := by
      rw [p1]
      simp [Matrix.IsHermitian.cfc]
    have hSform : Sigma =
        ((Unitary.conjStarAlgAut ℝ (Matrix (Fin m) (Fin m) ℝ)) hSigma.left.eigenvectorUnitary)
          (Matrix.diagonal (RCLike.ofReal ∘ hSigma.left.eigenvalues)) :=
      Matrix.IsHermitian.spectral_theorem hSigma.left
    have hSprod : Sigma =
        (hSigma.left.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ) *
          Matrix.diagonal (hSigma.left.eigenvalues) *
          star (hSigma.left.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ) := by
      have hself : IsSelfAdjoint Sigma := by
        simpa [Matrix.IsHermitian] using hSigma.left
      conv_lhs => rw [← cfc_id ℝ Sigma hself]
      rw [Matrix.IsHermitian.cfc_eq hSigma.left id]
      simp [Matrix.IsHermitian.cfc]
    have hGram : (Matrix.PosSemidef.sqrt hSigma : Matrix (Fin m) (Fin m) ℝ) *
        (Matrix.PosSemidef.sqrt hSigma).transpose = Sigma := by
      have hstT : ∀ M : Matrix (Fin m) (Fin m) ℝ, M.transpose = star M := fun M =>
        (Matrix.conjTranspose_eq_transpose_of_trivial M).symm
      have hAt : (Matrix.PosSemidef.sqrt hSigma : Matrix (Fin m) (Fin m) ℝ).transpose =
          (Matrix.PosSemidef.sqrt hSigma : Matrix (Fin m) (Fin m) ℝ) := by
        rw [hAform, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.diagonal_transpose,
          hstT (star ↑(hSigma.left.eigenvectorUnitary)), hstT ↑(hSigma.left.eigenvectorUnitary)]
        simp only [mul_assoc, star_star]
      have hAsq : (Matrix.PosSemidef.sqrt hSigma : Matrix (Fin m) (Fin m) ℝ) *
          (Matrix.PosSemidef.sqrt hSigma : Matrix (Fin m) (Fin m) ℝ) = Sigma := by
        have hUU : star (hSigma.left.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ) *
            (hSigma.left.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ) = 1 :=
          Matrix.UnitaryGroup.star_mul_self hSigma.left.eigenvectorUnitary
        have hDD : Matrix.diagonal (Real.sqrt ∘ hSigma.left.eigenvalues) *
            Matrix.diagonal (Real.sqrt ∘ hSigma.left.eigenvalues) =
            Matrix.diagonal (hSigma.left.eigenvalues) := by
          rw [Matrix.diagonal_mul_diagonal]
          exact congrArg Matrix.diagonal (funext fun i =>
            Real.mul_self_sqrt (Matrix.PosSemidef.eigenvalues_nonneg hSigma i))
        rw [hAform]
        set U : Matrix (Fin m) (Fin m) ℝ := (hSigma.left.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ)
        set D : Matrix (Fin m) (Fin m) ℝ := Matrix.diagonal (Real.sqrt ∘ hSigma.left.eigenvalues)
        set Dl : Matrix (Fin m) (Fin m) ℝ := Matrix.diagonal (hSigma.left.eigenvalues)
        have hUU' : star U * U = 1 := hUU
        have hDD' : D * D = Dl := hDD
        rw [mul_assoc (U * D) (star U) ((U * D) * star U), mul_assoc U D (star U),
          ← mul_assoc (star U) U (D * star U), hUU', one_mul, mul_assoc U D (D * star U),
          ← mul_assoc D D (star U), hDD', ← mul_assoc U Dl (star U)]
        exact hSprod.symm
      rw [hAt, hAsq]
    have hGaussG : IsGaussian (Measure.pi (fun _ : Fin m => gaussianReal 0 1)) := by
      have h := Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector.pushforward_isGaussian
        (Measure.pi (fun _ : Fin m => gaussianReal 0 1)) (fun ω => ω)
        (1 : Matrix (Fin m) (Fin m) ℝ) hICGV1 hPSD1
      simpa using h
    have hGcoord : ∀ i : Fin m,
        ∫ w : Fin m → ℝ, w i ∂(Measure.pi (fun _ : Fin m => gaussianReal 0 1)) = 0 := by
      intro i
      have hlaw := Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector.map_linearCombination
        (Measure.pi (fun _ : Fin m => gaussianReal 0 1)) (fun ω => ω)
        (1 : Matrix (Fin m) (Fin m) ℝ) hICGV1 hPSD1 (fun j => if j = i then 1 else 0)
      have hfun : (fun w : Fin m → ℝ => ∑ j, (if j = i then 1 else 0) * w j) = fun w => w i := by
        funext w
        simp
      rw [hfun] at hlaw
      have h1 : ∫ y : ℝ, y ∂(Measure.map (fun w : Fin m → ℝ => w i)
            (Measure.pi (fun _ : Fin m => gaussianReal 0 1)))
          = ∫ w : Fin m → ℝ, w i ∂(Measure.pi (fun _ : Fin m => gaussianReal 0 1)) :=
        by
          refine MeasureTheory.integral_map (f := fun y : ℝ => y) ?_ ?_
          · first
              | exact (continuous_apply i).measurable.aemeasurable
              | exact measurable_pi_apply i
          · exact measurable_id.aestronglyMeasurable
      rw [hlaw, ProbabilityTheory.integral_id_gaussianReal] at h1
      exact h1.symm
    have hGaussT : IsGaussian ((Measure.pi (fun _ : Fin m => gaussianReal 0 1)).map
        (fun w => Matrix.mulVec (Matrix.PosSemidef.sqrt hSigma) w)) := by
      have hlin := Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector.linearImage
        (Measure.pi (fun _ : Fin m => gaussianReal 0 1)) (fun ω => ω)
        (1 : Matrix (Fin m) (Fin m) ℝ) hICGV1 (Matrix.PosSemidef.sqrt hSigma)
      have hPSD : ((Matrix.PosSemidef.sqrt hSigma : Matrix (Fin m) (Fin m) ℝ) * 1 *
          (Matrix.PosSemidef.sqrt hSigma).transpose).PosSemidef := by
        simpa [Matrix.mul_one] using
          Matrix.posSemidef_self_mul_conjTranspose (Matrix.PosSemidef.sqrt hSigma)
      exact Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector.pushforward_isGaussian
        (Measure.pi (fun _ : Fin m => gaussianReal 0 1))
        (fun w => Matrix.mulVec (Matrix.PosSemidef.sqrt hSigma) w) _ hlin hPSD
    haveI := hGaussT
    have hmean_eq : ∫ x, id x ∂nu = ∫ x, id x ∂((Measure.pi (fun _ : Fin m => gaussianReal 0 1)).map
        (fun w => Matrix.mulVec (Matrix.PosSemidef.sqrt hSigma) w)) := by
      have hν : ∫ x, id x ∂nu = 0 := by
        funext i
        let L : (Fin m → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
        have hL : ∫ x, L x ∂nu = L (∫ x, id x ∂nu) :=
          ProbabilityTheory.IsGaussian.integral_dual (μ := nu) L
        show L (∫ x, id x ∂nu) = 0
        rw [← hL]
        exact hmean i
      have hT : ∫ x, id x ∂((Measure.pi (fun _ : Fin m => gaussianReal 0 1)).map
          (fun w => Matrix.mulVec (Matrix.PosSemidef.sqrt hSigma) w)) = 0 := by
        haveI hGG : IsGaussian (Measure.pi (fun _ : Fin m => gaussianReal 0 1)) := hGaussG
        have hInt : Integrable id (Measure.pi (fun _ : Fin m => gaussianReal 0 1)) :=
          MeasureTheory.memLp_one_iff_integrable.mp
            (ProbabilityTheory.IsGaussian.memLp_id (μ := Measure.pi (fun _ : Fin m => gaussianReal 0 1))
              1 (by simp))
        have hmass : ∫ w : Fin m → ℝ, id w ∂(Measure.pi (fun _ : Fin m => gaussianReal 0 1)) = 0 := by
          funext i
          let L : (Fin m → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
          have hL : ∫ w, L w ∂(Measure.pi (fun _ : Fin m => gaussianReal 0 1))
              = L (∫ w, id w ∂(Measure.pi (fun _ : Fin m => gaussianReal 0 1))) :=
            ContinuousLinearMap.integral_comp_id_comm' hInt L
          show L (∫ w, id w ∂(Measure.pi (fun _ : Fin m => gaussianReal 0 1))) = 0
          rw [← hL]
          exact hGcoord i
        let Φ : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) :=
          (Matrix.mulVecBilin ℝ ℝ (Matrix.PosSemidef.sqrt hSigma)).toContinuousLinearMap
        have hΦ : ∀ w : Fin m → ℝ, Φ w = Matrix.mulVec (Matrix.PosSemidef.sqrt hSigma) w := fun w =>
          Matrix.mulVecBilin_apply ℝ ℝ (Matrix.PosSemidef.sqrt hSigma) w
        have hfun : (fun w : Fin m → ℝ => Matrix.mulVec (Matrix.PosSemidef.sqrt hSigma) w) = ⇑Φ :=
          funext fun w => (hΦ w).symm
        have hstep : ∫ x, id x ∂((Measure.pi (fun _ : Fin m => gaussianReal 0 1)).map
              (fun w => Matrix.mulVec (Matrix.PosSemidef.sqrt hSigma) w))
            = ∫ w : Fin m → ℝ, Matrix.mulVec (Matrix.PosSemidef.sqrt hSigma) w
              ∂(Measure.pi (fun _ : Fin m => gaussianReal 0 1)) := by
          refine MeasureTheory.integral_map ?_ measurable_id.aestronglyMeasurable
          rw [hfun]
          exact Φ.continuous.measurable.aemeasurable
        rw [hstep]
        have hcomm : ∫ w : Fin m → ℝ, Matrix.mulVec (Matrix.PosSemidef.sqrt hSigma) w
              ∂(Measure.pi (fun _ : Fin m => gaussianReal 0 1))
            = Matrix.mulVec (Matrix.PosSemidef.sqrt hSigma)
              (∫ w, id w ∂(Measure.pi (fun _ : Fin m => gaussianReal 0 1))) := by
          simp only [hfun, ← hΦ]
          exact ContinuousLinearMap.integral_comp_id_comm' hInt Φ
        rw [hcomm, hmass, ← hΦ]
        simp
      rw [hν, hT]
    have hcov_eq : covarianceBilinDual nu = covarianceBilinDual ((Measure.pi (fun _ : Fin m => gaussianReal 0 1)).map
        (fun w => Matrix.mulVec (Matrix.PosSemidef.sqrt hSigma) w)) := by
      have hICGVν : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector
          nu (fun s : Fin m → ℝ => s) Sigma := by
        exact statopia_math_node_4002638969_66ac1fc1 m Sigma hSigma nu hprob hgauss hint1 hmean hint2 hcov
      have hICGVT : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector
          (Measure.pi (fun _ : Fin m => gaussianReal 0 1))
          (fun w => Matrix.mulVec (Matrix.PosSemidef.sqrt hSigma) w) Sigma := by
        have hlin := Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector.linearImage
          (Measure.pi (fun _ : Fin m => gaussianReal 0 1)) (fun ω => ω)
          (1 : Matrix (Fin m) (Fin m) ℝ) hICGV1 (Matrix.PosSemidef.sqrt hSigma)
        have hmat : (Matrix.PosSemidef.sqrt hSigma : Matrix (Fin m) (Fin m) ℝ) * 1 *
            (Matrix.PosSemidef.sqrt hSigma).transpose = Sigma := by
          rw [Matrix.mul_one]
          exact hGram
        rw [hmat] at hlin
        exact hlin
      have hm_eq := Statlib.StatFoundation.RandomVariable.Gaussian.map_eq_map_of_centeredGaussianVector
        nu (Measure.pi (fun _ : Fin m => gaussianReal 0 1)) (fun s : Fin m → ℝ => s)
        (fun w => Matrix.mulVec (Matrix.PosSemidef.sqrt hSigma) w) Sigma hICGVν hICGVT hSigma
      rw [MeasureTheory.Measure.map_id'] at hm_eq
      exact congrArg covarianceBilinDual hm_eq
    exact ProbabilityTheory.IsGaussian.ext_covarianceBilinDual hmean_eq hcov_eq
  /- @proof-region region.target-node.session.535f29bc7b80d23f end -/

end Statlib.Imported
end

