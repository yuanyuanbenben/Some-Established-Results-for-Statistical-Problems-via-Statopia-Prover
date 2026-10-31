import Statlib.StatFoundation.Statistics.Asymptotic.ScoreCLT
import Statlib.StatFoundation.Convergence.Resampling.GaussianMaxComparison
import Statlib.StatFoundation.Convergence.AnalysisTools.GaussianMaxAnticoncentration
import Statlib.StatFoundation.Statistics.Asymptotic.LAN
import Statlib.StatFoundation.Convergence.AnalysisTools.SmoothMax
import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.Vocabulary
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.Base
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.ProvedNodes.Node_2103973696_3a1ca2b0_181d2773

namespace PaperProofTasks.job_paper_de3065fb922748188f3a0354eba90ed9

open _root_.PaperProofTasks.job_paper_de3065fb922748188f3a0354eba90ed9.Statlib.Imported
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

set_option autoImplicit false in
theorem statopia_math_node_4284577856_99606abc : ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : ℕ) (hq : 1 ≤ q)
    (X : Ω → Fin q → ℝ) (hX : Measurable X)
    (Sigma : Matrix (Fin q) (Fin q) ℝ)
    (hSymm : ∀ k l : Fin q, Sigma k l = Sigma l k)
    (hPSD : Sigma.PosSemidef)
    (hVar : ∀ k : Fin q, Sigma k k = 1)
    (hGauss : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector μ X Sigma)
    (j : Fin q),
    MeasureTheory.Measure.map
        (fun ω => fun k : {k : Fin q // k ≠ j} => X ω k.1 - Sigma k.1 j * X ω j) μ
      = Statlib.Imported.gaussianVecMeasure
          (0 : {k : Fin q // k ≠ j} → ℝ)
          (fun k l : {k : Fin q // k ≠ j} => Sigma k.1 l.1 - Sigma k.1 j * Sigma l.1 j) := by
  /- @proof-region region.target-node.session.0433fb768fe57167 begin -/
  intro Ω _ μ _ q hq X hX Sigma hSymm hPSD hVar hGauss j
  classical
  set ι : Type := {k : Fin q // k ≠ j} with hι
  set S : Matrix ι ι ℝ := fun k l => Sigma k.1 l.1 - Sigma k.1 j * Sigma l.1 j with hS
  obtain ⟨hSpsd, hSsym⟩ := statopia_math_node_2103973696_3a1ca2b0 q j Sigma hPSD hVar
  rw [← hS] at hSpsd hSsym
  by_cases hne : Nonempty ι
  · have hn1 : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr hne
    set n : ℕ := Fintype.card ι with hn
    have hn1' : 1 ≤ n := hn1
    have hnpos : 0 < n := hn1
    set e : ι ≃ Fin n := Fintype.equivFin ι with he
    set φ : (ι → ℝ) ≃ᵐ (Fin n → ℝ) :=
      MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) e with hφ
    set f : Fin n → Fin q := fun i => (e.symm i).1 with hf
    set R : Ω → ι → ℝ := fun ω k => X ω k.1 - Sigma k.1 j * X ω j with hR
    set A : Matrix ι ι ℝ := Matrix.PosSemidef.sqrt hSsym with hA
    set M : Matrix (Fin q) (Fin q) ℝ :=
      fun k a => (if k = a then 1 else 0) - Sigma k j * (if a = j then 1 else 0) with hM
    set N : Matrix (Fin n) (Fin q) ℝ := M.submatrix f id with hN
    set Ahat : Matrix (Fin n) (Fin n) ℝ := fun i k => A (e.symm i) (e.symm k) with hAd
    set C : Matrix (Fin n) (Fin n) ℝ := fun i k => S (e.symm i) (e.symm k) with hCd
    set Ct : Matrix (Fin n) (Fin n) ℝ := (2⁻¹ : ℝ) • (C + C.transpose) with hCt
    have hφ_apply : ∀ (x : ι → ℝ) (k : Fin n), φ x k = x (e.symm k) := by
      intro x k
      conv_lhs => rw [← Equiv.apply_symm_apply e k]
      exact MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin n => ℝ) e x (e.symm k)
    have hAform : A = (↑(Matrix.PosSemidef.isHermitian hSsym).eigenvectorUnitary : Matrix ι ι ℝ) *
        Matrix.diagonal (RCLike.ofReal ∘ (fun x => Real.sqrt x)
          ∘ (Matrix.PosSemidef.isHermitian hSsym).eigenvalues) *
        star (↑(Matrix.PosSemidef.isHermitian hSsym).eigenvectorUnitary : Matrix ι ι ℝ) := by
      rw [hA]
      simp only [Matrix.PosSemidef.sqrt]
    set u : Matrix.unitaryGroup ι ℝ := (Matrix.PosSemidef.isHermitian hSsym).eigenvectorUnitary with hu
    set lam : ι → ℝ := (Matrix.PosSemidef.isHermitian hSsym).eigenvalues with hlam
    set dd : ι → ℝ := RCLike.ofReal ∘ Real.sqrt ∘ lam with hdd
    have hAform' : A = (↑u : Matrix ι ι ℝ) * Matrix.diagonal dd * star (↑u : Matrix ι ι ℝ) := hAform
    have hconj : ∀ x : Matrix ι ι ℝ,
        ((Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ))
          (Matrix.PosSemidef.isHermitian hSsym).eigenvectorUnitary) x
        = (↑u : Matrix ι ι ℝ) * x * star (↑u : Matrix ι ι ℝ) := by
      intro x
      rfl
    have hspec : ((1 / 2 : ℝ) • (S + S.transpose))
        = (↑u : Matrix ι ι ℝ) * Matrix.diagonal (RCLike.ofReal ∘ lam) * star (↑u : Matrix ι ι ℝ) := by
      have h := Matrix.IsHermitian.spectral_theorem (Matrix.PosSemidef.isHermitian hSsym)
      rw [hconj] at h
      exact h
    have hUU : star (↑u : Matrix ι ι ℝ) * (↑u : Matrix ι ι ℝ) = 1 :=
      Matrix.UnitaryGroup.star_mul_self u
    have hddsq : ∀ i, dd i * dd i = RCLike.ofReal (lam i) := by
      intro i
      have hnonneg : 0 ≤ lam i := Matrix.PosSemidef.eigenvalues_nonneg hSsym i
      have hsq : Real.sqrt (lam i) * Real.sqrt (lam i) = lam i := Real.mul_self_sqrt hnonneg
      simpa [hdd, Function.comp] using hsq
    have hsqq : A * A
        = (↑u : Matrix ι ι ℝ) * Matrix.diagonal (RCLike.ofReal ∘ lam) * star (↑u : Matrix ι ι ℝ) := by
      rw [hAform']
      calc ((↑u : Matrix ι ι ℝ) * Matrix.diagonal dd * star (↑u : Matrix ι ι ℝ))
            * ((↑u : Matrix ι ι ℝ) * Matrix.diagonal dd * star (↑u : Matrix ι ι ℝ))
          = (↑u : Matrix ι ι ℝ) * Matrix.diagonal dd
              * (star (↑u : Matrix ι ι ℝ) * (↑u : Matrix ι ι ℝ))
              * Matrix.diagonal dd * star (↑u : Matrix ι ι ℝ) := by
            simp only [Matrix.mul_assoc]
        _ = (↑u : Matrix ι ι ℝ) * Matrix.diagonal dd * 1 * Matrix.diagonal dd
              * star (↑u : Matrix ι ι ℝ) := by
            rw [hUU]
        _ = (↑u : Matrix ι ι ℝ) * (Matrix.diagonal dd * Matrix.diagonal dd)
              * star (↑u : Matrix ι ι ℝ) := by
            simp only [Matrix.mul_one, Matrix.mul_assoc]
        _ = (↑u : Matrix ι ι ℝ) * Matrix.diagonal (RCLike.ofReal ∘ lam)
              * star (↑u : Matrix ι ι ℝ) := by
            rw [Matrix.diagonal_mul_diagonal,
              show (fun i => dd i * dd i) = (RCLike.ofReal ∘ lam) from funext hddsq]
    have hDstar : star (Matrix.diagonal dd) = Matrix.diagonal dd := by
      ext i k
      by_cases h : i = k
      · subst h
        simp [Matrix.diagonal, hdd, Function.comp]
      · simp [Matrix.diagonal, h, Ne.symm h]
    have hAstar : star A = A := by
      rw [hAform', star_mul, star_mul, star_star, hDstar, Matrix.mul_assoc]
    have hAherm : A.IsHermitian := by
      simpa [Matrix.IsHermitian, Matrix.conjTranspose] using hAstar
    have hAtr : A.transpose = A := by
      have h := hAherm
      simpa [Matrix.IsHermitian, Matrix.conjTranspose] using h
    have hAA : A * A.transpose = (2⁻¹ : ℝ) • (S + S.transpose) := by
      have hhalf : (1 / 2 : ℝ) = 2⁻¹ := by norm_num
      rw [hAtr, hsqq, ← hspec, hhalf]
    have hmul_meas : ∀ {m k : Type} [Fintype m] [Fintype k] (B : Matrix m k ℝ),
        Measurable (fun v : k → ℝ => B.mulVec v) := by
      intro m k _ _ B
      refine measurable_pi_iff.mpr (fun i => ?_)
      have hsum : (fun v : k → ℝ => B.mulVec v i) = fun v => ∑ j, B i j * v j := by
        funext v
        simp [Matrix.mulVec, dotProduct]
      rw [hsum]
      exact Finset.measurable_sum _ (fun j _ => measurable_const.mul (measurable_pi_apply j))
    have hRmeas : Measurable R := by
      rw [hR]
      refine measurable_pi_iff.mpr (fun k => ?_)
      exact ((measurable_pi_apply k.1).comp hX).sub
        (((measurable_pi_apply j).comp hX).const_mul (Sigma k.1 j))
    have hNY : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector μ
        (fun ω => N.mulVec (X ω)) (N * Sigma * N.transpose) :=
      Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector.linearImage μ X Sigma
        hGauss N
    have hMvec : ∀ (y : Fin q → ℝ) (k : Fin q), M.mulVec y k = y k - Sigma k j * y j := by
      intro y k
      simp only [Matrix.mulVec, dotProduct, hM, sub_mul, Finset.sum_sub_distrib, ite_mul, mul_ite,
        one_mul, zero_mul, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
    have hvec : ∀ (y : Fin q → ℝ) (i : Fin n), N.mulVec y i = y (f i) - Sigma (f i) j * y j := by
      intro y i
      rw [show N.mulVec y i = M.mulVec y (f i) from rfl, hMvec]
    have hcol : ∀ (k l : Fin q), (∑ a, Sigma k a * M l a) = Sigma k l - Sigma l j * Sigma k j := by
      intro k l
      simp only [hM, mul_sub, Finset.sum_sub_distrib, mul_ite, ite_mul, one_mul, zero_mul, mul_one,
        mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring
    have hE : M * Sigma * M.transpose = fun k l => Sigma k l - Sigma k j * Sigma l j := by
      ext k l
      have hMS : ∀ a, (M * Sigma) k a = Sigma k a - Sigma k j * Sigma j a := fun a => by
        have h := hMvec (fun b => Sigma b a) k
        simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct] at h ⊢
        exact h
      have hstep : (M * Sigma * M.transpose) k l
          = ∑ a, (Sigma k a - Sigma k j * Sigma j a) * M l a := by
        simp only [Matrix.mul_apply, Matrix.transpose_apply, hMS]
      rw [hstep]
      have hsplit : (∑ a, (Sigma k a - Sigma k j * Sigma j a) * M l a)
          = (∑ a, Sigma k a * M l a) - Sigma k j * (∑ a, Sigma j a * M l a) := by
        have h1 : ∀ a, (Sigma k a - Sigma k j * Sigma j a) * M l a
            = Sigma k a * M l a - Sigma k j * (Sigma j a * M l a) := fun a => by ring
        simp only [h1, Finset.sum_sub_distrib, Finset.mul_sum]
      rw [hsplit, hcol k l, hcol j l, hSymm j l, hVar j]
      ring
    have hCeq : N * Sigma * N.transpose = (M * Sigma * M.transpose).submatrix f f := by
      have hNt : N.transpose = M.transpose.submatrix id f := rfl
      rw [hN, hNt, Matrix.submatrix_mul (M * Sigma) M.transpose f id f Function.bijective_id,
        Matrix.submatrix_mul M Sigma f id id Function.bijective_id]
      simp
    have hC' : N * Sigma * N.transpose = C := by
      rw [hCeq, hE]
      rfl
    have hAhat_fac : Ahat * Ahat.transpose
        = fun i k : Fin n => (A * A.transpose) (e.symm i) (e.symm k) := by
      ext i k
      simp only [Matrix.mul_apply, Matrix.transpose_apply, hAd]
      exact Equiv.sum_comp e.symm (fun b : ι => A (e.symm i) b * A (e.symm k) b)
    have hsub2 : (fun i k : Fin n => ((2⁻¹ : ℝ) • (S + S.transpose)) (e.symm i) (e.symm k))
        = Ct := by
      ext i k
      simp only [hCt, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, hCd,
        smul_eq_mul]
    have hAhat : Ahat * Ahat.transpose = Ct := by
      rw [hAhat_fac, hAA, hsub2]
    have hCtpsd : Ct.PosSemidef := by
      have h := hNY.posSemidef_symmetrizedCovariance hn1'
      rw [hC'] at h
      simpa only [hCt] using h
    haveI hstdprob : IsProbabilityMeasure
        (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi n) :=
      Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.standardPi_probability n
    have hbase : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector
        (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi n) (fun z : Fin n → ℝ => z)
        (1 : Matrix (Fin n) (Fin n) ℝ) := by
      have h := Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector_isCenteredGaussianVector
        hnpos (1 : Matrix (Fin n) (Fin n) ℝ) Matrix.PosSemidef.one
      have hfun : Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector
          (1 : Matrix (Fin n) (Fin n) ℝ) = fun z : Fin n → ℝ => z := by
        funext z i
        simp [Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector]
      rw [hfun] at h
      exact h
    have hstd0 : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector
        (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi n)
        (fun z : Fin n → ℝ => Ahat.mulVec z) (Ahat * 1 * Ahat.transpose) :=
      Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector.linearImage
        (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi n) (fun z : Fin n → ℝ => z)
        (1 : Matrix (Fin n) (Fin n) ℝ) hbase Ahat
    have hstd : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector
        (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi n)
        (fun z : Fin n → ℝ => Ahat.mulVec z) Ct := by
      have h := hstd0
      rw [Matrix.mul_one, hAhat] at h
      exact h
    have hcan : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector
        (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi n)
        (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector Ct) Ct :=
      Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector_isCenteredGaussianVector
        hnpos Ct hCtpsd
    have hmap_eq : Measure.map
          (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector Ct)
          (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi n)
        = Measure.map (fun z : Fin n → ℝ => Ahat.mulVec z)
          (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi n) :=
      Statlib.StatFoundation.RandomVariable.Gaussian.map_eq_map_of_centeredGaussianVector
        (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi n)
        (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi n)
        (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector Ct)
        (fun z : Fin n → ℝ => Ahat.mulVec z) Ct hcan hstd hCtpsd
    have hNYmap : Measure.map (fun ω => N.mulVec (X ω)) μ
        = Measure.map
          (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector Ct)
          (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi n) := by
      have h := hNY.map_eq_canonicalGaussianVector hn1'
      rw [hC'] at h
      simpa only [hCt] using h
    have hSum : Measure.map (fun ω => N.mulVec (X ω)) μ
        = Measure.map (fun z : Fin n → ℝ => Ahat.mulVec z)
          (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi n) := by
      rw [hNYmap, hmap_eq]
    have hRφ : ∀ ω, φ (R ω) = N.mulVec (X ω) := by
      intro ω
      funext k
      rw [hφ_apply, hvec]
    have hstep1 : Measure.map φ (Measure.map R μ) = Measure.map (fun ω => N.mulVec (X ω)) μ := by
      rw [Measure.map_map (MeasurableEquiv.measurable φ) hRmeas]
      congr 1
      exact funext hRφ
    have hunfold : gaussianVecMeasure (0 : ι → ℝ) S
        = Measure.map (fun y : ι → ℝ => Matrix.mulVec A y) (stdGaussianPi ι) := by
      unfold Statlib.Imported.gaussianVecMeasure
      rw [dif_pos hSsym]
      simp [← hA]
    have hφstd : Measure.map φ (stdGaussianPi ι)
        = Statlib.StatFoundation.RandomVariable.Gaussian.standardPi n := by
      simpa [hφ, Statlib.Imported.stdGaussianPi,
        Statlib.StatFoundation.RandomVariable.Gaussian.standardPi] using
        (MeasureTheory.Measure.pi_map_piCongrLeft e
          (fun _ : Fin n => ProbabilityTheory.gaussianReal (0 : ℝ) 1))
    have hAmeas : Measurable (fun y : ι → ℝ => Matrix.mulVec A y) := hmul_meas A
    have hAhat_meas : Measurable (fun z : Fin n → ℝ => Ahat.mulVec z) := hmul_meas Ahat
    have hAphi : ∀ y : ι → ℝ, φ (Matrix.mulVec A y) = Matrix.mulVec Ahat (φ y) := by
      intro y
      funext i
      rw [hφ_apply]
      simp only [Matrix.mulVec, dotProduct, hAd, hφ_apply]
      exact (Equiv.sum_comp e.symm (fun b : ι => A (e.symm i) b * y b)).symm
    have hstep2 : Measure.map φ (gaussianVecMeasure (0 : ι → ℝ) S)
        = Measure.map (fun z : Fin n → ℝ => Ahat.mulVec z)
          (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi n) := by
      rw [hunfold, ← hφstd, Measure.map_map (MeasurableEquiv.measurable φ) hAmeas,
        Measure.map_map hAhat_meas (MeasurableEquiv.measurable φ)]
      congr 1
      exact funext hAphi
    have hgoal : Measure.map φ (Measure.map R μ)
        = Measure.map φ (gaussianVecMeasure (0 : ι → ℝ) S) := by
      rw [hstep1, hstep2]
      exact hSum
    have hcomp : (⇑φ.symm ∘ ⇑φ) = id := funext fun x => MeasurableEquiv.symm_apply_apply φ x
    have h1 : Measure.map φ.symm (Measure.map φ (Measure.map R μ)) = Measure.map R μ := by
      rw [Measure.map_map (MeasurableEquiv.measurable φ.symm) (MeasurableEquiv.measurable φ),
        hcomp, Measure.map_id]
    have h2 : Measure.map φ.symm (Measure.map φ (gaussianVecMeasure (0 : ι → ℝ) S))
        = gaussianVecMeasure (0 : ι → ℝ) S := by
      rw [Measure.map_map (MeasurableEquiv.measurable φ.symm) (MeasurableEquiv.measurable φ),
        hcomp, Measure.map_id]
    rw [← h1, hgoal]
    exact h2
  · haveI hempty : IsEmpty ι := ⟨fun x => hne ⟨x⟩⟩
    have hconst1 : (fun ω => fun k : ι => X ω k.1 - Sigma k.1 j * X ω j) = fun _ => (0 : ι → ℝ) := by
      funext ω k
      exact isEmptyElim k
    have hconst2 : (fun y : ι → ℝ => (0 : ι → ℝ) + Matrix.mulVec (Matrix.PosSemidef.sqrt hSsym) y)
        = fun _ => (0 : ι → ℝ) := by
      funext y k
      exact isEmptyElim k
    haveI hprob : IsProbabilityMeasure (stdGaussianPi ι) := by
      set m : ℕ := Fintype.card ι with hm
      set e0 : ι ≃ Fin m := Fintype.equivFin ι with he0
      set φ0 : (ι → ℝ) ≃ᵐ (Fin m → ℝ) := MeasurableEquiv.piCongrLeft (fun _ : Fin m => ℝ) e0 with hφ0
      have hmap : Measure.map φ0 (stdGaussianPi ι)
          = Statlib.StatFoundation.RandomVariable.Gaussian.standardPi m := by
        simpa [hφ0, Statlib.Imported.stdGaussianPi,
          Statlib.StatFoundation.RandomVariable.Gaussian.standardPi] using
          (MeasureTheory.Measure.pi_map_piCongrLeft e0
            (fun _ : Fin m => ProbabilityTheory.gaussianReal (0 : ℝ) 1))
      have huniv : (Measure.map φ0 (stdGaussianPi ι)) Set.univ = (stdGaussianPi ι) Set.univ := by
        rw [Measure.map_apply (MeasurableEquiv.measurable φ0) MeasurableSet.univ]
        simp
      haveI hstdp : IsProbabilityMeasure
          (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi m) :=
        Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.standardPi_probability m
      refine ⟨?_⟩
      rw [← huniv, hmap]
      exact measure_univ
    have hLHS : Measure.map (fun _ => (0 : ι → ℝ)) μ = Measure.dirac 0 := by
      rw [MeasureTheory.Measure.map_const, measure_univ, one_smul]
    have hRHS : Measure.map (fun _ => (0 : ι → ℝ)) (stdGaussianPi ι) = Measure.dirac 0 := by
      rw [MeasureTheory.Measure.map_const, measure_univ, one_smul]
    unfold Statlib.Imported.gaussianVecMeasure
    rw [dif_pos hSsym, hconst1, hconst2, hLHS, hRHS]
  /- @proof-region region.target-node.session.0433fb768fe57167 end -/

end Statlib.Imported

