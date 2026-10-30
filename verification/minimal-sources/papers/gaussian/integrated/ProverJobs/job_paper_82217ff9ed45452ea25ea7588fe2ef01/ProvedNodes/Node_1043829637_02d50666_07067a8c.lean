import Statlib.HighDim.MatrixAnalysis.AndoVocabulary
import Statlib.StatFoundation.RandomVariable.Gaussian.Slepian
import ProverJobs.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Vocabulary
import ProverJobs.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Base
import ProverJobs.job_paper_82217ff9ed45452ea25ea7588fe2ef01.ProvedNodes.Node_2405363399_2b807e30_7221f5e7
import ProverJobs.job_paper_82217ff9ed45452ea25ea7588fe2ef01.ProvedNodes.Node_3076116109_992c70da_6addc001

namespace PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators
open _root_.PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Statlib.Imported
open _root_.PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Statlib.Imported.Model

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators
namespace Statlib.Imported

noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_1043829637_02d50666 : ∀ (a c0 alpha cvar ccirc eps0 Ccor : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (M : Model Ω μ a) (hM : Model.Assumptions M c0 alpha cvar ccirc eps0 Ccor)
    (n : ℕ) (hn : 1 ≤ n) (hl : M.ell n ≤ M.p n),
    (∀ i j : Fin (M.ell n), M.corrMat n (M.ell n) hl i j = M.corrMat n (M.ell n) hl j i) ∧
    (∀ i : Fin (M.ell n), M.corrMat n (M.ell n) hl i i = 1) ∧
    (∀ u : Fin (M.ell n) → ℝ,
      (M.tildeLaw n).map (fun w : Fin (M.p n) → ℝ =>
          ∑ i : Fin (M.ell n),
            u i * (w (M.g n (Fin.castLE hl i)) / M.sigma n (M.g n (Fin.castLE hl i))))
        = gaussianReal 0 (Real.toNNReal
            (∑ i : Fin (M.ell n), ∑ j : Fin (M.ell n),
              u i * M.corrMat n (M.ell n) hl i j * u j))) ∧
    (∀ i : Fin (M.ell n),
      (M.tildeLaw n).map (fun w : Fin (M.p n) → ℝ =>
          w (M.g n (Fin.castLE hl i)) / M.sigma n (M.g n (Fin.castLE hl i)))
        = gaussianReal 0 1) ∧
    (∀ j : Fin (M.p n),
      (M.tildeLaw n).map (fun w : Fin (M.p n) → ℝ => w j / M.sigma n j)
        = gaussianReal 0 1) ∧
    (∀ j : Fin (M.p n),
      (M.tildeLaw n).map (fun w : Fin (M.p n) → ℝ => w j / (M.sigma n j) ^ (M.tau n))
        = (gaussianReal 0 1).map (fun z : ℝ => (M.sigma n j) ^ (1 - M.tau n) * z)) := by
  /- @proof-region region.target-node.session.7a4c494f3a7c493b begin -/
  intro a c0 alpha cvar ccirc eps0 Ccor Ω instΩ μ instμ M hM n hn hEll
  have hn0 : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hSig : ∀ a' b : Fin (M.p n), M.Sigma n a' b = M.Sigma n b a' := by
    intro a' b
    have h1 := (statopia_math_node_3076116109_992c70da a c0 alpha cvar ccirc eps0 Ccor M hM n hn
      a' b a').1
    have h2 := (statopia_math_node_3076116109_992c70da a c0 alpha cvar ccirc eps0 Ccor M hM n hn
      b a' b).1
    have hc : M.covX n a' b = M.covX n b a' := by
      simp only [covX, dif_pos hn0]
      exact covariance_comm _ _
    rw [← h1, hc, h2]
  have hA : ∀ i j : Fin (M.ell n),
      M.corrMat n (M.ell n) hEll i j = M.corrMat n (M.ell n) hEll j i := by
    intro i j
    have hs := hSig (M.g n (Fin.castLE hEll i)) (M.g n (Fin.castLE hEll j))
    have h1 := (statopia_math_node_3076116109_992c70da a c0 alpha cvar ccirc eps0 Ccor M hM n hn
      (M.g n (Fin.castLE hEll i)) (M.g n (Fin.castLE hEll j)) (M.g n (Fin.castLE hEll i))).1
    have h2 := (statopia_math_node_3076116109_992c70da a c0 alpha cvar ccirc eps0 Ccor M hM n hn
      (M.g n (Fin.castLE hEll j)) (M.g n (Fin.castLE hEll i)) (M.g n (Fin.castLE hEll j))).1
    simp only [corrMat, corrEntry, Matrix.of_apply]
    rw [h1, h2, hs]
    ring
  have hB : ∀ i : Fin (M.ell n), M.corrMat n (M.ell n) hEll i i = 1 := by
    intro i
    have hd := statopia_math_node_3076116109_992c70da a c0 alpha cvar ccirc eps0 Ccor M hM n hn
      (M.g n (Fin.castLE hEll i)) (M.g n (Fin.castLE hEll i)) (M.g n (Fin.castLE hEll i))
    have hpos : 0 < M.sigma n (M.g n (Fin.castLE hEll i)) := hM.hsig_pos n hn0 _
    have hne : M.sigma n (M.g n (Fin.castLE hEll i)) * M.sigma n (M.g n (Fin.castLE hEll i)) ≠ 0 :=
      mul_ne_zero (ne_of_gt hpos) (ne_of_gt hpos)
    simp only [corrMat, corrEntry, Matrix.of_apply]
    rw [hd.1, ← hd.2.2, pow_two]
    exact div_self hne
  have hprobe1 : stdGauss (M.p n) = Statlib.StatFoundation.RandomVariable.Gaussian.standardPi (M.p n) := rfl
  haveI hstdProb : IsProbabilityMeasure
      (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi (M.p n)) := by
    change IsProbabilityMeasure (Measure.pi (fun _ : Fin (M.p n) => gaussianReal 0 1))
    infer_instance
  have hcgv_apply : ∀ (A : Matrix (Fin (M.p n)) (Fin (M.p n)) ℝ) (z : Fin (M.p n) → ℝ),
      Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector A z =
        (CFC.sqrt A).mulVec z := by
    intro A z
    simp only [Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector]
  have hcgv1_mulVec : ∀ (A : Matrix (Fin (M.p n)) (Fin (M.p n)) ℝ) (z : Fin (M.p n) → ℝ),
      A.mulVec (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector
        (1 : Matrix (Fin (M.p n)) (Fin (M.p n)) ℝ) z) = A.mulVec z := by
    intro A z
    rw [hcgv_apply]
    rw [Matrix.mulVec_mulVec]
    rw [CFC.sqrt_one, Matrix.mul_one]
  have hBsq : Matrix.PosSemidef.sqrt (M.hSigma n) *
      (Matrix.PosSemidef.sqrt (M.hSigma n)).transpose = M.Sigma n :=
    statopia_math_node_2405363399_2b807e30 (M.p n) (M.Sigma n) (M.hSigma n)
  have hBB : Matrix.PosSemidef.sqrt (M.hSigma n) * 1 *
      (Matrix.PosSemidef.sqrt (M.hSigma n)).transpose = M.Sigma n := by
    rw [Matrix.mul_one, hBsq]
  have hPSDB : (Matrix.PosSemidef.sqrt (M.hSigma n) * 1 *
      (Matrix.PosSemidef.sqrt (M.hSigma n)).transpose).PosSemidef := by
    rw [hBB]
    exact M.hSigma n
  have hCGV1 : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector
      (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi (M.p n))
      (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector
        (1 : Matrix (Fin (M.p n)) (Fin (M.p n)) ℝ))
      (1 : Matrix (Fin (M.p n)) (Fin (M.p n)) ℝ) :=
    Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector_isCenteredGaussianVector
      (Nat.lt_of_lt_of_le Nat.zero_lt_one (M.hp n)) 1 Matrix.PosSemidef.one
  have hCGVB : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector
      (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi (M.p n))
      (fun z => (Matrix.PosSemidef.sqrt (M.hSigma n)).mulVec
        (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector
          (1 : Matrix (Fin (M.p n)) (Fin (M.p n)) ℝ) z))
      (Matrix.PosSemidef.sqrt (M.hSigma n) * 1 *
        (Matrix.PosSemidef.sqrt (M.hSigma n)).transpose) :=
    Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector.linearImage
      (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi (M.p n))
      (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector
        (1 : Matrix (Fin (M.p n)) (Fin (M.p n)) ℝ))
      (1 : Matrix (Fin (M.p n)) (Fin (M.p n)) ℝ)
      hCGV1
      (Matrix.PosSemidef.sqrt (M.hSigma n))
  have hC : ∀ u : Fin (M.ell n) → ℝ,
      (M.tildeLaw n).map
          (fun w => ∑ i : Fin (M.ell n),
            u i * (w (M.g n (Fin.castLE hEll i)) /
              (M.sigma n (M.g n (Fin.castLE hEll i)))))
        = gaussianReal 0 (Real.toNNReal (∑ i : Fin (M.ell n), ∑ j : Fin (M.ell n),
            u i * M.corrMat n (M.ell n) hEll i j * u j)) := by
    intro u
    let S : Matrix (Fin (M.ell n)) (Fin (M.p n)) ℝ :=
      Matrix.of (fun i l => if l = M.g n (Fin.castLE hEll i) then
        (M.sigma n (M.g n (Fin.castLE hEll i)))⁻¹ else 0)
    have hSapply : ∀ (i : Fin (M.ell n)) (l : Fin (M.p n)), S i l =
        (if l = M.g n (Fin.castLE hEll i) then
          (M.sigma n (M.g n (Fin.castLE hEll i)))⁻¹ else 0) := by
      intro i l
      rfl
    have hSmulVec : ∀ (x : Fin (M.p n) → ℝ) (i : Fin (M.ell n)),
        (S.mulVec x) i =
          (M.sigma n (M.g n (Fin.castLE hEll i)))⁻¹ * x (M.g n (Fin.castLE hEll i)) := by
      intro x i
      have h1 : (S.mulVec x) i = ∑ l : Fin (M.p n), S i l * x l := rfl
      rw [h1]
      simp only [hSapply]
      simp
    have hBm : Measurable (fun z : Fin (M.p n) → ℝ =>
        (Matrix.PosSemidef.sqrt (M.hSigma n)).mulVec z) := by
      have heq : (fun z : Fin (M.p n) → ℝ =>
          (Matrix.PosSemidef.sqrt (M.hSigma n)).mulVec z) =
          (fun z i => ∑ j : Fin (M.p n),
            (Matrix.PosSemidef.sqrt (M.hSigma n)) i j * z j) := rfl
      rw [heq]
      measurability
    have hFm : Measurable (fun w : Fin (M.p n) → ℝ => ∑ i : Fin (M.ell n),
        u i * (w (M.g n (Fin.castLE hEll i)) /
          (M.sigma n (M.g n (Fin.castLE hEll i))))) := by
      measurability
    have hPSDS : (S * (Matrix.PosSemidef.sqrt (M.hSigma n) * 1 *
        (Matrix.PosSemidef.sqrt (M.hSigma n)).transpose) * S.transpose).PosSemidef := by
      have h1 : (S * M.Sigma n * S.conjTranspose).PosSemidef :=
        Matrix.PosSemidef.mul_mul_conjTranspose_same (M.hSigma n) S
      rw [Matrix.conjTranspose_eq_transpose_of_trivial, ← hBB] at h1
      exact h1
    have hSgv : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector
        (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi (M.p n))
        (fun z => S.mulVec ((Matrix.PosSemidef.sqrt (M.hSigma n)).mulVec
          (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector
            (1 : Matrix (Fin (M.p n)) (Fin (M.p n)) ℝ) z)))
        (S * (Matrix.PosSemidef.sqrt (M.hSigma n) * 1 *
          (Matrix.PosSemidef.sqrt (M.hSigma n)).transpose) * S.transpose) :=
      Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector.linearImage
        (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi (M.p n))
        (fun z => (Matrix.PosSemidef.sqrt (M.hSigma n)).mulVec
          (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector
            (1 : Matrix (Fin (M.p n)) (Fin (M.p n)) ℝ) z))
        (Matrix.PosSemidef.sqrt (M.hSigma n) * 1 *
          (Matrix.PosSemidef.sqrt (M.hSigma n)).transpose)
        hCGVB S
    have hlaw :=
      Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector.map_linearCombination
        (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi (M.p n))
        (fun z => S.mulVec ((Matrix.PosSemidef.sqrt (M.hSigma n)).mulVec
          (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector
            (1 : Matrix (Fin (M.p n)) (Fin (M.p n)) ℝ) z)))
        (S * (Matrix.PosSemidef.sqrt (M.hSigma n) * 1 *
          (Matrix.PosSemidef.sqrt (M.hSigma n)).transpose) * S.transpose)
        hSgv hPSDS u
    have hmat : S * (Matrix.PosSemidef.sqrt (M.hSigma n) * 1 *
        (Matrix.PosSemidef.sqrt (M.hSigma n)).transpose) * S.transpose =
        M.corrMat n (M.ell n) hEll := by
      rw [hBB]
      refine Matrix.ext ?_
      intro i j
      have hcx := (statopia_math_node_3076116109_992c70da a c0 alpha cvar ccirc eps0 Ccor M hM n hn
        (M.g n (Fin.castLE hEll i)) (M.g n (Fin.castLE hEll j))
        (M.g n (Fin.castLE hEll i))).1
      simp only [corrMat, corrEntry, Matrix.of_apply]
      rw [hcx]
      rw [Matrix.mul_apply]
      have hcol : ∀ x : Fin (M.p n), (S * M.Sigma n) i x =
          (M.sigma n (M.g n (Fin.castLE hEll i)))⁻¹ *
            M.Sigma n (M.g n (Fin.castLE hEll i)) x := by
        intro x
        rw [Matrix.mul_apply]
        simp only [hSapply]
        simp
      simp only [Matrix.transpose_apply, hcol, hSapply]
      simp
      ring
    have hpt : ∀ z : Fin (M.p n) → ℝ,
        ∑ j : Fin (M.ell n), u j * (S.mulVec ((Matrix.PosSemidef.sqrt (M.hSigma n)).mulVec
          (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector
            (1 : Matrix (Fin (M.p n)) (Fin (M.p n)) ℝ) z))) j
          = ∑ i : Fin (M.ell n), u i *
              (((Matrix.PosSemidef.sqrt (M.hSigma n)).mulVec z) (M.g n (Fin.castLE hEll i)) /
                M.sigma n (M.g n (Fin.castLE hEll i))) := by
      intro z
      rw [hcgv1_mulVec]
      simp only [hSmulVec]
      refine Finset.sum_congr rfl ?_
      intro i _
      ring
    have hfun : ((fun w : Fin (M.p n) → ℝ => ∑ i : Fin (M.ell n),
        u i * (w (M.g n (Fin.castLE hEll i)) /
          (M.sigma n (M.g n (Fin.castLE hEll i))))) ∘
        (fun z => (Matrix.PosSemidef.sqrt (M.hSigma n)).mulVec z)) =
        (fun z : Fin (M.p n) → ℝ => ∑ j : Fin (M.ell n),
          u j * (S.mulVec ((Matrix.PosSemidef.sqrt (M.hSigma n)).mulVec
            (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector
              (1 : Matrix (Fin (M.p n)) (Fin (M.p n)) ℝ) z))) j) := by
      funext z
      exact (hpt z).symm
    have hQ : (∑ i : Fin (M.ell n), ∑ j : Fin (M.ell n),
        u i * (S * (Matrix.PosSemidef.sqrt (M.hSigma n) *
          (1 : Matrix (Fin (M.p n)) (Fin (M.p n)) ℝ) *
          (Matrix.PosSemidef.sqrt (M.hSigma n)).transpose) * S.transpose) i j * u j)
        = ∑ i : Fin (M.ell n), ∑ j : Fin (M.ell n),
          u i * M.corrMat n (M.ell n) hEll i j * u j := by
      rw [hmat]
    have hdot : ∀ (A : Matrix (Fin (M.ell n)) (Fin (M.ell n)) ℝ) (v : Fin (M.ell n) → ℝ),
        star v ⬝ᵥ A.mulVec v = ∑ i, ∑ j, v i * A i j * v j := by
      intro A v
      have h1 : star v ⬝ᵥ A.mulVec v =
          ∑ i : Fin (M.ell n), star (v i) * (∑ j : Fin (M.ell n), A i j * v j) := rfl
      rw [h1]
      simp only [star_trivial]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.mul_sum]
      simp only [mul_assoc]
    have hTnn : 0 ≤ ∑ i : Fin (M.ell n), ∑ j : Fin (M.ell n),
        u i * M.corrMat n (M.ell n) hEll i j * u j := by
      rw [← hQ]
      have h := Matrix.PosSemidef.dotProduct_mulVec_nonneg hPSDS u
      rw [hdot] at h
      exact h
    have htilde : M.tildeLaw n =
        (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi (M.p n)).map
          (fun z => (Matrix.PosSemidef.sqrt (M.hSigma n)).mulVec z) := rfl
    rw [htilde, Measure.map_map hFm hBm, hfun, hlaw]
    refine congrArg (fun v : NNReal => gaussianReal (0 : ℝ) v) ?_
    rw [Real.toNNReal_of_nonneg hTnn]
    exact Subtype.ext hQ
  have hE : ∀ j : Fin (M.p n),
      (M.tildeLaw n).map (fun w => w j / M.sigma n j) = gaussianReal 0 1 := by
    intro j
    have htilde : M.tildeLaw n =
        (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi (M.p n)).map
          (fun z => (Matrix.PosSemidef.sqrt (M.hSigma n)).mulVec z) := rfl
    have hBm : Measurable (fun z : Fin (M.p n) → ℝ =>
        (Matrix.PosSemidef.sqrt (M.hSigma n)).mulVec z) := by
      have heq : (fun z : Fin (M.p n) → ℝ =>
          (Matrix.PosSemidef.sqrt (M.hSigma n)).mulVec z) =
          (fun z i => ∑ j : Fin (M.p n),
            (Matrix.PosSemidef.sqrt (M.hSigma n)) i j * z j) := rfl
      rw [heq]
      measurability
    have hFm : Measurable (fun w : Fin (M.p n) → ℝ => w j / M.sigma n j) := by
      measurability
    have hlaw :=
      Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector.map_linearCombination
        (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi (M.p n))
        (fun z => (Matrix.PosSemidef.sqrt (M.hSigma n)).mulVec
          (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector
            (1 : Matrix (Fin (M.p n)) (Fin (M.p n)) ℝ) z))
        (Matrix.PosSemidef.sqrt (M.hSigma n) * 1 *
          (Matrix.PosSemidef.sqrt (M.hSigma n)).transpose)
        hCGVB hPSDB (fun l : Fin (M.p n) => if l = j then (M.sigma n j)⁻¹ else 0)
    have hpt : ∀ z : Fin (M.p n) → ℝ,
        (fun w : Fin (M.p n) → ℝ => w j / M.sigma n j)
            ((Matrix.PosSemidef.sqrt (M.hSigma n)).mulVec z) =
          ∑ l : Fin (M.p n), (if l = j then (M.sigma n j)⁻¹ else 0) *
            (Matrix.PosSemidef.sqrt (M.hSigma n)).mulVec
              (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector
                (1 : Matrix (Fin (M.p n)) (Fin (M.p n)) ℝ) z) l := by
      intro z
      rw [hcgv1_mulVec]
      have hsum : (∑ l : Fin (M.p n), (if l = j then (M.sigma n j)⁻¹ else 0) *
          (Matrix.PosSemidef.sqrt (M.hSigma n)).mulVec z l) =
          (M.sigma n j)⁻¹ * (Matrix.PosSemidef.sqrt (M.hSigma n)).mulVec z j := by
        simp
      rw [hsum]
      show (Matrix.PosSemidef.sqrt (M.hSigma n)).mulVec z j / M.sigma n j =
        (M.sigma n j)⁻¹ * (Matrix.PosSemidef.sqrt (M.hSigma n)).mulVec z j
      ring
    have hfun : ((fun w : Fin (M.p n) → ℝ => w j / M.sigma n j) ∘
        (fun z => (Matrix.PosSemidef.sqrt (M.hSigma n)).mulVec z)) =
        (fun z : Fin (M.p n) → ℝ => ∑ l : Fin (M.p n),
          (if l = j then (M.sigma n j)⁻¹ else 0) *
            (Matrix.PosSemidef.sqrt (M.hSigma n)).mulVec
              (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector
                (1 : Matrix (Fin (M.p n)) (Fin (M.p n)) ℝ) z) l) := by
      funext z
      exact hpt z
    have hQ : (∑ i : Fin (M.p n), ∑ l : Fin (M.p n),
        (if i = j then (M.sigma n j)⁻¹ else 0) *
          (Matrix.PosSemidef.sqrt (M.hSigma n) *
            (1 : Matrix (Fin (M.p n)) (Fin (M.p n)) ℝ) *
            (Matrix.PosSemidef.sqrt (M.hSigma n)).transpose) i l *
          (if l = j then (M.sigma n j)⁻¹ else 0)) = 1 := by
      rw [hBB]
      have hcollapse : (∑ i : Fin (M.p n), ∑ l : Fin (M.p n),
          (if i = j then (M.sigma n j)⁻¹ else 0) * M.Sigma n i l *
            (if l = j then (M.sigma n j)⁻¹ else 0)) =
          (M.sigma n j)⁻¹ * M.Sigma n j j * (M.sigma n j)⁻¹ := by
        simp
      rw [hcollapse]
      have hsq : (M.sigma n j) ^ 2 = M.Sigma n j j :=
        (statopia_math_node_3076116109_992c70da a c0 alpha cvar ccirc eps0 Ccor M hM n hn
          j j j).2.2
      have hs : M.sigma n j ≠ 0 := ne_of_gt (hM.hsig_pos n hn0 j)
      rw [← hsq, pow_two]
      field_simp
    rw [htilde, Measure.map_map hFm hBm, hfun, hlaw]
    congr 1
    exact Subtype.ext hQ
  have hD : ∀ i : Fin (M.ell n),
      (M.tildeLaw n).map
          (fun w => w (M.g n (Fin.castLE hEll i)) /
            (M.sigma n (M.g n (Fin.castLE hEll i))))
        = gaussianReal 0 1 := by
    intro i
    exact hE (M.g n (Fin.castLE hEll i))
  have hF : ∀ j : Fin (M.p n),
      (M.tildeLaw n).map (fun w => w j / (M.sigma n j) ^ (M.tau n))
        = (gaussianReal 0 1).map (fun z => (M.sigma n j) ^ (1 - M.tau n) * z) := by
    intro j
    have hp : (0 : ℝ) < M.sigma n j := hM.hsig_pos n hn0 j
    have hpt : ∀ w : Fin (M.p n) → ℝ,
        w j / (M.sigma n j) ^ (M.tau n)
          = (M.sigma n j) ^ (1 - M.tau n) * (w j / M.sigma n j) := by
      intro w
      have hptau : (M.sigma n j) ^ (M.tau n) ≠ 0 := (Real.rpow_pos_of_pos hp _).ne'
      have hsig : M.sigma n j ≠ 0 := hp.ne'
      rw [Real.rpow_sub hp, Real.rpow_one]
      field_simp
    have hfun : (fun w : Fin (M.p n) → ℝ => w j / (M.sigma n j) ^ (M.tau n))
        = (fun w : Fin (M.p n) → ℝ =>
            (M.sigma n j) ^ (1 - M.tau n) * (w j / M.sigma n j)) := funext hpt
    have hgm : Measurable (fun z : ℝ => (M.sigma n j) ^ (1 - M.tau n) * z) :=
      (continuous_const.mul continuous_id).measurable
    have hfm : Measurable (fun w : Fin (M.p n) → ℝ => w j / M.sigma n j) :=
      Measurable.div_const (f := fun w : Fin (M.p n) → ℝ => w j)
        (measurable_pi_apply j) (M.sigma n j)
    calc (M.tildeLaw n).map
          (fun w : Fin (M.p n) → ℝ => w j / (M.sigma n j) ^ (M.tau n))
        = (M.tildeLaw n).map (fun w : Fin (M.p n) → ℝ =>
            (M.sigma n j) ^ (1 - M.tau n) * (w j / M.sigma n j)) := by rw [hfun]
      _ = ((M.tildeLaw n).map (fun w : Fin (M.p n) → ℝ => w j / M.sigma n j)).map
            (fun z : ℝ => (M.sigma n j) ^ (1 - M.tau n) * z) := by
          rw [Measure.map_map hgm hfm]
          rfl
      _ = (gaussianReal 0 1).map
            (fun z : ℝ => (M.sigma n j) ^ (1 - M.tau n) * z) := by rw [hE j]
  refine ⟨hA, hB, hC, hD, hE, hF⟩
  /- @proof-region region.target-node.session.7a4c494f3a7c493b end -/

end
end Statlib.Imported

