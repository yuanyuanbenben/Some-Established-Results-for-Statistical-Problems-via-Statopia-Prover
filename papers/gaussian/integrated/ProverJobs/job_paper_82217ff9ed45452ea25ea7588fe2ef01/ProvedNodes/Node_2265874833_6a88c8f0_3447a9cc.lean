import ProverJobs.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Vocabulary
import ProverJobs.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Base

namespace PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators
open _root_.PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Statlib.Imported
open _root_.PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Statlib.Imported.Model

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators
namespace Statlib.Imported
open _root_.Statlib
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_2265874833_6a88c8f0 : ∀ (a c0 alpha cvar ccirc eps0 Ccor : ℝ)
    (halpha : 0 < alpha) (hccirc : ccirc ∈ Set.Ioo (0 : ℝ) 1)
    (heps0 : eps0 ∈ Set.Ioo (0 : ℝ) 1) (hCcor : 0 < Ccor)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (M : Model Ω μ a) (hM : Model.Assumptions M c0 alpha cvar ccirc eps0 Ccor)
    (n : ℕ) (hn : 1 ≤ n),
    (M.corrMat n (M.ell n) (M.ell_le_p n)).PosSemidef ∧
      Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector
        (M.tildeLaw n)
        (fun w (i : Fin (M.ell n)) =>
          w (M.g n (Fin.castLE (M.ell_le_p n) i)) /
            M.sigma n (M.g n (Fin.castLE (M.ell_le_p n) i)))
        (M.corrMat n (M.ell n) (M.ell_le_p n)) := by
  /- @proof-region region.target-node.session.7b4b78a5dbc56ed7 begin -/
  intro a c0 alpha cvar ccirc eps0 Ccor halpha hccirc heps0 hCcor Ω _ μ _ M hM n hn
  have hnpos : 0 < n := by omega
  set T : Matrix (Fin (M.p n)) (Fin (M.p n)) ℝ := Matrix.PosSemidef.sqrt (M.hSigma n) with hTdef
  set A : Matrix (Fin (M.ell n)) (Fin (M.p n)) ℝ :=
    Matrix.of (fun (i : Fin (M.ell n)) (j : Fin (M.p n)) =>
      T (M.g n (Fin.castLE (M.ell_le_p n) i)) j /
        M.sigma n (M.g n (Fin.castLE (M.ell_le_p n) i))) with hAdef
  have hTform : T = (↑((M.hSigma n).isHermitian.eigenvectorUnitary) :
        Matrix (Fin (M.p n)) (Fin (M.p n)) ℝ)
      * Matrix.diagonal (RCLike.ofReal ∘ Real.sqrt ∘ (M.hSigma n).isHermitian.eigenvalues)
      * star (↑((M.hSigma n).isHermitian.eigenvectorUnitary) :
        Matrix (Fin (M.p n)) (Fin (M.p n)) ℝ) := by
    rw [hTdef]
    unfold Matrix.PosSemidef.sqrt
    rfl
  have hDpsd : (Matrix.diagonal
      (RCLike.ofReal ∘ Real.sqrt ∘ (M.hSigma n).isHermitian.eigenvalues) :
        Matrix (Fin (M.p n)) (Fin (M.p n)) ℝ).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    simpa using Real.sqrt_nonneg ((M.hSigma n).isHermitian.eigenvalues i)
  have hSE : (↑((M.hSigma n).isHermitian.eigenvectorUnitary) :
        Matrix (Fin (M.p n)) (Fin (M.p n)) ℝ)
      * Matrix.diagonal (RCLike.ofReal ∘ (M.hSigma n).isHermitian.eigenvalues)
      * star (↑((M.hSigma n).isHermitian.eigenvectorUnitary) :
        Matrix (Fin (M.p n)) (Fin (M.p n)) ℝ) = M.Sigma n := by
    rw [show (↑((M.hSigma n).isHermitian.eigenvectorUnitary) :
          Matrix (Fin (M.p n)) (Fin (M.p n)) ℝ)
        * Matrix.diagonal (RCLike.ofReal ∘ (M.hSigma n).isHermitian.eigenvalues)
        * star (↑((M.hSigma n).isHermitian.eigenvectorUnitary) :
          Matrix (Fin (M.p n)) (Fin (M.p n)) ℝ)
        = (M.hSigma n).isHermitian.cfc (id : ℝ → ℝ) from rfl]
    rw [← Matrix.IsHermitian.cfc_eq (M.hSigma n).isHermitian (id : ℝ → ℝ)]
    exact cfc_id ℝ (M.Sigma n) (Matrix.IsHermitian.eq (M.hSigma n).isHermitian)
  have hUU : star (↑((M.hSigma n).isHermitian.eigenvectorUnitary) :
        Matrix (Fin (M.p n)) (Fin (M.p n)) ℝ)
      * (↑((M.hSigma n).isHermitian.eigenvectorUnitary) :
        Matrix (Fin (M.p n)) (Fin (M.p n)) ℝ) = 1 := by
    simpa using ((M.hSigma n).isHermitian.eigenvectorUnitary).2
  have hDD : (Matrix.diagonal (RCLike.ofReal ∘ Real.sqrt ∘ (M.hSigma n).isHermitian.eigenvalues)
      * Matrix.diagonal (RCLike.ofReal ∘ Real.sqrt ∘ (M.hSigma n).isHermitian.eigenvalues) :
        Matrix (Fin (M.p n)) (Fin (M.p n)) ℝ)
      = (Matrix.diagonal (RCLike.ofReal ∘ (M.hSigma n).isHermitian.eigenvalues) :
        Matrix (Fin (M.p n)) (Fin (M.p n)) ℝ) := by
    ext i j
    rw [Matrix.mul_apply]
    by_cases hij : i = j
    · subst hij
      simp [Matrix.diagonal,
        Real.mul_self_sqrt (Matrix.PosSemidef.eigenvalues_nonneg (M.hSigma n) i)]
    · simp [Matrix.diagonal, hij]
  have hTT : T * T = M.Sigma n := by
    rw [hTform]
    set U : Matrix (Fin (M.p n)) (Fin (M.p n)) ℝ :=
      ↑((M.hSigma n).isHermitian.eigenvectorUnitary) with hUdef
    set D : Matrix (Fin (M.p n)) (Fin (M.p n)) ℝ :=
      Matrix.diagonal (RCLike.ofReal ∘ Real.sqrt ∘ (M.hSigma n).isHermitian.eigenvalues) with hDdef
    have hUU' : star U * U = 1 := by
      rw [hUdef]
      exact hUU
    have hDD' : D * D
        = Matrix.diagonal (RCLike.ofReal ∘ (M.hSigma n).isHermitian.eigenvalues) := by
      rw [hDdef]
      exact hDD
    have hSE' : U * Matrix.diagonal (RCLike.ofReal ∘ (M.hSigma n).isHermitian.eigenvalues)
        * star U = M.Sigma n := by
      rw [hUdef]
      exact hSE
    calc (U * D * star U) * (U * D * star U)
        = U * D * (star U * U) * D * star U := by noncomm_ring
      _ = U * D * 1 * D * star U := by rw [hUU']
      _ = U * (D * D) * star U := by noncomm_ring
      _ = U * Matrix.diagonal (RCLike.ofReal ∘ (M.hSigma n).isHermitian.eigenvalues) * star U := by
            rw [hDD']
      _ = M.Sigma n := hSE'
  have hTpsd : T.PosSemidef := by
    rw [hTform]
    set U : Matrix (Fin (M.p n)) (Fin (M.p n)) ℝ :=
      ↑((M.hSigma n).isHermitian.eigenvectorUnitary) with hUdef
    set D : Matrix (Fin (M.p n)) (Fin (M.p n)) ℝ :=
      Matrix.diagonal (RCLike.ofReal ∘ Real.sqrt ∘ (M.hSigma n).isHermitian.eigenvalues) with hDdef
    have hD : D.PosSemidef := by
      rw [hDdef]
      exact hDpsd
    exact Matrix.PosSemidef.mul_mul_conjTranspose_same hD U
  have hTconj : T.conjTranspose = T :=
    Matrix.IsHermitian.eq (Matrix.PosSemidef.isHermitian hTpsd)
  have hsum : ∀ x y : Fin (M.p n), (∑ j : Fin (M.p n), T x j * T y j) = M.Sigma n x y := by
    intro x y
    rw [show (∑ j : Fin (M.p n), T x j * T y j) = (T * T.conjTranspose) x y from by
      rw [Matrix.mul_apply]
      simp [Matrix.conjTranspose_apply]]
    rw [hTconj, hTT]
  have hcov : ∀ a' b' : Fin (M.p n), M.covX n a' b' = M.Sigma n a' b' := by
    intro a' b'
    have hXa : (fun ω => M.X n ⟨0, hnpos⟩ ω a')
        = fun ω => M.mu n a' + ∑ j : Fin (M.p n), T a' j * M.Z n ⟨0, hnpos⟩ ω j := by
      funext ω
      rw [M.hmodel n ⟨0, hnpos⟩ ω, ← hTdef]
      rfl
    have hXb : (fun ω => M.X n ⟨0, hnpos⟩ ω b')
        = fun ω => M.mu n b' + ∑ j : Fin (M.p n), T b' j * M.Z n ⟨0, hnpos⟩ ω j := by
      funext ω
      rw [M.hmodel n ⟨0, hnpos⟩ ω, ← hTdef]
      rfl
    have hMa : MemLp (fun ω => M.X n ⟨0, hnpos⟩ ω a') 2 μ := M.hX_memLp n ⟨0, hnpos⟩ a'
    have hMb : MemLp (fun ω => M.X n ⟨0, hnpos⟩ ω b') 2 μ := M.hX_memLp n ⟨0, hnpos⟩ b'
    rw [covX, dif_pos hnpos, hXa, hXb]
    have hMa' : MemLp (fun ω => M.mu n a' + ∑ j : Fin (M.p n), T a' j * M.Z n ⟨0, hnpos⟩ ω j) 2 μ :=
      hXa ▸ hMa
    have hMb' : MemLp (fun ω => M.mu n b' + ∑ j : Fin (M.p n), T b' j * M.Z n ⟨0, hnpos⟩ ω j) 2 μ :=
      hXb ▸ hMb
    rw [covariance_eq_sub hMa' hMb']
    simp only [Pi.mul_apply]
    have hIa : ∫ ω, (M.mu n a' + ∑ j : Fin (M.p n), T a' j * M.Z n ⟨0, hnpos⟩ ω j) ∂μ
        = M.mu n a' := by
      have hint : ∀ j : Fin (M.p n), Integrable (fun ω => T a' j * M.Z n ⟨0, hnpos⟩ ω j) μ :=
        fun j => (M.hZ_int n ⟨0, hnpos⟩ j).const_mul (T a' j)
      have hzero : ∀ j : Fin (M.p n), ∫ ω, T a' j * M.Z n ⟨0, hnpos⟩ ω j ∂μ = 0 := by
        intro j
        rw [integral_const_mul, M.hZ_mean n ⟨0, hnpos⟩ j, mul_zero]
      rw [integral_add (integrable_const (M.mu n a'))
          (integrable_finset_sum Finset.univ (fun j _ => hint j)),
        integral_finset_sum Finset.univ (fun j _ => hint j)]
      simp [hzero]
    have hIb : ∫ ω, (M.mu n b' + ∑ j : Fin (M.p n), T b' j * M.Z n ⟨0, hnpos⟩ ω j) ∂μ
        = M.mu n b' := by
      have hint : ∀ j : Fin (M.p n), Integrable (fun ω => T b' j * M.Z n ⟨0, hnpos⟩ ω j) μ :=
        fun j => (M.hZ_int n ⟨0, hnpos⟩ j).const_mul (T b' j)
      have hzero : ∀ j : Fin (M.p n), ∫ ω, T b' j * M.Z n ⟨0, hnpos⟩ ω j ∂μ = 0 := by
        intro j
        rw [integral_const_mul, M.hZ_mean n ⟨0, hnpos⟩ j, mul_zero]
      rw [integral_add (integrable_const (M.mu n b'))
          (integrable_finset_sum Finset.univ (fun j _ => hint j)),
        integral_finset_sum Finset.univ (fun j _ => hint j)]
      simp [hzero]
    have hIab : ∫ ω, (M.mu n a' + ∑ j : Fin (M.p n), T a' j * M.Z n ⟨0, hnpos⟩ ω j)
        * (M.mu n b' + ∑ j : Fin (M.p n), T b' j * M.Z n ⟨0, hnpos⟩ ω j) ∂μ
        = M.mu n a' * M.mu n b' + M.Sigma n a' b' := by
      have hAint : Integrable (fun ω => ∑ j : Fin (M.p n), T a' j * M.Z n ⟨0, hnpos⟩ ω j) μ :=
        integrable_finset_sum Finset.univ
          (fun j _ => (M.hZ_int n ⟨0, hnpos⟩ j).const_mul (T a' j))
      have hBint : Integrable (fun ω => ∑ j : Fin (M.p n), T b' j * M.Z n ⟨0, hnpos⟩ ω j) μ :=
        integrable_finset_sum Finset.univ
          (fun j _ => (M.hZ_int n ⟨0, hnpos⟩ j).const_mul (T b' j))
      have hA0 : ∫ ω, (∑ j : Fin (M.p n), T a' j * M.Z n ⟨0, hnpos⟩ ω j) ∂μ = 0 := by
        rw [integral_finset_sum Finset.univ
          (fun j _ => (M.hZ_int n ⟨0, hnpos⟩ j).const_mul (T a' j))]
        have hzero : ∀ j : Fin (M.p n), ∫ ω, T a' j * M.Z n ⟨0, hnpos⟩ ω j ∂μ = 0 := by
          intro j
          rw [integral_const_mul, M.hZ_mean n ⟨0, hnpos⟩ j, mul_zero]
        simp [hzero]
      have hB0 : ∫ ω, (∑ j : Fin (M.p n), T b' j * M.Z n ⟨0, hnpos⟩ ω j) ∂μ = 0 := by
        rw [integral_finset_sum Finset.univ
          (fun j _ => (M.hZ_int n ⟨0, hnpos⟩ j).const_mul (T b' j))]
        have hzero : ∀ j : Fin (M.p n), ∫ ω, T b' j * M.Z n ⟨0, hnpos⟩ ω j ∂μ = 0 := by
          intro j
          rw [integral_const_mul, M.hZ_mean n ⟨0, hnpos⟩ j, mul_zero]
        simp [hzero]
      have hint : ∀ j l : Fin (M.p n),
          Integrable (fun ω => (T a' j * M.Z n ⟨0, hnpos⟩ ω j)
            * (T b' l * M.Z n ⟨0, hnpos⟩ ω l)) μ := by
        intro j l
        have hpt2 : (fun ω => (T a' j * M.Z n ⟨0, hnpos⟩ ω j)
            * (T b' l * M.Z n ⟨0, hnpos⟩ ω l))
            = fun ω => (T a' j * T b' l)
              * (M.Z n ⟨0, hnpos⟩ ω j * M.Z n ⟨0, hnpos⟩ ω l) :=
          funext (fun ω => by ring)
        rw [hpt2]
        exact (M.hZ_cov_int n ⟨0, hnpos⟩ j l).const_mul (T a' j * T b' l)
      have hterm : ∀ j l : Fin (M.p n),
          ∫ ω, (T a' j * M.Z n ⟨0, hnpos⟩ ω j) * (T b' l * M.Z n ⟨0, hnpos⟩ ω l) ∂μ
            = T a' j * T b' l * (if j = l then 1 else 0) := by
        intro j l
        have hpt2 : (fun ω => (T a' j * M.Z n ⟨0, hnpos⟩ ω j)
            * (T b' l * M.Z n ⟨0, hnpos⟩ ω l))
            = fun ω => (T a' j * T b' l)
              * (M.Z n ⟨0, hnpos⟩ ω j * M.Z n ⟨0, hnpos⟩ ω l) :=
          funext (fun ω => by ring)
        rw [hpt2, integral_const_mul, M.hZ_cov n ⟨0, hnpos⟩ j l]
      have hABval : ∫ ω, (∑ j : Fin (M.p n), T a' j * M.Z n ⟨0, hnpos⟩ ω j)
          * (∑ l : Fin (M.p n), T b' l * M.Z n ⟨0, hnpos⟩ ω l) ∂μ = M.Sigma n a' b' := by
        have hpt : (fun ω => (∑ j : Fin (M.p n), T a' j * M.Z n ⟨0, hnpos⟩ ω j)
            * (∑ l : Fin (M.p n), T b' l * M.Z n ⟨0, hnpos⟩ ω l))
            = fun ω => ∑ j : Fin (M.p n), ∑ l : Fin (M.p n),
                (T a' j * M.Z n ⟨0, hnpos⟩ ω j) * (T b' l * M.Z n ⟨0, hnpos⟩ ω l) := by
          funext ω
          rw [Finset.sum_mul]
          simp only [Finset.mul_sum]
        rw [hpt, integral_finset_sum Finset.univ
          (fun j _ => integrable_finset_sum Finset.univ (fun l _ => hint j l))]
        have hstep : ∀ j : Fin (M.p n),
            ∫ ω, (∑ l : Fin (M.p n), (T a' j * M.Z n ⟨0, hnpos⟩ ω j)
              * (T b' l * M.Z n ⟨0, hnpos⟩ ω l)) ∂μ
              = ∑ l : Fin (M.p n), T a' j * T b' l * (if j = l then 1 else 0) := by
          intro j
          rw [integral_finset_sum Finset.univ (fun l _ => hint j l)]
          exact Finset.sum_congr rfl (fun l _ => hterm j l)
        simp only [hstep]
        have hcol : ∀ j : Fin (M.p n),
            (∑ l : Fin (M.p n), T a' j * T b' l * (if j = l then 1 else 0))
              = T a' j * T b' j := by
          intro j
          simp
        simp only [hcol]
        exact hsum a' b'
      have hABint : Integrable (fun ω => (∑ j : Fin (M.p n), T a' j * M.Z n ⟨0, hnpos⟩ ω j)
          * (∑ l : Fin (M.p n), T b' l * M.Z n ⟨0, hnpos⟩ ω l)) μ := by
        have hpt : (fun ω => (∑ j : Fin (M.p n), T a' j * M.Z n ⟨0, hnpos⟩ ω j)
            * (∑ l : Fin (M.p n), T b' l * M.Z n ⟨0, hnpos⟩ ω l))
            = fun ω => ∑ j : Fin (M.p n), ∑ l : Fin (M.p n),
                (T a' j * M.Z n ⟨0, hnpos⟩ ω j) * (T b' l * M.Z n ⟨0, hnpos⟩ ω l) := by
          funext ω
          rw [Finset.sum_mul]
          simp only [Finset.mul_sum]
        rw [hpt]
        exact integrable_finset_sum Finset.univ
          (fun j _ => integrable_finset_sum Finset.univ (fun l _ => hint j l))
      have hpt3 : (fun ω => (M.mu n a' + ∑ j : Fin (M.p n), T a' j * M.Z n ⟨0, hnpos⟩ ω j)
          * (M.mu n b' + ∑ j : Fin (M.p n), T b' j * M.Z n ⟨0, hnpos⟩ ω j))
          = fun ω => M.mu n a' * M.mu n b'
              + (M.mu n a' * (∑ j : Fin (M.p n), T b' j * M.Z n ⟨0, hnpos⟩ ω j)
                + (M.mu n b' * (∑ j : Fin (M.p n), T a' j * M.Z n ⟨0, hnpos⟩ ω j)
                  + (∑ j : Fin (M.p n), T a' j * M.Z n ⟨0, hnpos⟩ ω j)
                    * (∑ j : Fin (M.p n), T b' j * M.Z n ⟨0, hnpos⟩ ω j))) :=
        funext (fun ω => by ring)
      have hI1 : Integrable (fun ω => M.mu n a'
          * (∑ j : Fin (M.p n), T b' j * M.Z n ⟨0, hnpos⟩ ω j)) μ :=
        hBint.const_mul (M.mu n a')
      have hI2 : Integrable (fun ω => M.mu n b'
          * (∑ j : Fin (M.p n), T a' j * M.Z n ⟨0, hnpos⟩ ω j)) μ :=
        hAint.const_mul (M.mu n b')
      have hI3 : Integrable (fun ω => (∑ j : Fin (M.p n), T a' j * M.Z n ⟨0, hnpos⟩ ω j)
          * (∑ l : Fin (M.p n), T b' l * M.Z n ⟨0, hnpos⟩ ω l)) μ := hABint
      have hI23 : Integrable (fun ω => M.mu n b'
          * (∑ j : Fin (M.p n), T a' j * M.Z n ⟨0, hnpos⟩ ω j)
          + (∑ j : Fin (M.p n), T a' j * M.Z n ⟨0, hnpos⟩ ω j)
            * (∑ l : Fin (M.p n), T b' l * M.Z n ⟨0, hnpos⟩ ω l)) μ := hI2.add hI3
      have hI123 : Integrable (fun ω => M.mu n a'
          * (∑ j : Fin (M.p n), T b' j * M.Z n ⟨0, hnpos⟩ ω j)
          + (M.mu n b' * (∑ j : Fin (M.p n), T a' j * M.Z n ⟨0, hnpos⟩ ω j)
            + (∑ j : Fin (M.p n), T a' j * M.Z n ⟨0, hnpos⟩ ω j)
              * (∑ l : Fin (M.p n), T b' l * M.Z n ⟨0, hnpos⟩ ω l))) μ := hI1.add hI23
      have hIc : ∫ ω, M.mu n a'
          * (∑ j : Fin (M.p n), T b' j * M.Z n ⟨0, hnpos⟩ ω j) ∂μ = 0 := by
        rw [integral_const_mul, hB0, mul_zero]
      have hId : ∫ ω, M.mu n b'
          * (∑ j : Fin (M.p n), T a' j * M.Z n ⟨0, hnpos⟩ ω j) ∂μ = 0 := by
        rw [integral_const_mul, hA0, mul_zero]
      have hIcd : ∫ ω, M.mu n a' * M.mu n b' ∂μ = M.mu n a' * M.mu n b' := by
        simp
      rw [hpt3,
        integral_add (integrable_const (M.mu n a' * M.mu n b')) hI123,
        integral_add hI1 hI23,
        integral_add hI2 hI3]
      rw [hIc, hId, hIcd, hABval]
      ring
    rw [hIa, hIb, hIab]
    ring
  have hAAT : A * A.transpose = M.corrMat n (M.ell n) (M.ell_le_p n) := by
    ext i j
    have h1 : (A * A.transpose) i j
        = (∑ k : Fin (M.p n),
            T (M.g n (Fin.castLE (M.ell_le_p n) i)) k
              * T (M.g n (Fin.castLE (M.ell_le_p n) j)) k)
          / (M.sigma n (M.g n (Fin.castLE (M.ell_le_p n) i))
            * M.sigma n (M.g n (Fin.castLE (M.ell_le_p n) j))) := by
      rw [Matrix.mul_apply]
      have h2 : ∀ k : Fin (M.p n), A i k * A.transpose k j
          = (T (M.g n (Fin.castLE (M.ell_le_p n) i)) k
              * T (M.g n (Fin.castLE (M.ell_le_p n) j)) k)
            / (M.sigma n (M.g n (Fin.castLE (M.ell_le_p n) i))
              * M.sigma n (M.g n (Fin.castLE (M.ell_le_p n) j))) := by
        intro k
        rw [Matrix.transpose_apply, hAdef]
        simp only [Matrix.of_apply]
        rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
        ring
      simp only [h2]
      rw [Finset.sum_div]
    rw [h1, hsum (M.g n (Fin.castLE (M.ell_le_p n) i)) (M.g n (Fin.castLE (M.ell_le_p n) j)),
      ← hcov (M.g n (Fin.castLE (M.ell_le_p n) i)) (M.g n (Fin.castLE (M.ell_le_p n) j))]
    simp only [corrMat, Matrix.of_apply, corrEntry]
  have hpsd : (M.corrMat n (M.ell n) (M.ell_le_p n)).PosSemidef := by
    have hconj : A.conjTranspose = A.transpose := by
      ext i j
      simp [Matrix.conjTranspose_apply]
    rw [← hAAT, ← hconj]
    exact Matrix.posSemidef_self_mul_conjTranspose A
  have hicgv : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector
      (M.tildeLaw n)
      (fun w (i : Fin (M.ell n)) =>
        w (M.g n (Fin.castLE (M.ell_le_p n) i)) /
          M.sigma n (M.g n (Fin.castLE (M.ell_le_p n) i)))
      (M.corrMat n (M.ell n) (M.ell_le_p n)) := by
    have hZmeas : Measurable (fun (w : Fin (M.p n) → ℝ) (i : Fin (M.ell n)) =>
        w (M.g n (Fin.castLE (M.ell_le_p n) i)) /
          M.sigma n (M.g n (Fin.castLE (M.ell_le_p n) i))) := by
      fun_prop
    have hTmeas : Measurable (fun w : Fin (M.p n) → ℝ => T.mulVec w) := by
      apply measurable_pi_iff.2
      intro i
      show Measurable (fun w : Fin (M.p n) → ℝ => ∑ j : Fin (M.p n), T i j * w j)
      fun_prop
    have htilde : M.tildeLaw n
        = (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi (M.p n)).map
            (fun w : Fin (M.p n) → ℝ => T.mulVec w) := by
      rw [tildeLaw, ← hTdef]
      rfl
    have hbase : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector
        (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi (M.p n))
        (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector
          (1 : Matrix (Fin (M.p n)) (Fin (M.p n)) ℝ))
        (1 : Matrix (Fin (M.p n)) (Fin (M.p n)) ℝ) :=
      Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector_isCenteredGaussianVector
        (by have h := M.hp n; omega) (1 : Matrix (Fin (M.p n)) (Fin (M.p n)) ℝ) Matrix.PosSemidef.one
    haveI hstdprob : IsProbabilityMeasure
        (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi (M.p n)) :=
      Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.standardPi_probability_productIntegrationByParts
        (M.p n)
    have hAI0 := Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector.linearImage
      (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi (M.p n))
      (Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector
        (1 : Matrix (Fin (M.p n)) (Fin (M.p n)) ℝ))
      (1 : Matrix (Fin (M.p n)) (Fin (M.p n)) ℝ) hbase A
    have hAI : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector
        (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi (M.p n))
        (fun z : Fin (M.p n) → ℝ => A.mulVec z)
        (A * (1 : Matrix (Fin (M.p n)) (Fin (M.p n)) ℝ) * A.transpose) := by
      simpa [Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.identity_canonicalGaussianVector]
        using hAI0
    have hpt : ∀ (z : Fin (M.p n) → ℝ) (i : Fin (M.ell n)),
        T.mulVec z (M.g n (Fin.castLE (M.ell_le_p n) i)) /
          M.sigma n (M.g n (Fin.castLE (M.ell_le_p n) i)) = A.mulVec z i := by
      intro z i
      show (∑ j : Fin (M.p n), T (M.g n (Fin.castLE (M.ell_le_p n) i)) j * z j)
            / M.sigma n (M.g n (Fin.castLE (M.ell_le_p n) i))
          = ∑ j : Fin (M.p n), (T (M.g n (Fin.castLE (M.ell_le_p n) i)) j
              / M.sigma n (M.g n (Fin.castLE (M.ell_le_p n) i))) * z j
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl (fun k _ => by
        rw [div_eq_mul_inv, div_eq_mul_inv]; ring)
    have hFm : ∀ u : Fin (M.ell n) → ℝ, Measurable (fun ω : Fin (M.p n) → ℝ =>
        Real.exp (∑ j : Fin (M.ell n), u j *
          (fun w (i : Fin (M.ell n)) => w (M.g n (Fin.castLE (M.ell_le_p n) i)) /
            M.sigma n (M.g n (Fin.castLE (M.ell_le_p n) i))) ω j)) := by
      intro u
      fun_prop
    have hFfun : ∀ u : Fin (M.ell n) → ℝ,
        ((fun ω : Fin (M.p n) → ℝ => Real.exp (∑ j : Fin (M.ell n), u j *
            (fun w (i : Fin (M.ell n)) => w (M.g n (Fin.castLE (M.ell_le_p n) i)) /
              M.sigma n (M.g n (Fin.castLE (M.ell_le_p n) i))) ω j))
          ∘ (fun w : Fin (M.p n) → ℝ => T.mulVec w))
          = (fun z : Fin (M.p n) → ℝ =>
              Real.exp (∑ j : Fin (M.ell n), u j * (A.mulVec z) j)) := by
      intro u
      funext z
      simp only [Function.comp_apply]
      congr 1
      exact Finset.sum_congr rfl (fun k _ => by rw [hpt z k])
    refine ⟨hZmeas, ?_, ?_⟩
    · intro u
      rw [htilde]
      refine (MeasureTheory.integrable_map_measure (hFm u).aestronglyMeasurable
        hTmeas.aemeasurable).2 ?_
      rw [hFfun u]
      exact hAI.integrable_exp u
    · intro u
      have hInt : ∫ ω : Fin (M.p n) → ℝ, Real.exp (∑ j : Fin (M.ell n), u j *
            (fun w (i : Fin (M.ell n)) => w (M.g n (Fin.castLE (M.ell_le_p n) i)) /
              M.sigma n (M.g n (Fin.castLE (M.ell_le_p n) i))) ω j) ∂(M.tildeLaw n)
          = ∫ z : Fin (M.p n) → ℝ,
              Real.exp (∑ j : Fin (M.ell n), u j * (A.mulVec z) j)
              ∂(Statlib.StatFoundation.RandomVariable.Gaussian.standardPi (M.p n)) := by
        rw [htilde]
        rw [MeasureTheory.integral_map hTmeas.aemeasurable (hFm u).aestronglyMeasurable]
        refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
        show Real.exp (∑ j : Fin (M.ell n), u j *
            (T.mulVec z (M.g n (Fin.castLE (M.ell_le_p n) j)) /
              M.sigma n (M.g n (Fin.castLE (M.ell_le_p n) j))))
          = Real.exp (∑ j : Fin (M.ell n), u j * (A.mulVec z) j)
        congr 1
        exact Finset.sum_congr rfl (fun k _ => by rw [hpt z k])
      rw [hInt, hAI.mgf_eq u]
      rw [Matrix.mul_one, hAAT]
  exact ⟨hpsd, hicgv⟩
  /- @proof-region region.target-node.session.7b4b78a5dbc56ed7 end -/

end
end Statlib.Imported

