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

noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_3076116109_992c70da : ∀ (a c0 alpha cvar ccirc eps0 Ccor : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (M : Model Ω μ a) (hM : Model.Assumptions M c0 alpha cvar ccirc eps0 Ccor)
    (n : ℕ) (hn : 1 ≤ n) (i j k : Fin (M.p n)),
    M.covX n i j = M.Sigma n i j ∧ M.covX n k k = M.Sigma n k k ∧
      (M.sigma n k) ^ 2 = M.Sigma n k k := by
  /- @proof-region region.target-node.session.2d321d5e78ada270 begin -/
  intro a c0 alpha cvar ccirc eps0 Ccor Ω hΩ μ hμ M hM n hn i j k
  haveI : IsProbabilityMeasure μ := hμ
  have hpos : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  set B : Matrix (Fin (M.p n)) (Fin (M.p n)) ℝ := Matrix.PosSemidef.sqrt (M.hSigma n) with hB
  set U : Matrix (Fin (M.p n)) (Fin (M.p n)) ℝ := ↑((M.hSigma n).isHermitian.eigenvectorUnitary) with hU
  set D : Matrix (Fin (M.p n)) (Fin (M.p n)) ℝ := Matrix.diagonal (RCLike.ofReal ∘ (fun x : ℝ => Real.sqrt x) ∘ (M.hSigma n).isHermitian.eigenvalues) with hD
  have hBform : B = U * D * star U := by
    simp only [hB, hU, hD, Matrix.PosSemidef.sqrt]
  have hstar : star U * U = 1 := by
    simp [hU]
  have hDD : D * D = Matrix.diagonal (RCLike.ofReal ∘ (M.hSigma n).isHermitian.eigenvalues) := by
    rw [hD, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [Function.comp_apply]
    rw [← Real.mul_self_sqrt (Matrix.PosSemidef.eigenvalues_nonneg (M.hSigma n) i)]
    simp
  have hBB : B * B = M.Sigma n := by
    calc B * B = (U * D * star U) * (U * D * star U) := by rw [hBform]
      _ = U * D * (star U * U) * D * star U := by noncomm_ring
      _ = U * D * (1 : Matrix (Fin (M.p n)) (Fin (M.p n)) ℝ) * D * star U := by rw [hstar]
      _ = U * (D * D) * star U := by noncomm_ring
      _ = U * Matrix.diagonal (RCLike.ofReal ∘ (M.hSigma n).isHermitian.eigenvalues) * star U := by rw [hDD]
      _ = M.Sigma n := by
            refine Eq.trans ?_ (Matrix.IsHermitian.spectral_theorem (M.hSigma n).isHermitian).symm
            rw [Unitary.conjStarAlgAut_apply, ← hU]
  have hBsym : B.transpose = B := by
    have hDstar : star D = D := by
      rw [hD]
      ext i j
      by_cases h : i = j
      · rw [h]
        simp [Matrix.diagonal]
      · simp [Matrix.diagonal, h, Ne.symm h]
    have h1 : star B = B := by
      rw [hBform]
      simp only [star_mul, star_star, hDstar]
      noncomm_ring
    ext i j
    simpa using congrFun (congrFun h1 i) j
  have hXB : ∀ (a : Fin (M.p n)) (ω : Ω),
      M.X n ⟨0, hpos⟩ ω a = M.mu n a + ∑ l, B a l * M.Z n ⟨0, hpos⟩ ω l := by
    intro a ω
    have h1 := congrFun (M.hmodel n ⟨0, hpos⟩ ω) a
    simp only [Pi.add_apply, ← hB] at h1
    exact h1
  have hmean : ∀ a : Fin (M.p n), ∫ ω, M.X n ⟨0, hpos⟩ ω a ∂μ = M.mu n a := by
    intro a
    have hsumInt : ∀ l : Fin (M.p n), Integrable (fun ω => B a l * M.Z n ⟨0, hpos⟩ ω l) μ :=
      fun l => (M.hZ_int n ⟨0, hpos⟩ l).const_mul (B a l)
    have hIntSum : Integrable (fun ω => ∑ l, B a l * M.Z n ⟨0, hpos⟩ ω l) μ :=
      MeasureTheory.integrable_finset_sum Finset.univ (fun l _ => hsumInt l)
    calc ∫ ω, M.X n ⟨0, hpos⟩ ω a ∂μ
        = ∫ ω, (M.mu n a + ∑ l, B a l * M.Z n ⟨0, hpos⟩ ω l) ∂μ := by
            simp only [hXB]
      _ = M.mu n a := by
            rw [MeasureTheory.integral_add (MeasureTheory.integrable_const _) hIntSum,
                MeasureTheory.integral_finset_sum Finset.univ (fun l _ => hsumInt l)]
            simp [MeasureTheory.integral_const_mul, M.hZ_mean]
  have hmain : ∀ (i j : Fin (M.p n)), M.covX n i j = M.Sigma n i j := by
    intro i j
    have hpt : ∀ ω : Ω,
        (M.X n ⟨0, hpos⟩ ω i - ∫ ω', M.X n ⟨0, hpos⟩ ω' i ∂μ)
          * (M.X n ⟨0, hpos⟩ ω j - ∫ ω', M.X n ⟨0, hpos⟩ ω' j ∂μ)
        = ∑ l, ∑ m, (B i l * B j m) * (M.Z n ⟨0, hpos⟩ ω l * M.Z n ⟨0, hpos⟩ ω m) := by
      intro ω
      rw [hmean i, hmean j, hXB i ω, hXB j ω]
      simp only [add_sub_cancel_left]
      rw [Finset.sum_mul_sum]
      exact Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun m _ => by ring))
    have hInner : ∀ l : Fin (M.p n),
        ∫ ω, (∑ m, (B i l * B j m) * (M.Z n ⟨0, hpos⟩ ω l * M.Z n ⟨0, hpos⟩ ω m)) ∂μ
          = B i l * B j l := by
      intro l
      rw [MeasureTheory.integral_finset_sum Finset.univ
        (fun m _ => (M.hZ_cov_int n ⟨0, hpos⟩ l m).const_mul (B i l * B j m))]
      simp only [MeasureTheory.integral_const_mul, M.hZ_cov, mul_boole, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]
    have hInt : ∫ ω, (∑ l, ∑ m, (B i l * B j m) * (M.Z n ⟨0, hpos⟩ ω l * M.Z n ⟨0, hpos⟩ ω m)) ∂μ
        = ∑ l, B i l * B j l := by
      rw [MeasureTheory.integral_finset_sum Finset.univ (fun l _ =>
        MeasureTheory.integrable_finset_sum Finset.univ (fun m _ =>
          (M.hZ_cov_int n ⟨0, hpos⟩ l m).const_mul (B i l * B j m)))]
      exact Finset.sum_congr rfl (fun l _ => hInner l)
    have hSumEq : ∑ l, B i l * B j l = M.Sigma n i j := by
      have h1 : ∑ l, B i l * B j l = (B * B.transpose) i j := by
        simp [Matrix.mul_apply, Matrix.transpose_apply]
      rw [h1, hBsym, hBB]
    simp only [covX, dif_pos hpos, covariance]
    calc ∫ ω, (M.X n ⟨0, hpos⟩ ω i - ∫ ω', M.X n ⟨0, hpos⟩ ω' i ∂μ)
            * (M.X n ⟨0, hpos⟩ ω j - ∫ ω', M.X n ⟨0, hpos⟩ ω' j ∂μ) ∂μ
        = ∫ ω, (∑ l, ∑ m, (B i l * B j m) * (M.Z n ⟨0, hpos⟩ ω l * M.Z n ⟨0, hpos⟩ ω m)) ∂μ := by
            congr 1
            funext ω
            exact hpt ω
      _ = ∑ l, B i l * B j l := hInt
      _ = M.Sigma n i j := hSumEq
  have hsigma : (M.sigma n k) ^ 2 = M.Sigma n k k := by
    have h1 : M.sigma n k = Real.sqrt (variance (fun ω => M.X n ⟨0, hpos⟩ ω k) μ) := by
      simp only [sigma, dif_pos hpos]
    have h3 : variance (fun ω => M.X n ⟨0, hpos⟩ ω k) μ
        = covariance (fun ω => M.X n ⟨0, hpos⟩ ω k) (fun ω => M.X n ⟨0, hpos⟩ ω k) μ := by
      have hmeas : AEMeasurable (fun ω => M.X n ⟨0, hpos⟩ ω k) μ :=
        (M.hX_memLp n ⟨0, hpos⟩ k).aestronglyMeasurable.aemeasurable
      exact (covariance_self hmeas).symm
    have h2 : variance (fun ω => M.X n ⟨0, hpos⟩ ω k) μ = M.covX n k k := by
      rw [h3]
      simp only [covX, dif_pos hpos]
    rw [h1]
    rw [Real.sq_sqrt (variance_nonneg (fun ω => M.X n ⟨0, hpos⟩ ω k) μ)]
    rw [h2, hmain k k]
  exact ⟨hmain i j, hmain k k, hsigma⟩
  /- @proof-region region.target-node.session.2d321d5e78ada270 end -/

end
end Statlib.Imported

