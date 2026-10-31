import Statlib.StatFoundation.Statistics.Asymptotic.ScoreCLT
import Statlib.StatFoundation.Convergence.Resampling.GaussianMaxComparison
import Statlib.StatFoundation.Convergence.AnalysisTools.GaussianMaxAnticoncentration
import Statlib.StatFoundation.Statistics.Asymptotic.LAN
import Statlib.StatFoundation.Convergence.AnalysisTools.SmoothMax
import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.Vocabulary
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.Base
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.ProvedNodes.Node_2427644982_7294da19_198768f7
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.ProvedNodes.Node_679072742_9b6183cb_723b14b4

namespace PaperProofTasks.job_paper_de3065fb922748188f3a0354eba90ed9

open _root_.PaperProofTasks.job_paper_de3065fb922748188f3a0354eba90ed9.Statlib.Imported
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

set_option autoImplicit false in
theorem statopia_math_node_1423981741_b7996ae4 : ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (p : ℕ) (hp : 1 ≤ p)
    (X : Ω → Fin p → ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (hGauss : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector μ X Sigma)
    (hL2 : ∀ j : Fin p, MemLp (fun ω => X ω j) 2 μ)
    (hpos : ∀ j : Fin p, 0 < ∫ ω, (X ω j) ^ 2 ∂μ)
    (hInt : Integrable (fun ω => ⨆ j : Fin p, X ω j / coordStdDev μ X j) μ)
    (x : ℝ),
    let s : ℝ := if 0 ≤ x then 1 / sigmaUnder μ X else 1 / sigmaOver μ X
    let muShift : Fin p → ℝ := fun j => x * (s - 1 / coordStdDev μ X j)
    let W : Ω → Fin p → ℝ := fun ω j => X ω j / coordStdDev μ X j + muShift j
    ∃ S : Finset (Fin p), S.Nonempty ∧
      (∀ j ∈ S, ∀ k ∈ S, j ≠ k →
        covariance (fun ω => X ω j / coordStdDev μ X j)
            (fun ω => X ω k / coordStdDev μ X k) μ /
          (Real.sqrt (variance (fun ω => X ω j / coordStdDev μ X j) μ) *
            Real.sqrt (variance (fun ω => X ω k / coordStdDev μ X k) μ)) < 1) ∧
      (μ {ω | (⨆ j : ↥S, W ω (j : Fin p)) = (⨆ j : Fin p, W ω j)} = 1) ∧
      (μ {ω | (⨆ j : ↥S, X ω (j : Fin p) / coordStdDev μ X (j : Fin p)) =
        (⨆ j : Fin p, X ω j / coordStdDev μ X j)} = 1) := by
  /- @proof-region region.target-node.session.810196326f294406 begin -/
  intro Ω _ μ _ p hp X Sigma hGauss hL2 hpos hInt x
  classical
  dsimp only
  obtain ⟨hμbd, hWsub, hmeanvar, hgauss, hmax⟩ :=
    statopia_math_node_2427644982_7294da19 μ p hp X Sigma hGauss hL2 hpos hInt x
  obtain ⟨hmax1, hmax2, hmax3, hmax4⟩ := hmax
  let u : Ω → Fin p → ℝ := fun ω j => X ω j / coordStdDev μ X j
  let s : ℝ := if 0 ≤ x then 1 / sigmaUnder μ X else 1 / sigmaOver μ X
  let muShift : Fin p → ℝ := fun j => x * (s - 1 / coordStdDev μ X j)
  let W : Ω → Fin p → ℝ := fun ω j => X ω j / coordStdDev μ X j + muShift j
  have hu_sq : ∀ j : Fin p, ∫ ω, (u ω j) ^ 2 ∂μ = 1 := by
    intro j
    have hi := (hmeanvar j).2.1
    have hs := (hmeanvar j).2.2
    rw [hs] at hi
    rw [← hi]
    congr 1
    funext ω
    simp only [u]
    rw [hWsub j ω]
  have hu_mem : ∀ j : Fin p, MemLp (fun ω => u ω j) 2 μ := by
    intro j
    have h := (hL2 j).mul_const (coordStdDev μ X j)⁻¹
    simpa only [u, div_eq_mul_inv] using h
  have hW_int : ∀ j : Fin p, Integrable (fun ω => W ω j) μ := by
    intro j
    have hu_int : Integrable (fun ω => u ω j) μ := (hu_mem j).integrable (by norm_num)
    have heq : (fun ω => W ω j) = fun ω => u ω j + muShift j := by
      funext ω; simp only [u, W]
    rw [heq]
    exact hu_int.add (integrable_const (muShift j))
  have hu_mean : ∀ j : Fin p, ∫ ω, u ω j ∂μ = 0 := by
    intro j
    have hWu : ∫ ω, W ω j ∂μ = muShift j := (hmeanvar j).1
    have hsplit : ∫ ω, u ω j ∂μ = ∫ ω, (W ω j - muShift j) ∂μ := by
      congr 1; funext ω; simp only [u, W]; ring
    rw [hsplit]
    have hsplit2 : ∫ ω, (W ω j - muShift j) ∂μ =
        ∫ ω, W ω j ∂μ - ∫ ω, (fun _ => muShift j) ω ∂μ :=
      integral_sub (hW_int j) (integrable_const _)
    rw [hsplit2, hWu]
    have hc : ∫ ω, (fun _ => muShift j) ω ∂μ = muShift j := by simp
    rw [hc]; ring
  have hu_var : ∀ j : Fin p, variance (fun ω => u ω j) μ = 1 := by
    intro j
    rw [variance_eq_integral (hu_mem j).aemeasurable, hu_mean j]
    simpa using hu_sq j
  have hu_cov : ∀ j k : Fin p,
      covariance (fun ω => u ω j) (fun ω => u ω k) μ = ∫ ω, u ω j * u ω k ∂μ := by
    intro j k
    rw [covariance_eq_sub (hu_mem j) (hu_mem k), hu_mean j, hu_mean k]
    simp
  obtain ⟨S, hSne, hcorr, hWmax, humax⟩ :=
    statopia_math_node_679072742_9b6183cb μ p hp
      (fun ω j => X ω j / coordStdDev μ X j) muShift hu_mem hu_sq
  refine ⟨S, hSne, ?_, ?_, ?_⟩
  · intro j hj k hk hjk
    have hlt := hcorr j hj k hk hjk
    have hcov : covariance (fun ω => X ω j / coordStdDev μ X j)
        (fun ω => X ω k / coordStdDev μ X k) μ = ∫ ω, u ω j * u ω k ∂μ := hu_cov j k
    have hvj : variance (fun ω => X ω j / coordStdDev μ X j) μ = 1 := hu_var j
    have hvk : variance (fun ω => X ω k / coordStdDev μ X k) μ = 1 := hu_var k
    have hsj : Real.sqrt (variance (fun ω => X ω j / coordStdDev μ X j) μ) = 1 := by
      rw [hvj]; exact Real.sqrt_one
    have hsk : Real.sqrt (variance (fun ω => X ω k / coordStdDev μ X k) μ) = 1 := by
      rw [hvk]; exact Real.sqrt_one
    rw [hcov, hsj, hsk, one_mul, div_one]
    exact hlt
  · exact hWmax
  · exact humax
  /- @proof-region region.target-node.session.810196326f294406 end -/

end Statlib.Imported

