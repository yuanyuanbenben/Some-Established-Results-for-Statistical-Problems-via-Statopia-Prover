import Statlib.StatFoundation.Statistics.Asymptotic.ScoreCLT
import Statlib.StatFoundation.Convergence.Resampling.GaussianMaxComparison
import Statlib.StatFoundation.Convergence.AnalysisTools.GaussianMaxAnticoncentration
import Statlib.StatFoundation.Statistics.Asymptotic.LAN
import Statlib.StatFoundation.Convergence.AnalysisTools.SmoothMax
import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.Vocabulary
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.Base
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.ProvedNodes.Node_154348488_06fea6fe_e7bb9c8f
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.ProvedNodes.Node_2322479387_a1995076_a2e043f8

namespace PaperProofTasks.job_paper_de3065fb922748188f3a0354eba90ed9
open _root_.PaperProofTasks.job_paper_de3065fb922748188f3a0354eba90ed9.Statlib.Imported
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

set_option autoImplicit false in
theorem statopia_math_node_2427644982_7294da19 : ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
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
    (∀ j : Fin p,
        0 ≤ muShift j ∧ muShift j ≤ (1 / sigmaUnder μ X - 1 / sigmaOver μ X) * |x|) ∧
    (∀ (j : Fin p) (ω : Ω), W ω j - muShift j = X ω j / coordStdDev μ X j) ∧
    (∀ j : Fin p,
        (∫ ω, W ω j ∂μ = muShift j) ∧
          (∫ ω, (W ω j - muShift j) ^ 2 ∂μ = variance (fun ω => W ω j) μ) ∧
          (variance (fun ω => W ω j) μ = 1)) ∧
    (IsGaussian (Measure.map (fun ω => fun j => W ω j) μ) ∧
      (∃ SigmaZ : Matrix (Fin p) (Fin p) ℝ,
        Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector μ
          (fun ω j => W ω j - muShift j) SigmaZ) ∧
      (∀ j : Fin p, ∫ ω, (W ω j - muShift j) ^ 2 ∂μ = 1)) ∧
    ((∀ ω : Ω,
        (⨆ j : Fin p, W ω j) - x * s = ⨆ j : Fin p, (X ω j - x) / coordStdDev μ X j) ∧
      (∀ ω : Ω,
        (⨆ j : Fin p, (W ω j - muShift j)) = ⨆ j : Fin p, X ω j / coordStdDev μ X j) ∧
      (∫ ω, (⨆ j : Fin p, (W ω j - muShift j)) ∂μ = standardizedMaxMean μ X) ∧
      0 ≤ standardizedMaxMean μ X) := by
  /- @proof-region region.target-node.session.093430f74bd58a0b begin -/
  intro Ω mΩ μ hμ p hp X Sigma hGauss hL2 hpos hInt x
  let s : ℝ := if 0 ≤ x then 1 / sigmaUnder μ X else 1 / sigmaOver μ X

  let muShift : Fin p → ℝ := fun j => x * (s - 1 / coordStdDev μ X j)
  let W : Ω → Fin p → ℝ := fun ω j => X ω j / coordStdDev μ X j + muShift j
  have h2 : ∀ (j : Fin p) (ω : Ω), W ω j - muShift j = X ω j / coordStdDev μ X j := by
    intro j ω
    show X ω j / coordStdDev μ X j + muShift j - muShift j = X ω j / coordStdDev μ X j
    ring
  have h5b : ∀ ω : Ω,
      (⨆ j : Fin p, (W ω j - muShift j)) = ⨆ j : Fin p, X ω j / coordStdDev μ X j := by
    intro ω
    refine iSup_congr (fun j => ?_)
    show X ω j / coordStdDev μ X j + muShift j - muShift j = X ω j / coordStdDev μ X j
    ring
  refine ⟨?_, h2, ?_, ?_, ?_⟩
  · intro j
    haveI : Nonempty (Fin p) := ⟨j⟩
    have hσpos : ∀ k : Fin p, 0 < coordStdDev μ X k := fun k => by
      show 0 < Real.sqrt (∫ ω, (X ω k) ^ 2 ∂μ)
      exact Real.sqrt_pos_of_pos (hpos k)
    have hbddB : BddBelow (Set.range (fun k : Fin p => coordStdDev μ X k)) :=
      ⟨0, by rintro _ ⟨k, rfl⟩; exact (hσpos k).le⟩
    have hbddA : BddAbove (Set.range (fun k : Fin p => coordStdDev μ X k)) :=
      ⟨(Finset.univ : Finset (Fin p)).sup' ⟨j, Finset.mem_univ j⟩ (fun k => coordStdDev μ X k),
        by rintro _ ⟨k, rfl⟩; exact Finset.le_sup' (fun k => coordStdDev μ X k) (Finset.mem_univ k)⟩
    have hunder_le : sigmaUnder μ X ≤ coordStdDev μ X j := by
      show (⨅ k : Fin p, coordStdDev μ X k) ≤ coordStdDev μ X j
      exact ciInf_le hbddB j
    have hover_ge : coordStdDev μ X j ≤ sigmaOver μ X := by
      show coordStdDev μ X j ≤ (⨆ k : Fin p, coordStdDev μ X k)
      exact le_ciSup hbddA j
    have hunder_pos : 0 < sigmaUnder μ X := by
      show 0 < (⨅ k : Fin p, coordStdDev μ X k)
      rw [← Finset.inf'_univ_eq_ciInf]
      exact (Finset.lt_inf'_iff ⟨j, Finset.mem_univ j⟩).2 (fun b _ => hσpos b)
    have hle1 : 1 / coordStdDev μ X j ≤ 1 / sigmaUnder μ X :=
      one_div_le_one_div_of_le hunder_pos hunder_le
    have hle2 : 1 / sigmaOver μ X ≤ 1 / coordStdDev μ X j :=
      one_div_le_one_div_of_le (hσpos j) hover_ge
    by_cases hx : 0 ≤ x
    · rw [if_pos hx]
      refine ⟨?_, ?_⟩
      · calc 0 = x * 0 := by ring
          _ ≤ x * (1 / sigmaUnder μ X - 1 / coordStdDev μ X j) :=
              mul_le_mul_of_nonneg_left (by linarith) hx
      · calc x * (1 / sigmaUnder μ X - 1 / coordStdDev μ X j)
            ≤ x * (1 / sigmaUnder μ X - 1 / sigmaOver μ X) :=
              mul_le_mul_of_nonneg_left (by linarith) hx
          _ = (1 / sigmaUnder μ X - 1 / sigmaOver μ X) * |x| := by
              rw [abs_of_nonneg hx]; ring
    · rw [if_neg hx]
      have hx' : x < 0 := not_le.1 hx
      refine ⟨?_, ?_⟩
      · calc 0 = (-x) * 0 := by ring
          _ ≤ (-x) * (1 / coordStdDev μ X j - 1 / sigmaOver μ X) :=
              mul_le_mul_of_nonneg_left (by linarith) (by linarith)
          _ = x * (1 / sigmaOver μ X - 1 / coordStdDev μ X j) := by ring
      · calc x * (1 / sigmaOver μ X - 1 / coordStdDev μ X j)
            = (-x) * (1 / coordStdDev μ X j - 1 / sigmaOver μ X) := by ring
          _ ≤ (-x) * (1 / sigmaUnder μ X - 1 / sigmaOver μ X) :=
              mul_le_mul_of_nonneg_left (by linarith) (by linarith)
          _ = (1 / sigmaUnder μ X - 1 / sigmaOver μ X) * |x| := by
              rw [abs_of_neg hx']; ring

  · intro j
    have hmean : ∀ k : Fin p, ∫ ω, X ω k ∂μ = 0 :=
      statopia_math_node_154348488_06fea6fe μ p hp X Sigma hGauss hL2
    have hσj : 0 < coordStdDev μ X j := by
      show 0 < Real.sqrt (∫ ω, (X ω j) ^ 2 ∂μ)
      exact Real.sqrt_pos_of_pos (hpos j)
    have hintX : Integrable (fun ω => X ω j) μ := (hL2 j).integrable (by norm_num)
    have hintDiv : Integrable (fun ω => X ω j / coordStdDev μ X j) μ := hintX.div_const _
    have hzeroInt : ∫ ω, X ω j / coordStdDev μ X j ∂μ = 0 := by
      simp only [div_eq_mul_inv, integral_mul_const, hmean j, zero_mul]
    have hWj : ∫ ω, W ω j ∂μ = muShift j := by
      calc ∫ ω, W ω j ∂μ
          = ∫ ω, (X ω j / coordStdDev μ X j + muShift j) ∂μ := rfl
        _ = ∫ ω, X ω j / coordStdDev μ X j ∂μ + ∫ ω, muShift j ∂μ :=
            integral_add hintDiv (integrable_const _)
        _ = muShift j := by
            rw [hzeroInt, zero_add]
            simp
    have hA : AEMeasurable (fun ω => W ω j) μ :=
      ((hL2 j).aemeasurable.div_const (coordStdDev μ X j)).add_const (muShift j)
    have hσ2 : coordStdDev μ X j ^ 2 = ∫ ω, (X ω j) ^ 2 ∂μ := by
      show Real.sqrt (∫ ω, (X ω j) ^ 2 ∂μ) ^ 2 = ∫ ω, (X ω j) ^ 2 ∂μ
      exact Real.sq_sqrt (hpos j).le
    have hpt : ∀ ω : Ω,
        (W ω j - muShift j) ^ 2 = (X ω j) ^ 2 * (coordStdDev μ X j ^ 2)⁻¹ := by
      intro ω
      simp only [h2 j ω, div_eq_mul_inv, mul_pow, inv_pow]
    refine ⟨hWj, ?_, ?_⟩
    · show ∫ ω, (W ω j - muShift j) ^ 2 ∂μ = variance (fun ω => W ω j) μ
      rw [variance_eq_integral hA]
      simp only [hWj]
    · rw [variance_eq_integral hA, hWj]
      simp only [hpt, integral_mul_const, ← hσ2]
      exact mul_inv_cancel₀ (pow_ne_zero 2 (ne_of_gt hσj))
  · refine ⟨?_, ?_, ?_⟩
    · show IsGaussian (Measure.map (fun ω => fun j => X ω j / coordStdDev μ X j + muShift j) μ)
      have key := statopia_math_node_2322479387_a1995076 μ p hp X Sigma hGauss
        (fun j => (coordStdDev μ X j)⁻¹) muShift
      simpa only [div_eq_mul_inv, mul_comm] using key
    · refine ⟨Matrix.diagonal (fun k => (coordStdDev μ X k)⁻¹) * Sigma *
        (Matrix.diagonal (fun k => (coordStdDev μ X k)⁻¹)).transpose, ?_⟩
      have h := Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector.linearImage
        μ X Sigma hGauss
        (Matrix.diagonal (fun k => (coordStdDev μ X k)⁻¹) : Matrix (Fin p) (Fin p) ℝ)
      have hpt : ∀ (ω : Ω) (j : Fin p), W ω j - muShift j
          = (Matrix.diagonal (fun k => (coordStdDev μ X k)⁻¹)).mulVec (X ω) j := by
        intro ω j
        rw [h2 j ω, Matrix.mulVec_diagonal]
        simp only [div_eq_mul_inv, mul_comm]
      show Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector μ
        (fun ω j => W ω j - muShift j)
        (Matrix.diagonal (fun k => (coordStdDev μ X k)⁻¹) * Sigma *
          (Matrix.diagonal (fun k => (coordStdDev μ X k)⁻¹)).transpose)
      simp only [hpt]
      exact h
    · intro j
      show ∫ ω, (W ω j - muShift j) ^ 2 ∂μ = 1
      have hσj : 0 < coordStdDev μ X j := by
        show 0 < Real.sqrt (∫ ω, (X ω j) ^ 2 ∂μ)
        exact Real.sqrt_pos_of_pos (hpos j)
      have hσ2 : coordStdDev μ X j ^ 2 = ∫ ω, (X ω j) ^ 2 ∂μ := by
        show Real.sqrt (∫ ω, (X ω j) ^ 2 ∂μ) ^ 2 = ∫ ω, (X ω j) ^ 2 ∂μ
        exact Real.sq_sqrt (hpos j).le
      have hpt : ∀ ω : Ω,
          (W ω j - muShift j) ^ 2 = (X ω j) ^ 2 * (coordStdDev μ X j ^ 2)⁻¹ := by
        intro ω
        simp only [h2 j ω, div_eq_mul_inv, mul_pow, inv_pow]
      simp only [hpt, integral_mul_const, ← hσ2]
      exact mul_inv_cancel₀ (pow_ne_zero 2 (ne_of_gt hσj))
  · refine ⟨?_, h5b, ?_, ?_⟩
    · intro ω
      haveI : Nonempty (Fin p) := ⟨⟨0, lt_of_lt_of_le Nat.zero_lt_one hp⟩⟩
      have hbdd : ∀ (f : Fin p → ℝ),
          BddAbove (Set.range f) := fun f =>
        ⟨(Finset.univ : Finset (Fin p)).sup'
            ⟨⟨0, lt_of_lt_of_le Nat.zero_lt_one hp⟩, Finset.mem_univ _⟩ f,
          by rintro _ ⟨k, rfl⟩; exact Finset.le_sup' f (Finset.mem_univ k)⟩
      have hg : (⨆ j : Fin p, W ω j)
          = ⨆ j : Fin p, ((X ω j - x) / coordStdDev μ X j + x * s) := by
        refine iSup_congr (fun j => ?_)
        show X ω j / coordStdDev μ X j + x * (s - 1 / coordStdDev μ X j)
            = (X ω j - x) / coordStdDev μ X j + x * s
        simp only [div_eq_mul_inv]
        ring
      have hsup : (⨆ j : Fin p, ((X ω j - x) / coordStdDev μ X j + x * s))
          = (⨆ j : Fin p, (X ω j - x) / coordStdDev μ X j) + x * s := by
        refine le_antisymm ?_ ?_
        · refine ciSup_le (fun j => ?_)
          have h := le_ciSup (hbdd (fun k : Fin p => (X ω k - x) / coordStdDev μ X k)) j
          linarith
        · have key : (⨆ j : Fin p, (X ω j - x) / coordStdDev μ X j)
              ≤ (⨆ j : Fin p, ((X ω j - x) / coordStdDev μ X j + x * s)) - x * s := by
            refine ciSup_le (fun j => ?_)
            have h := le_ciSup
              (hbdd (fun k : Fin p => (X ω k - x) / coordStdDev μ X k + x * s)) j
            linarith
          linarith
      rw [hg, hsup]
      ring
    simp only [add_sub_cancel_right, standardizedMaxMean]
    · let j0 : Fin p := ⟨0, lt_of_lt_of_le Nat.zero_lt_one hp⟩
      haveI : Nonempty (Fin p) := ⟨j0⟩
      have hmean : ∀ k : Fin p, ∫ ω, X ω k ∂μ = 0 :=
        statopia_math_node_154348488_06fea6fe μ p hp X Sigma hGauss hL2
      have hbdd : ∀ (f : Fin p → ℝ),
          BddAbove (Set.range f) := fun f =>
        ⟨(Finset.univ : Finset (Fin p)).sup' ⟨j0, Finset.mem_univ _⟩ f,
          by rintro _ ⟨k, rfl⟩; exact Finset.le_sup' f (Finset.mem_univ k)⟩
      have hzero : ∫ ω, X ω j0 / coordStdDev μ X j0 ∂μ = 0 := by
        simp only [div_eq_mul_inv, integral_mul_const, hmean j0, zero_mul]
      have hgInt : Integrable (fun ω => X ω j0 / coordStdDev μ X j0) μ :=
        ((hL2 j0).integrable (by norm_num)).div_const _
      have hpoint : ∀ ω : Ω, X ω j0 / coordStdDev μ X j0
          ≤ ⨆ j : Fin p, X ω j / coordStdDev μ X j :=
        fun ω => le_ciSup (hbdd (fun j : Fin p => X ω j / coordStdDev μ X j)) j0
      have hmono := integral_mono hgInt hInt hpoint
      rw [hzero] at hmono
      simpa only [standardizedMaxMean] using hmono

  /- @proof-region region.target-node.session.093430f74bd58a0b end -/

end Statlib.Imported

