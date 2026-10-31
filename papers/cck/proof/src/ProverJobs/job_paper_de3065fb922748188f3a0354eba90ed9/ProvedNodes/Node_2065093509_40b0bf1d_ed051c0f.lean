import Statlib.StatFoundation.Statistics.Asymptotic.ScoreCLT
import Statlib.StatFoundation.Convergence.Resampling.GaussianMaxComparison
import Statlib.StatFoundation.Convergence.AnalysisTools.GaussianMaxAnticoncentration
import Statlib.StatFoundation.Statistics.Asymptotic.LAN
import Statlib.StatFoundation.Convergence.AnalysisTools.SmoothMax
import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.Vocabulary
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.Base
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.ProvedNodes.Node_1572792732_43168f8b_9f1c2f60
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.ProvedNodes.Node_2728575719_e5a804ed_703aa02c
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.ProvedNodes.Node_643971460_c175e112_fb332a25

namespace PaperProofTasks.job_paper_de3065fb922748188f3a0354eba90ed9


open _root_.PaperProofTasks.job_paper_de3065fb922748188f3a0354eba90ed9.Statlib.Imported
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

set_option autoImplicit false in
theorem statopia_math_node_2065093509_40b0bf1d : ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℕ) (hp : 1 ≤ p)
    (X : Ω → Fin p → ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (hGauss : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector μ X Sigma)
    (hL2 : ∀ j : Fin p, MemLp (fun ω => X ω j) 2 μ)
    (hpos : ∀ j : Fin p, 0 < ∫ ω, (X ω j) ^ 2 ∂μ)
    (hInt : Integrable (fun ω => ⨆ j : Fin p, X ω j / coordStdDev μ X j) μ)
      (eps : ℝ) (heps_pos : 0 < eps) (heps_le : eps ≤ sigmaUnder μ X),
      ∀ x : ℝ,
        eps + sigmaOver μ X *
            (standardizedMaxMean μ X + Real.sqrt (2 * Real.log (sigmaUnder μ X / eps))) ≤ |x| →
          μ {ω | |coordMax X ω - x| ≤ eps} ≤ ENNReal.ofReal (eps / sigmaUnder μ X) := by
  /- @proof-region region.target-node.session.8aa07876729f5f82 begin -/
  intro Ω hΩ μ hμ p hp X Sigma hGauss hL2 hpos hInt eps heps_pos heps_le x hx
  have hp0 : 0 < p := lt_of_lt_of_le Nat.zero_lt_one hp
  have hσpos : ∀ j : Fin p, 0 < coordStdDev μ X j := fun j => Real.sqrt_pos.2 (hpos j)
  have hcoord : ∀ j : Fin p, coordStdDev μ X j = Real.sqrt (∫ ω, (X ω j) ^ 2 ∂μ) := fun j => rfl
  have hbddAbove : BddAbove (Set.range (fun j : Fin p => coordStdDev μ X j)) := by
    refine ⟨Real.sqrt (∑ j : Fin p, ∫ ω, (X ω j) ^ 2 ∂μ), ?_⟩
    rintro _ ⟨j, rfl⟩
    change coordStdDev μ X j ≤ Real.sqrt (∑ j : Fin p, ∫ ω, (X ω j) ^ 2 ∂μ)
    rw [hcoord j]
    apply Real.sqrt_le_sqrt
    exact Finset.single_le_sum (f := fun j : Fin p => ∫ ω, (X ω j) ^ 2 ∂μ)
      (fun i _ => integral_nonneg (fun ω => sq_nonneg (X ω i))) (Finset.mem_univ j)
  have hbddBelow : BddBelow (Set.range (fun j : Fin p => coordStdDev μ X j)) :=
    ⟨0, by rintro _ ⟨j, rfl⟩; exact (hσpos j).le⟩
  have hσ_le_sO : ∀ j : Fin p, coordStdDev μ X j ≤ sigmaOver μ X := fun j => le_ciSup hbddAbove j
  have hσU_pos : 0 < sigmaUnder μ X := lt_of_lt_of_le heps_pos heps_le
  have hsO_pos : 0 < sigmaOver μ X := lt_of_lt_of_le (hσpos ⟨0, hp0⟩) (hσ_le_sO ⟨0, hp0⟩)
  have hlog : 0 ≤ Real.log (sigmaUnder μ X / eps) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ heps_pos]
    simpa using heps_le
  have hs_sq :
      (Real.sqrt (2 * Real.log (sigmaUnder μ X / eps))) ^ 2 = 2 * Real.log (sigmaUnder μ X / eps) :=
    Real.sq_sqrt (by linarith)
  have hexp :
      Real.exp (-((Real.sqrt (2 * Real.log (sigmaUnder μ X / eps))) ^ 2) / (2 * 1))
        = eps / sigmaUnder μ X := by
    rw [hs_sq]
    have h2 : -(2 * Real.log (sigmaUnder μ X / eps)) / (2 * 1)
        = -Real.log (sigmaUnder μ X / eps) := by ring
    rw [h2, Real.exp_neg, Real.exp_log (div_pos hσU_pos heps_pos), inv_div]
  have hvar : ∀ j : Fin p, ∫ ω, (X ω j / coordStdDev μ X j) ^ 2 ∂μ ≤ 1 := by
    intro j
    have hσ2 : coordStdDev μ X j ^ 2 = ∫ ω, (X ω j) ^ 2 ∂μ := by
      rw [hcoord j, Real.sq_sqrt (integral_nonneg fun ω => sq_nonneg (X ω j))]
    have hcongr : (fun ω => (X ω j / coordStdDev μ X j) ^ 2)
        = fun ω => (coordStdDev μ X j ^ 2)⁻¹ * (X ω j) ^ 2 := by
      funext ω
      rw [div_pow, div_eq_inv_mul]
    have heq : ∫ ω, (X ω j / coordStdDev μ X j) ^ 2 ∂μ = 1 := by
      rw [hcongr, integral_const_mul, ← hσ2,
        inv_mul_cancel₀ (ne_of_gt (pow_pos (hσpos j) 2))]
    exact le_of_eq heq
  have hsup_ge : ∀ (ω : Ω) (j : Fin p),
      X ω j / coordStdDev μ X j ≤ ⨆ k : Fin p, X ω k / coordStdDev μ X k := by
    intro ω j
    have hbdd : BddAbove (Set.range (fun k : Fin p => X ω k / coordStdDev μ X k)) := by
      refine ⟨∑ k : Fin p, |X ω k / coordStdDev μ X k|, ?_⟩
      rintro _ ⟨k, rfl⟩
      exact le_trans (le_abs_self _)
        (Finset.single_le_sum (f := fun i : Fin p => |X ω i / coordStdDev μ X i|)
          (fun i _ => abs_nonneg _) (Finset.mem_univ k))
    exact le_ciSup hbdd j
  have haP : 0 ≤ standardizedMaxMean μ X := by
    have hmean0 : ∫ ω, X ω ⟨0, hp0⟩ ∂μ = 0 :=
      (statopia_math_node_2728575719_e5a804ed μ p hp X Sigma hGauss hpos ⟨0, hp0⟩).1
    have hint_coord : Integrable (fun ω => X ω ⟨0, hp0⟩) μ :=
      MemLp.integrable (by norm_num) (hL2 ⟨0, hp0⟩)
    have hint_div : Integrable (fun ω => X ω ⟨0, hp0⟩ / coordStdDev μ X ⟨0, hp0⟩) μ :=
      hint_coord.div_const _
    have hdiv0 : ∫ ω, X ω ⟨0, hp0⟩ / coordStdDev μ X ⟨0, hp0⟩ ∂μ = 0 := by
      have hcongr : (fun ω => X ω ⟨0, hp0⟩ / coordStdDev μ X ⟨0, hp0⟩)
          = fun ω => (coordStdDev μ X ⟨0, hp0⟩)⁻¹ * X ω ⟨0, hp0⟩ := by
        funext ω
        rw [div_eq_inv_mul]
      rw [hcongr, integral_const_mul, hmean0, mul_zero]
    have hmono :
        ∫ ω, X ω ⟨0, hp0⟩ / coordStdDev μ X ⟨0, hp0⟩ ∂μ ≤ standardizedMaxMean μ X :=
      integral_mono hint_div hInt (fun ω => hsup_ge ω ⟨0, hp0⟩)
    rw [hdiv0] at hmono
    exact hmono
  have hcsup_ge : ∀ (ω : Ω) (j : Fin p), X ω j ≤ ⨆ k : Fin p, X ω k := by
    intro ω j
    have hbdd : BddAbove (Set.range (fun k : Fin p => X ω k)) := by
      refine ⟨∑ k : Fin p, |X ω k|, ?_⟩
      rintro _ ⟨k, rfl⟩
      exact le_trans (le_abs_self _)
        (Finset.single_le_sum (f := fun i : Fin p => |X ω i|)
          (fun i _ => abs_nonneg _) (Finset.mem_univ k))
    exact le_ciSup hbdd j
  have hexp' : Real.exp (-((Real.sqrt (2 * Real.log (sigmaUnder μ X / eps))) ^ 2) / 2)
      = eps / sigmaUnder μ X := by
    rw [hs_sq]
    have h2 : -(2 * Real.log (sigmaUnder μ X / eps)) / 2
        = -Real.log (sigmaUnder μ X / eps) := by ring
    rw [h2, Real.exp_neg, Real.exp_log (div_pos hσU_pos heps_pos), inv_div]
  have hA_nonneg : 0 ≤ sigmaOver μ X *
      (standardizedMaxMean μ X + Real.sqrt (2 * Real.log (sigmaUnder μ X / eps))) := by
    have hs0 : 0 ≤ Real.sqrt (2 * Real.log (sigmaUnder μ X / eps)) := Real.sqrt_nonneg _
    have hsum : 0 ≤ standardizedMaxMean μ X + Real.sqrt (2 * Real.log (sigmaUnder μ X / eps)) := by
      linarith
    exact mul_nonneg hsO_pos.le hsum
  by_cases hs0 : Real.sqrt (2 * Real.log (sigmaUnder μ X / eps)) = 0
  · have hratio : eps / sigmaUnder μ X = 1 := by
      rw [← hexp, hs0]
      simp
    rw [hratio, ENNReal.ofReal_one]
    exact le_trans (measure_mono (Set.subset_univ _)) (le_of_eq measure_univ)
  · have hs_pos : 0 < Real.sqrt (2 * Real.log (sigmaUnder μ X / eps)) :=
      lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hs0)
    rcases le_total 0 x with hx0 | hx0
    · have hxT : eps + sigmaOver μ X *
          (standardizedMaxMean μ X + Real.sqrt (2 * Real.log (sigmaUnder μ X / eps))) ≤ x := by
        rwa [abs_of_nonneg hx0] at hx
      let D : Matrix (Fin p) (Fin p) ℝ := Matrix.diagonal (fun k => (coordStdDev μ X k)⁻¹)
      let Y : Ω → Fin p → ℝ := fun ω => D.mulVec (X ω)
      have hYcoord : ∀ (ω : Ω) (k : Fin p), Y ω k = X ω k / coordStdDev μ X k := by
        intro ω k
        have h1 : Y ω k = ∑ j : Fin p,
            (Matrix.diagonal (fun i => (coordStdDev μ X i)⁻¹)) k j * X ω j := rfl
        have h2 : (∑ j : Fin p,
            (Matrix.diagonal (fun i => (coordStdDev μ X i)⁻¹)) k j * X ω j)
            = (Matrix.diagonal (fun i => (coordStdDev μ X i)⁻¹)) k k * X ω k := by
          refine Finset.sum_eq_single k ?_ ?_
          · intro j _ hj
            simp [Matrix.diagonal, Ne.symm hj]
          · intro hk
            exact absurd (Finset.mem_univ k) hk
        rw [h1, h2]
        simp [Matrix.diagonal, div_eq_inv_mul]
      have hYeq : ∀ ω : Ω, coordMax Y ω = ⨆ k : Fin p, X ω k / coordStdDev μ X k := by
        intro ω
        show (⨆ k : Fin p, Y ω k) = ⨆ k : Fin p, X ω k / coordStdDev μ X k
        exact iSup_congr (fun k => hYcoord ω k)
      have hvarY : ∀ k : Fin p, ∫ ω, (Y ω k) ^ 2 ∂μ ≤ 1 := by
        intro k
        have hc : (fun ω => (Y ω k) ^ 2) = fun ω => (X ω k / coordStdDev μ X k) ^ 2 := by
          funext ω
          rw [hYcoord ω k]
        rw [hc]
        exact hvar k
      have hIntY : Integrable (fun ω => coordMax Y ω) μ := by
        have hc : (fun ω => coordMax Y ω)
            = fun ω => (⨆ k : Fin p, X ω k / coordStdDev μ X k) := funext hYeq
        rw [hc]
        exact hInt
      have hdev := statopia_math_node_643971460_c175e112 μ p hp Y (D * Sigma * D.transpose)
        (hGauss.linearImage μ X Sigma D) 1 one_pos hvarY hIntY
        (Real.sqrt (2 * Real.log (sigmaUnder μ X / eps))) hs_pos
      have hdev' : μ {ω : Ω | standardizedMaxMean μ X +
            Real.sqrt (2 * Real.log (sigmaUnder μ X / eps)) ≤
              ⨆ k : Fin p, X ω k / coordStdDev μ X k} ≤
          ENNReal.ofReal (eps / sigmaUnder μ X) := by
        simpa only [hYeq, hexp] using hdev
      refine le_trans (measure_mono ?_) hdev'
      intro ω hω
      have h1 : x - eps ≤ coordMax X ω := by
        have h := (abs_le.mp (show |coordMax X ω - x| ≤ eps from hω)).1
        linarith
      have hMA : sigmaOver μ X *
          (standardizedMaxMean μ X + Real.sqrt (2 * Real.log (sigmaUnder μ X / eps)))
            ≤ coordMax X ω := by linarith
      have hMnn : 0 ≤ coordMax X ω := le_trans hA_nonneg hMA
      haveI : Nonempty (Fin p) := ⟨⟨0, hp0⟩⟩
      obtain ⟨jstar, hjstar⟩ := exists_eq_ciSup_of_finite (f := fun k : Fin p => X ω k)
      have hMeq : X ω jstar = coordMax X ω := hjstar
      have hsum : 0 ≤ standardizedMaxMean μ X +
          Real.sqrt (2 * Real.log (sigmaUnder μ X / eps)) := by
        have h := Real.sqrt_nonneg (2 * Real.log (sigmaUnder μ X / eps))
        linarith
      have hstep1 : standardizedMaxMean μ X +
          Real.sqrt (2 * Real.log (sigmaUnder μ X / eps))
            ≤ coordMax X ω / coordStdDev μ X jstar := by
        rw [le_div_iff₀ (hσpos jstar)]
        calc (standardizedMaxMean μ X + Real.sqrt (2 * Real.log (sigmaUnder μ X / eps)))
              * coordStdDev μ X jstar
            ≤ (standardizedMaxMean μ X + Real.sqrt (2 * Real.log (sigmaUnder μ X / eps)))
              * sigmaOver μ X := mul_le_mul_of_nonneg_left (hσ_le_sO jstar) hsum
          _ = sigmaOver μ X *
              (standardizedMaxMean μ X + Real.sqrt (2 * Real.log (sigmaUnder μ X / eps))) := by
                ring
          _ ≤ coordMax X ω := hMA
      have hstep2 : coordMax X ω / coordStdDev μ X jstar
          ≤ ⨆ k : Fin p, X ω k / coordStdDev μ X k := by
        have h := hsup_ge ω jstar
        rwa [hMeq] at h
      exact le_trans hstep1 hstep2
    · have hxA : sigmaOver μ X *
          (standardizedMaxMean μ X + Real.sqrt (2 * Real.log (sigmaUnder μ X / eps))) + eps
            ≤ -x := by
        have h := hx
        rw [abs_of_nonpos hx0] at h
        linarith
      have hsubL : {ω : Ω | |coordMax X ω - x| ≤ eps} ⊆
          {ω : Ω | X ω ⟨0, hp0⟩ ≤ -(sigmaOver μ X *
            (standardizedMaxMean μ X + Real.sqrt (2 * Real.log (sigmaUnder μ X / eps))))} := by
        intro ω hω
        have h1 : coordMax X ω - x ≤ eps := (abs_le.mp hω).2
        have h2 : coordMax X ω ≤ -(sigmaOver μ X *
            (standardizedMaxMean μ X + Real.sqrt (2 * Real.log (sigmaUnder μ X / eps)))) := by
          linarith
        exact le_trans (hcsup_ge ω ⟨0, hp0⟩) h2
      have hchild := (statopia_math_node_2728575719_e5a804ed μ p hp X Sigma hGauss hpos
        ⟨0, hp0⟩).2 (sigmaOver μ X *
          (standardizedMaxMean μ X + Real.sqrt (2 * Real.log (sigmaUnder μ X / eps)))) hA_nonneg
      refine le_trans (measure_mono hsubL) (le_trans hchild (ENNReal.ofReal_le_ofReal ?_))
      have hc_nonneg : 0 ≤ sigmaOver μ X *
          (standardizedMaxMean μ X + Real.sqrt (2 * Real.log (sigmaUnder μ X / eps)))
            / coordStdDev μ X ⟨0, hp0⟩ := div_nonneg hA_nonneg (hσpos ⟨0, hp0⟩).le
      have hsum : 0 ≤ standardizedMaxMean μ X +
          Real.sqrt (2 * Real.log (sigmaUnder μ X / eps)) := by
        have h := Real.sqrt_nonneg (2 * Real.log (sigmaUnder μ X / eps))
        linarith
      have hc_ge : Real.sqrt (2 * Real.log (sigmaUnder μ X / eps)) ≤
          sigmaOver μ X * (standardizedMaxMean μ X +
            Real.sqrt (2 * Real.log (sigmaUnder μ X / eps))) / coordStdDev μ X ⟨0, hp0⟩ := by
        have h1 : standardizedMaxMean μ X + Real.sqrt (2 * Real.log (sigmaUnder μ X / eps))
            ≤ sigmaOver μ X * (standardizedMaxMean μ X +
              Real.sqrt (2 * Real.log (sigmaUnder μ X / eps)))
                / coordStdDev μ X ⟨0, hp0⟩ := by
          rw [le_div_iff₀ (hσpos ⟨0, hp0⟩)]
          calc (standardizedMaxMean μ X + Real.sqrt (2 * Real.log (sigmaUnder μ X / eps)))
                * coordStdDev μ X ⟨0, hp0⟩
              ≤ (standardizedMaxMean μ X + Real.sqrt (2 * Real.log (sigmaUnder μ X / eps)))
                * sigmaOver μ X := mul_le_mul_of_nonneg_left (hσ_le_sO ⟨0, hp0⟩) hsum
            _ = sigmaOver μ X *
                (standardizedMaxMean μ X + Real.sqrt (2 * Real.log (sigmaUnder μ X / eps))) := by
                  ring
        linarith
      have hsq_le : (Real.sqrt (2 * Real.log (sigmaUnder μ X / eps))) ^ 2 ≤
          (sigmaOver μ X * (standardizedMaxMean μ X +
            Real.sqrt (2 * Real.log (sigmaUnder μ X / eps))) / coordStdDev μ X ⟨0, hp0⟩) ^ 2 := by
        nlinarith [hc_ge, hc_nonneg, Real.sqrt_nonneg (2 * Real.log (sigmaUnder μ X / eps))]
      rw [← hexp']
      exact Real.exp_le_exp.mpr (by linarith)
  /- @proof-region region.target-node.session.8aa07876729f5f82 end -/

end Statlib.Imported

