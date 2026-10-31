import Statlib.StatFoundation.Statistics.Asymptotic.ScoreCLT
import Statlib.StatFoundation.Convergence.Resampling.GaussianMaxComparison
import Statlib.StatFoundation.Convergence.AnalysisTools.GaussianMaxAnticoncentration
import Statlib.StatFoundation.Statistics.Asymptotic.LAN
import Statlib.StatFoundation.Convergence.AnalysisTools.SmoothMax
import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.Vocabulary
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.Base
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.ProvedNodes.Node_1423981741_b7996ae4_5251302c
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.ProvedNodes.Node_2427644982_7294da19_198768f7
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.ProvedNodes.Node_2646130728_f6109688_c4e1d5cd
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.ProvedNodes.Node_3799861955_1c292e8a_9afb9068

namespace PaperProofTasks.job_paper_de3065fb922748188f3a0354eba90ed9



open _root_.PaperProofTasks.job_paper_de3065fb922748188f3a0354eba90ed9.Statlib.Imported
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

set_option autoImplicit false in
theorem statopia_math_node_966165858_9b26162f : ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℕ) (hp : 1 ≤ p)
    (X : Ω → Fin p → ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (hGauss : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector μ X Sigma)
    (hL2 : ∀ j : Fin p, MemLp (fun ω => X ω j) 2 μ)
    (hpos : ∀ j : Fin p, 0 < ∫ ω, (X ω j) ^ 2 ∂μ)
    (hInt : Integrable (fun ω => ⨆ j : Fin p, X ω j / coordStdDev μ X j) μ)
    (x : ℝ) (ε : ℝ) (hε : 0 < ε),
    μ {ω | |coordMax X ω - x| ≤ ε} ≤
      ENNReal.ofReal
        (4 * ε / sigmaUnder μ X *
          ((1 / sigmaUnder μ X - 1 / sigmaOver μ X) * |x| +
            standardizedMaxMean μ X + 1)) := by
  /- @proof-region region.target-node.session.5823c0de0e44f0d2 begin -/
  intro Ω hΩ μ hμ p hp X Sigma hGauss hL2 hpos hInt x ε hε
  let s : ℝ := if 0 ≤ x then 1 / sigmaUnder μ X else 1 / sigmaOver μ X
  let muShift : Fin p → ℝ := fun j => x * (s - 1 / coordStdDev μ X j)
  let W : Ω → Fin p → ℝ := fun ω j => X ω j / coordStdDev μ X j + muShift j
  obtain ⟨S, hS_ne, hS_corr, hS_W, hS_X⟩ :=
    statopia_math_node_1423981741_b7996ae4 μ p hp X Sigma hGauss hL2 hpos hInt x
  have hA :
      μ {ω | |(⨆ j : Fin p, (X ω j - x) / coordStdDev μ X j)| ≤ ε / sigmaUnder μ X} ≤
        ENNReal.ofReal
          (4 * ε / sigmaUnder μ X *
            ((1 / sigmaUnder μ X - 1 / sigmaOver μ X) * |x| +
              standardizedMaxMean μ X + 1)) :=
    statopia_math_node_2646130728_f6109688 μ p hp X Sigma hGauss hL2 hpos hInt x ε hε
      S hS_ne hS_corr hS_W hS_X
  have h4 :
      {ω | |coordMax X ω - x| ≤ ε} ⊆
        {ω | |(⨆ j : Fin p, (X ω j - x) / coordStdDev μ X j)| ≤ ε / sigmaUnder μ X} := by
    haveI : Nonempty (Fin p) := ⟨⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hp⟩⟩
    have hσpos : 0 < sigmaUnder μ X := by
      change 0 < ⨅ j : Fin p, coordStdDev μ X j
      rw [← Finset.inf'_univ_eq_ciInf (fun j : Fin p => coordStdDev μ X j)]
      rw [Finset.lt_inf'_iff Finset.univ_nonempty]
      intro i _
      exact Real.sqrt_pos.mpr (hpos i)
    have hσle : ∀ j : Fin p, sigmaUnder μ X ≤ coordStdDev μ X j :=
      fun j => ciInf_le (Finite.bddBelow_range (fun j : Fin p => coordStdDev μ X j)) j
    intro ω hω
    simp only [Set.mem_setOf_eq, coordMax] at hω ⊢
    rw [abs_le] at hω ⊢
    obtain ⟨hlo, hhi⟩ := hω
    refine ⟨?_, ?_⟩
    · obtain ⟨jstar, hjstar⟩ := exists_eq_ciSup_of_finite (f := fun j : Fin p => X ω j)
      have hσjpos : 0 < coordStdDev μ X jstar := lt_of_lt_of_le hσpos (hσle jstar)
      have hjlo : -ε ≤ X ω jstar - x := by linarith [hlo, hjstar]
      have hstep1 : (-ε) / coordStdDev μ X jstar ≤ (X ω jstar - x) / coordStdDev μ X jstar := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right hjlo (le_of_lt (inv_pos.mpr hσjpos))
      have h1 : (coordStdDev μ X jstar)⁻¹ ≤ (sigmaUnder μ X)⁻¹ := by
        simpa only [one_div] using one_div_le_one_div_of_le hσpos (hσle jstar)
      have hεc : ε / coordStdDev μ X jstar ≤ ε / sigmaUnder μ X := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left h1 hε.le
      have hstep2 : -(ε / sigmaUnder μ X) ≤ (-ε) / coordStdDev μ X jstar := by
        rw [neg_div]
        exact neg_le_neg_iff.mpr hεc
      have hle_sup :
          (X ω jstar - x) / coordStdDev μ X jstar ≤
            ⨆ j : Fin p, (X ω j - x) / coordStdDev μ X j :=
        le_ciSup (Finite.bddAbove_range (fun j : Fin p => (X ω j - x) / coordStdDev μ X j)) jstar
      linarith [hstep1, hstep2, hle_sup]
    · apply ciSup_le
      intro j
      have hσjpos : 0 < coordStdDev μ X j := lt_of_lt_of_le hσpos (hσle j)
      have hjle : X ω j ≤ ⨆ j : Fin p, X ω j :=
        le_ciSup (Finite.bddAbove_range (fun j : Fin p => X ω j)) j
      have hjhi : X ω j - x ≤ ε := by linarith [hhi, hjle]
      have hstep1 : (X ω j - x) / coordStdDev μ X j ≤ ε / coordStdDev μ X j := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right hjhi (le_of_lt (inv_pos.mpr hσjpos))
      have h1 : (coordStdDev μ X j)⁻¹ ≤ (sigmaUnder μ X)⁻¹ := by
        simpa only [one_div] using one_div_le_one_div_of_le hσpos (hσle j)
      have hstep2 : ε / coordStdDev μ X j ≤ ε / sigmaUnder μ X := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left h1 hε.le
      linarith [hstep1, hstep2]
  calc μ {ω | |coordMax X ω - x| ≤ ε}
      ≤ μ {ω | |(⨆ j : Fin p, (X ω j - x) / coordStdDev μ X j)| ≤ ε / sigmaUnder μ X} :=
        measure_mono h4
    _ ≤ ENNReal.ofReal
          (4 * ε / sigmaUnder μ X *
            ((1 / sigmaUnder μ X - 1 / sigmaOver μ X) * |x| +
              standardizedMaxMean μ X + 1)) := hA
  /- @proof-region region.target-node.session.5823c0de0e44f0d2 end -/

end Statlib.Imported

