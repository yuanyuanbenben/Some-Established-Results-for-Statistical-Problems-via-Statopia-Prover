import Statlib.StatFoundation.Vocabulary.OrliczNorm
import ProverJobs.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.Vocabulary
import ProverJobs.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.Base

namespace PaperProofTasks.job_paper_cb04ce35a04d48a9bf96750470ca0eb0

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal
open _root_.PaperProofTasks.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.Statlib.Imported
universe u

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal
namespace Statlib.Imported

noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_193944682_6a261332 : ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Ω → ℝ) (hξ : AEMeasurable ξ μ),
    Statlib.StatFoundation.Vocabulary.orliczNorm 1 ξ μ = psi1Norm μ ξ := by
  /- @proof-region region.target-node.session.9e1cd2c5538f3269 begin -/
  intro Ω inst μ hprob ξ hξ
  unfold Statlib.StatFoundation.Vocabulary.orliczNorm psi1Norm
  have hK : ∀ s : ℝ, 0 < s →
      ((∫⁻ ω, ENNReal.ofReal (Statlib.StatFoundation.Vocabulary.psiOrlicz 1 (|ξ ω| / s)) ∂μ) ≤ 1 ↔
      (∫⁻ ω, ENNReal.ofReal (Real.exp (|ξ ω| / s)) ∂μ) ≤ 2) := by
    intro s hs
    have hpt : ∀ ω : Ω,
        ENNReal.ofReal (Real.exp (|ξ ω| / s)) =
          1 + ENNReal.ofReal (Statlib.StatFoundation.Vocabulary.psiOrlicz 1 (|ξ ω| / s)) := by
      intro ω
      have hy : 0 ≤ |ξ ω| / s := div_nonneg (abs_nonneg (ξ ω)) (le_of_lt hs)
      have hexp1 : 0 ≤ Real.exp (|ξ ω| / s) - 1 := by
        have h1 : (1 : ℝ) ≤ Real.exp (|ξ ω| / s) := by
          calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
            _ ≤ Real.exp (|ξ ω| / s) := Real.exp_le_exp.mpr hy
        linarith
      have hpsi : Statlib.StatFoundation.Vocabulary.psiOrlicz 1 (|ξ ω| / s)
          = Real.exp (|ξ ω| / s) - 1 := by
        simp only [Statlib.StatFoundation.Vocabulary.psiOrlicz, Real.rpow_one]
      have hL : ENNReal.ofReal (Real.exp (|ξ ω| / s))
          = ENNReal.ofReal (Real.exp (|ξ ω| / s) - 1) + 1 := by
        conv_lhs => rw [show Real.exp (|ξ ω| / s) = (Real.exp (|ξ ω| / s) - 1) + 1 by ring]
        rw [ENNReal.ofReal_add hexp1 (by norm_num : (0 : ℝ) ≤ 1), ENNReal.ofReal_one]
      rw [hL, hpsi]
      exact add_comm _ _
    have hE : (∫⁻ ω, ENNReal.ofReal (Real.exp (|ξ ω| / s)) ∂μ)
        = 1 + (∫⁻ ω, ENNReal.ofReal (Statlib.StatFoundation.Vocabulary.psiOrlicz 1 (|ξ ω| / s)) ∂μ) := by
      calc (∫⁻ ω, ENNReal.ofReal (Real.exp (|ξ ω| / s)) ∂μ)
          = (∫⁻ ω, (1 + ENNReal.ofReal (Statlib.StatFoundation.Vocabulary.psiOrlicz 1 (|ξ ω| / s))) ∂μ) :=
            lintegral_congr (fun ω => hpt ω)
        _ = (∫⁻ _ : Ω, (1 : ℝ≥0∞) ∂μ) + (∫⁻ ω, ENNReal.ofReal (Statlib.StatFoundation.Vocabulary.psiOrlicz 1 (|ξ ω| / s)) ∂μ) :=
            lintegral_add_left (measurable_const : Measurable (fun _ : Ω => (1 : ℝ≥0∞))) (fun ω => ENNReal.ofReal (Statlib.StatFoundation.Vocabulary.psiOrlicz 1 (|ξ ω| / s)))
        _ = 1 + (∫⁻ ω, ENNReal.ofReal (Statlib.StatFoundation.Vocabulary.psiOrlicz 1 (|ξ ω| / s)) ∂μ) := by
            rw [lintegral_const, measure_univ, mul_one]
    rw [hE, show (2 : ℝ≥0∞) = 1 + 1 by norm_num]
    exact (ENNReal.add_le_add_iff_left (by norm_num : (1 : ℝ≥0∞) ≠ ⊤)).symm
  apply le_antisymm
  · apply le_iInf
    intro s
    apply sInf_le
    refine ⟨?_, ?_⟩
    · exact ENNReal.ofReal_pos.mpr s.2.1
    · have htr : (ENNReal.ofReal s.1).toReal = s.1 := ENNReal.toReal_ofReal (le_of_lt s.2.1)
      simp only [htr]
      exact (hK s.1 s.2.1).mpr s.2.2
  · apply le_sInf
    intro t ht
    by_cases htop : t = ⊤
    · rw [htop]; exact le_top
    · have htpos : 0 < t.toReal := ENNReal.toReal_pos ht.1.ne' htop
      have hteq : ENNReal.ofReal t.toReal = t := ENNReal.ofReal_toReal htop
      have hGS : (∫⁻ ω, ENNReal.ofReal (Real.exp (|ξ ω| / t.toReal)) ∂μ) ≤ 2 :=
        (hK t.toReal htpos).mp ht.2
      calc ⨅ s : {s : ℝ // 0 < s ∧ (∫⁻ ω, ENNReal.ofReal (Real.exp (|ξ ω| / s)) ∂μ) ≤ 2},
            ENNReal.ofReal s.1
          ≤ ENNReal.ofReal t.toReal :=
            iInf_le (fun s : {s : ℝ // 0 < s ∧ (∫⁻ ω, ENNReal.ofReal (Real.exp (|ξ ω| / s)) ∂μ) ≤ 2} =>
              ENNReal.ofReal s.1) ⟨t.toReal, htpos, hGS⟩
        _ = t := hteq
  /- @proof-region region.target-node.session.9e1cd2c5538f3269 end -/

end

end Statlib.Imported

