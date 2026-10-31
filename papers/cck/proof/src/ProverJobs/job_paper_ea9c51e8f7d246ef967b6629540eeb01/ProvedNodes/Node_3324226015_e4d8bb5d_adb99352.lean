import Statlib.StatFoundation.Statistics.Asymptotic.ScoreCLT
import Statlib.StatFoundation.Convergence.Resampling.GaussianMaxComparison
import Statlib.StatFoundation.Convergence.AnalysisTools.GaussianMaxAnticoncentration
import Statlib.StatFoundation.Statistics.Asymptotic.LAN
import Statlib.StatFoundation.Convergence.AnalysisTools.SmoothMax
import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import ProverJobs.job_paper_ea9c51e8f7d246ef967b6629540eeb01.Vocabulary
import ProverJobs.job_paper_ea9c51e8f7d246ef967b6629540eeb01.Base

namespace PaperProofTasks.job_paper_ea9c51e8f7d246ef967b6629540eeb01

open _root_.PaperProofTasks.job_paper_ea9c51e8f7d246ef967b6629540eeb01.Statlib.Imported
open MeasureTheory ProbabilityTheory

namespace Statlib.Imported

open MeasureTheory ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_3324226015_e4d8bb5d : ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m n : ℕ) (W : Ω → Fin (m + n) → ℝ)
    (Sigma : Matrix (Fin (m + n)) (Fin (m + n)) ℝ)
    (hW : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector P W Sigma),
    Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector P
      (fun ω (i : Fin m) => W ω (Fin.castAdd n i))
      ((2 : ℝ)⁻¹ • (Matrix.of (fun i j : Fin m => Sigma (Fin.castAdd n i) (Fin.castAdd n j)) +
        (Matrix.of (fun i j : Fin m => Sigma (Fin.castAdd n i) (Fin.castAdd n j))).transpose)) := by
  /- @proof-region region.target-node.session.952eaa7be88ded79 begin -/
  intro Ω instΩ P instP m n W Sigma hW
  set M : Matrix (Fin m) (Fin m) ℝ :=
    Matrix.of (fun i j : Fin m => Sigma (Fin.castAdd n i) (Fin.castAdd n j)) with hM
  set S : Matrix (Fin m) (Fin m) ℝ := (2 : ℝ)⁻¹ • (M + M.transpose) with hS
  have hsum : ∀ (u : Fin m → ℝ) (ω : Ω),
      (∑ a : Fin (m + n), Fin.append u (fun _ => (0 : ℝ)) a * W ω a)
        = ∑ i : Fin m, u i * W ω (Fin.castAdd n i) := by
    intro u ω
    rw [Fin.sum_univ_add]
    simp [Fin.append_left', Fin.append_right]
  refine ⟨?_, ?_, ?_⟩
  · exact measurable_pi_iff.mpr
      (fun i => (measurable_pi_apply (Fin.castAdd n i)).comp hW.measurable)
  · intro u
    have h := hW.integrable_exp (Fin.append u (fun _ => (0 : ℝ)))
    simpa only [hsum] using h
  · intro u
    have h := hW.mgf_eq (Fin.append u (fun _ => (0 : ℝ)))
    have hL : (∫ ω, Real.exp (∑ i : Fin m, u i * W ω (Fin.castAdd n i)) ∂P)
        = ∫ ω, Real.exp (∑ a : Fin (m + n),
            Fin.append u (fun _ => (0 : ℝ)) a * W ω a) ∂P := by
      simp only [hsum]
    rw [hL, h]
    congr 1
    have h1 : ∀ i j : Fin m, S i j = (2 : ℝ)⁻¹ * (M i j + M j i) := by
      intro i j
      simp only [hS, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul]
    have e1 : (∑ a : Fin (m + n), ∑ b : Fin (m + n),
          Fin.append u (fun _ => (0 : ℝ)) a * Sigma a b * Fin.append u (fun _ => (0 : ℝ)) b)
        = ∑ i : Fin m, ∑ j : Fin m, u i * M i j * u j := by
      have happ : ∀ i : Fin m, Fin.append u (fun _ => (0 : ℝ)) (Fin.castAdd n i) = u i :=
        fun i => Fin.append_left' u (fun _ => (0 : ℝ)) i
      simp only [hM, Matrix.of_apply, Fin.sum_univ_add, Fin.append_right, happ,
        zero_mul, mul_zero, Finset.sum_const_zero, add_zero]
    have hA : ∀ i : Fin m, (∑ j : Fin m, u i * S i j * u j)
        = (2 : ℝ)⁻¹ * (∑ j : Fin m, u i * M i j * u j)
          + (2 : ℝ)⁻¹ * (∑ j : Fin m, u i * M j i * u j) := by
      intro i
      rw [show (∑ j : Fin m, u i * S i j * u j)
            = ∑ j : Fin m,
                ((2 : ℝ)⁻¹ * (u i * M i j * u j) + (2 : ℝ)⁻¹ * (u i * M j i * u j)) from
          Finset.sum_congr rfl (fun j _ => by rw [h1 i j]; ring)]
      rw [Finset.sum_add_distrib,
        show (∑ j : Fin m, (2 : ℝ)⁻¹ * (u i * M i j * u j))
            = (2 : ℝ)⁻¹ * (∑ j : Fin m, u i * M i j * u j) from by rw [Finset.mul_sum],
        show (∑ j : Fin m, (2 : ℝ)⁻¹ * (u i * M j i * u j))
            = (2 : ℝ)⁻¹ * (∑ j : Fin m, u i * M j i * u j) from by rw [Finset.mul_sum]]
    have hB : (∑ i : Fin m, ((2 : ℝ)⁻¹ * (∑ j : Fin m, u i * M i j * u j)
          + (2 : ℝ)⁻¹ * (∑ j : Fin m, u i * M j i * u j)))
        = (2 : ℝ)⁻¹ * (∑ i : Fin m, ∑ j : Fin m, u i * M i j * u j)
          + (2 : ℝ)⁻¹ * (∑ i : Fin m, ∑ j : Fin m, u i * M j i * u j) := by
      rw [Finset.sum_add_distrib,
        show (∑ i : Fin m, (2 : ℝ)⁻¹ * (∑ j : Fin m, u i * M i j * u j))
            = (2 : ℝ)⁻¹ * (∑ i : Fin m, ∑ j : Fin m, u i * M i j * u j) from by
          rw [Finset.mul_sum],
        show (∑ i : Fin m, (2 : ℝ)⁻¹ * (∑ j : Fin m, u i * M j i * u j))
            = (2 : ℝ)⁻¹ * (∑ i : Fin m, ∑ j : Fin m, u i * M j i * u j) from by
          rw [Finset.mul_sum]]
    have h4 : (∑ i : Fin m, ∑ j : Fin m, u i * M j i * u j)
        = ∑ i : Fin m, ∑ j : Fin m, u i * M i j * u j := by
      conv_lhs => rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
    have hQ : (∑ i : Fin m, ∑ j : Fin m, u i * S i j * u j)
        = ∑ i : Fin m, ∑ j : Fin m, u i * M i j * u j := by
      calc (∑ i : Fin m, ∑ j : Fin m, u i * S i j * u j)
          = ∑ i : Fin m, ((2 : ℝ)⁻¹ * (∑ j : Fin m, u i * M i j * u j)
              + (2 : ℝ)⁻¹ * (∑ j : Fin m, u i * M j i * u j)) :=
              Finset.sum_congr rfl (fun i _ => hA i)
        _ = (2 : ℝ)⁻¹ * (∑ i : Fin m, ∑ j : Fin m, u i * M i j * u j)
              + (2 : ℝ)⁻¹ * (∑ i : Fin m, ∑ j : Fin m, u i * M j i * u j) := hB
        _ = (2 : ℝ)⁻¹ * (∑ i : Fin m, ∑ j : Fin m, u i * M i j * u j)
              + (2 : ℝ)⁻¹ * (∑ i : Fin m, ∑ j : Fin m, u i * M i j * u j) := by rw [h4]
        _ = ∑ i : Fin m, ∑ j : Fin m, u i * M i j * u j := by
              rw [← add_mul, show (2 : ℝ)⁻¹ + 2⁻¹ = 1 by norm_num, one_mul]
    rw [e1, hQ]
  /- @proof-region region.target-node.session.952eaa7be88ded79 end -/

end Statlib.Imported

