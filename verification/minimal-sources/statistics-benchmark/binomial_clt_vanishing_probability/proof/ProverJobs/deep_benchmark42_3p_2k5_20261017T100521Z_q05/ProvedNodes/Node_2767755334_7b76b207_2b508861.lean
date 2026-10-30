import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q05.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q05.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q05.ProvedNodes.Node_1256681931_9609104f_ef3fcd33
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q05.ProvedNodes.Node_2653343113_924914c7_8fb8f917
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q05.ProvedNodes.Node_932896096_2342c8d2_d8faad21



open MeasureTheory ProbabilityTheory Filter
open Msc62GroundTruth

open MeasureTheory ProbabilityTheory Filter
namespace Msc62GroundTruth

set_option autoImplicit false in
theorem statopia_math_node_2767755334_7b76b207 : ∀ (Ω : Type*) [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → ℕ)
    (hY_meas : ∀ n, 1 ≤ n → AEMeasurable (Y n) μ)
    (hY_dist : ∀ (n : ℕ) (hn : 1 ≤ n),
      Measure.map (Y n) μ =
        binomialMeasure n
          (Real.toNNReal (1 / Real.sqrt (n : ℝ)))
          (toNNReal_one_div_sqrt_n_le_one n hn)),
    ∀ (n : ℕ) (hn : 1 ≤ n) (t : ℝ),
      charFun
        (Measure.map
          (fun ω : Ω =>
            if 1 ≤ n then
              (n : ℝ) ^ (3 / 4 : ℝ) *
                (((Y n ω : ℝ) / (n : ℝ)) - 1 / Real.sqrt (n : ℝ))
            else 0)
          μ) t =
        Complex.exp (Complex.I * ((-(t * (n : ℝ) ^ (1 / 4 : ℝ)) : ℝ) : ℂ)) *
          (((((1 : ℝ) - 1 / Real.sqrt (n : ℝ) : ℝ) : ℂ)
              + (((1 / Real.sqrt (n : ℝ) : ℝ) : ℂ)
                  * Complex.exp
                      (Complex.I *
                        ((t * (n : ℝ) ^ (-(1 / 4) : ℝ) : ℝ) : ℂ)))) ^ n) := by
  /- @proof-region region.target-node.session.d400092a19c8ad76 begin -/
  intro Ω instΩ μ instμ Y hY_meas hY_dist n hn t
  have hlaw := statopia_math_node_932896096_2342c8d2 Ω μ Y hY_meas hY_dist n hn
  haveI hbin : IsFiniteMeasure
      (binomialMeasure n (Real.toNNReal (1 / Real.sqrt (n : ℝ)))
        (toNNReal_one_div_sqrt_n_le_one n hn)) := by
    unfold binomialMeasure
    infer_instance
  have hshift : (fun y : ℝ => (n : ℝ) ^ (-(1 / 4) : ℝ) * y - (n : ℝ) ^ (1 / 4 : ℝ)) =
      fun y : ℝ => (n : ℝ) ^ (-(1 / 4) : ℝ) * y + -((n : ℝ) ^ (1 / 4 : ℝ)) := by
    funext y
    ring
  rw [hlaw, hshift, statopia_math_node_1256681931_9609104f,
    statopia_math_node_2653343113_924914c7 n (Real.toNNReal (1 / Real.sqrt (n : ℝ)))
      (toNNReal_one_div_sqrt_n_le_one n hn) ((n : ℝ) ^ (-(1 / 4) : ℝ) * t)]
  have hqcoe : ((Real.toNNReal (1 / Real.sqrt (n : ℝ)) : NNReal) : ℝ) = 1 / Real.sqrt (n : ℝ) := by
    simp
  have hexp : (-((n : ℝ) ^ (1 / 4 : ℝ)) : ℝ) * t = -(t * (n : ℝ) ^ (1 / 4 : ℝ)) := by
    ring
  have harg : ((n : ℝ) ^ (-(1 / 4) : ℝ) * t : ℝ) = t * (n : ℝ) ^ (-(1 / 4) : ℝ) := by
    ring
  rw [hqcoe, hexp, harg]
  /- @proof-region region.target-node.session.d400092a19c8ad76 end -/

end Msc62GroundTruth
