import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q03.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q03.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q03.ProvedNodes.Node_393377813_944d1b82_888fa0c5
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q03.ProvedNodes.Node_467221787_65608b8a_2c042b1a
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q03.ProvedNodes.Node_859487190_88621b65_8a0d7230

open MeasureTheory Matrix ProbabilityTheory

open MeasureTheory Matrix ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_3678446978_c1498b57 : ∀ (m : ℕ) (hm : 1 ≤ m),
    (Measure.pi (fun _ : Fin m => gaussianReal 0 1)).map
        (fun y : Fin m → ℝ => ∑ k : Fin m, (y k) ^ 2)
      = volume.withDensity
          (fun s : ℝ => ENNReal.ofReal (gammaConvDensity ((m : ℝ) / 2) s)) := by
  /- @proof-region region.target-node.session.2017058a19b45cf6 begin -/
  intro m hm
  have hbase : (Measure.pi (fun _ : Fin 1 => gaussianReal 0 1)).map
        (fun y : Fin 1 → ℝ => ∑ k : Fin 1, (y k) ^ 2)
      = volume.withDensity
          (fun s : ℝ => ENNReal.ofReal (gammaConvDensity (((1 : ℕ) : ℝ) / 2) s)) := by
    exact statopia_math_node_467221787_65608b8a
  have hstep : ∀ (n : ℕ), 1 ≤ n →
      ((Measure.pi (fun _ : Fin n => gaussianReal 0 1)).map
          (fun y : Fin n → ℝ => ∑ k : Fin n, (y k) ^ 2)
        = volume.withDensity
            (fun s : ℝ => ENNReal.ofReal (gammaConvDensity ((n : ℝ) / 2) s))) →
      ((Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)).map
          (fun y : Fin (n + 1) → ℝ => ∑ k : Fin (n + 1), (y k) ^ 2)
        = volume.withDensity
            (fun s : ℝ => ENNReal.ofReal (gammaConvDensity (((n + 1 : ℕ) : ℝ) / 2) s))) := by
    exact statopia_math_node_393377813_944d1b82
  have key : ∀ n : ℕ, 1 ≤ n →
      ((Measure.pi (fun _ : Fin n => gaussianReal 0 1)).map
          (fun y : Fin n → ℝ => ∑ k : Fin n, (y k) ^ 2)
        = volume.withDensity
            (fun s : ℝ => ENNReal.ofReal (gammaConvDensity ((n : ℝ) / 2) s))) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => simpa using hbase
    | succ n hn ih => exact hstep n hn ih
  exact key m hm
  /- @proof-region region.target-node.session.2017058a19b45cf6 end -/
