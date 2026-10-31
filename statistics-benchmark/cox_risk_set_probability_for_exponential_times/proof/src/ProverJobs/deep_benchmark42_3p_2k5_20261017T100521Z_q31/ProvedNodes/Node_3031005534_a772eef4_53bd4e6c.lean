import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q31.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q31.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q31.ProvedNodes.Node_2533135513_78bc87cd_d2405e6f
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q31.ProvedNodes.Node_294271807_892f3447_b07075a5


open MeasureTheory ProbabilityTheory

open MeasureTheory ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_3031005534_a772eef4 : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 1 ≤ n)
    (lambda0 beta : ℝ) (hlambda : 0 < lambda0)
    (z : Fin n → ℝ)
    (T : Fin n → Ω → ℝ)
    (hTmeas : ∀ i, Measurable (T i))
    (hTnonneg : ∀ i ω, 0 ≤ T i ω)
    (hindep : iIndepFun T P)
    (hsurvival : ∀ i t, 0 ≤ t →
      P {ω | t < T i ω} =
        ENNReal.ofReal (Real.exp (-lambda0 * Real.exp (beta * z i) * t))),
    ∀ i : Fin n,
      P {ω | ∀ j : Fin n, j ≠ i → T i ω < T j ω} =
        ∫⁻ ω, ENNReal.ofReal
          (Real.exp (-(∑ j ∈ Finset.univ.erase i, lambda0 * Real.exp (beta * z j))
            * T i ω)) ∂P := by
  /- @proof-region region.target-node.session.0d3d78f2a869fad6 begin -/
  intro Ω _ P _ n hn lambda0 beta hlambda z T hTmeas hTnonneg hindep hsurvival i
  obtain ⟨-, hprob, -⟩ :=
    statopia_math_node_294271807_892f3447 P n hn T hTmeas hindep i
  rw [hprob]
  refine lintegral_congr fun x => ?_
  have hset : {y : Ω | ∀ j : Fin n, j ≠ i → T i x < T j y}
      = {y : Ω | ∀ j ∈ Finset.univ.erase i, T i x < T j y} := by
    ext y
    simp [Finset.mem_erase]
  rw [hset]
  exact statopia_math_node_2533135513_78bc87cd P n hn lambda0 beta hlambda z T
    hTmeas hindep hsurvival (T i x) (hTnonneg i x) (Finset.univ.erase i)
  /- @proof-region region.target-node.session.0d3d78f2a869fad6 end -/
