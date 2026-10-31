import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q05.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q05.ProvedNodes
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q05.Base

open MeasureTheory ProbabilityTheory Filter
namespace Msc62GroundTruth

theorem binomial_clt_vanishing_probability
    (Ω : Type*) [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → ℕ)
    (hY_meas : ∀ n, 1 ≤ n → AEMeasurable (Y n) μ)
    (Z : Ω → ℝ)
    (hZ_meas : Measurable Z)
    (hZ_law : Measure.map Z μ = gaussianReal 0 1) :
    let p : ℕ → ℝ :=
      fun n => 1 / Real.sqrt (n : ℝ)
    let W : ℕ → Ω → ℝ :=
      fun n ω =>
        if 1 ≤ n then
          (n : ℝ) ^ (3 / 4 : ℝ) *
            (((Y n ω : ℝ) / (n : ℝ)) - p n)
        else
          0
    ∀ hY_dist : ∀ (n : ℕ) (hn : 1 ≤ n),
      Measure.map (Y n) μ =
        binomialMeasure n
          (Real.toNNReal (p n))
          (toNNReal_one_div_sqrt_n_le_one n hn),
      TendstoInDistribution W atTop Z μ
:= by
  /- @proof-region region.root.8ad7d29e3ea3 begin -/
  dsimp only
  intro hY_dist
  have hW : ∀ n : ℕ,
      AEMeasurable
        (fun ω : Ω =>
          if 1 ≤ n then
            (n : ℝ) ^ (3 / 4 : ℝ) * (((Y n ω : ℝ) / (n : ℝ)) - 1 / Real.sqrt (n : ℝ))
          else 0) μ := by
    intro n
    by_cases hn : 1 ≤ n
    · have hg : Measurable
          (fun k : ℕ => (n : ℝ) ^ (3 / 4 : ℝ) * (((k : ℝ) / (n : ℝ)) - 1 / Real.sqrt (n : ℝ))) :=
        measurable_of_countable _
      have h1 : AEMeasurable
          (fun ω : Ω =>
            (n : ℝ) ^ (3 / 4 : ℝ) * (((Y n ω : ℝ) / (n : ℝ)) - 1 / Real.sqrt (n : ℝ))) μ :=
        hg.comp_aemeasurable' (hY_meas n hn)
      have h2 : (fun ω : Ω =>
            if 1 ≤ n then
              (n : ℝ) ^ (3 / 4 : ℝ) * (((Y n ω : ℝ) / (n : ℝ)) - 1 / Real.sqrt (n : ℝ))
            else 0)
          = fun ω : Ω =>
              (n : ℝ) ^ (3 / 4 : ℝ) * (((Y n ω : ℝ) / (n : ℝ)) - 1 / Real.sqrt (n : ℝ)) := by
        funext ω
        rw [if_pos hn]
      rw [h2]
      exact h1
    · have h0 : (fun ω : Ω =>
            if 1 ≤ n then
              (n : ℝ) ^ (3 / 4 : ℝ) * (((Y n ω : ℝ) / (n : ℝ)) - 1 / Real.sqrt (n : ℝ))
            else 0) = fun _ : Ω => (0 : ℝ) := by
        funext ω
        rw [if_neg hn]
      rw [h0]
      exact aemeasurable_const
  have hchar : ∀ t : ℝ,
      Tendsto
        (fun n : ℕ =>
          charFun
            (Measure.map
              (fun ω : Ω =>
                if 1 ≤ n then
                  (n : ℝ) ^ (3 / 4 : ℝ) * (((Y n ω : ℝ) / (n : ℝ)) - 1 / Real.sqrt (n : ℝ))
                else 0)
              μ) t)
        atTop (nhds (Complex.exp ((-(t ^ 2) / 2 : ℝ) : ℂ))) := by
    intro t
    have hlim := statopia_math_node_348443290_53a92061 t
    have heq : (fun n : ℕ =>
          Complex.exp (Complex.I * ((-(t * (n : ℝ) ^ ((1 : ℝ) / 4)) : ℝ) : ℂ)) *
            (((((1 : ℝ) - 1 / Real.sqrt (n : ℝ)) : ℝ) : ℂ) +
              (((1 / Real.sqrt (n : ℝ) : ℝ) : ℂ) *
                Complex.exp (Complex.I * ((t * (n : ℝ) ^ ((-(1 : ℝ)) / 4) : ℝ) : ℂ)))) ^ n)
        =ᶠ[atTop]
        (fun n : ℕ =>
          charFun
            (Measure.map
              (fun ω : Ω =>
                if 1 ≤ n then
                  (n : ℝ) ^ (3 / 4 : ℝ) * (((Y n ω : ℝ) / (n : ℝ)) - 1 / Real.sqrt (n : ℝ))
                else 0)
              μ) t) := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have h := (statopia_math_node_2767755334_7b76b207 Ω μ Y hY_meas hY_dist n hn t).symm
      have hexp : (n : ℝ) ^ (-(1 / 4) : ℝ) = (n : ℝ) ^ ((-(1 : ℝ)) / 4) := by
        rw [show (-(1 / 4) : ℝ) = (-(1 : ℝ)) / 4 by norm_num]
      simpa only [hexp] using h
    exact (tendsto_congr' heq).mp hlim
  have hcont : ContinuousAt (fun t : ℝ => Complex.exp ((-(t ^ 2) / 2 : ℝ) : ℂ)) 0 := by
    have hreal : Continuous fun t : ℝ => ((-(t ^ 2) / 2 : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (by fun_prop)
    exact (Complex.continuous_exp.comp hreal).continuousAt
  obtain ⟨μ₀, hμ₀char, hμ₀tend⟩ :=
    Statlib.StatFoundation.Convergence.levy_continuity
      (μs := fun n : ℕ =>
        ⟨Measure.map
          (fun ω : Ω =>
            if 1 ≤ n then
              (n : ℝ) ^ (3 / 4 : ℝ) * (((Y n ω : ℝ) / (n : ℝ)) - 1 / Real.sqrt (n : ℝ))
            else 0) μ,
          Measure.isProbabilityMeasure_map (hW n)⟩)
      (f := fun t : ℝ => Complex.exp ((-(t ^ 2) / 2 : ℝ) : ℂ))
      hchar (by simp) hcont
  refine Statlib.StatFoundation.Convergence.tendstoInDistribution_of_probabilityMeasure_tendsto_and_gaussianReal_charFun
    hW hZ_meas.aemeasurable hZ_law ⟨μ₀, ?_, ?_⟩
  · intro t
    exact (hμ₀char t).trans (statopia_math_node_1870440469_f2276e59 t).symm
  · exact hμ₀tend
  /- @proof-region region.root.8ad7d29e3ea3 end -/

end Msc62GroundTruth
