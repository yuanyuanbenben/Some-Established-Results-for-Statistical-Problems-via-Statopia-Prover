import ProverJobs.manual_dp_root_finish_20261031.ConsGeneral
import ProverJobs.manual_dp_cons_asymptotic_20261031.Bridge
import ProverJobs.manual_dp_root_finish_20261031.MarkovTail
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
noncomputable section
namespace OfflineDPConsGeneral
attribute [local instance] Classical.propDecidable
open Statlib.Imported ManualDPCons OfflineDPConsMeas

/-- Complete consGeneral overclustering expectation under the source analytic
assumptions. The rate threshold depends on the fixed data configuration, not on
sample size or a selected prior. No expectation or convergence is a free premise. -/
theorem consGeneral_complete (C : LocationConfig) (prior : ConcentrationPrior)
    (p : Fin C.t → ℝ) (hp : ∀ j, 0 ≤ p j) (hpsum : ∑ j, p j = 1)
    (D rho nu : ℝ) (hD : 0 < D) (hnu : 0 < nu)
    (hrho : 4 * dpK5 C.U C.m C.c C.theta ≤ rho)
    (hA3_int : ∀ q : ℕ, 1 ≤ q → Integrable (fun a : ℝ => a^q * prior.dens a) volume)
    (hA3 : ∀ q : ℕ, 1 ≤ q → (∫ a : ℝ, a^q * prior.dens a ∂volume) <
      D * rho^(-(q:ℤ)) * Real.Gamma (nu+(q:ℝ)+1)) :
    Tendsto (fun n : ℕ => ∫⁻ ω, ENNReal.ofReal (if dpOmega C.c C.theta C.N n ω then
        ∑ s ∈ Finset.Icc 1 (n-C.t), dpRatio C.g C.q0 prior.dens C.t n s ω else 0)
      ∂dpPinf C.g C.theta p) atTop (𝓝 0) := by
  have hlim := ManualDPConsAsymptotic.prior_ratio_bound_sum_tendsto_zero C prior D rho nu hD hnu hrho hA3_int hA3
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall (fun _ => zero_le _))
  filter_upwards [eventually_ge_atTop 3, eventually_ge_atTop C.t] with n hn htn
  exact actual_ratio_sum_bound C prior p hp hpsum n hn htn

theorem consGeneral_probability (C : LocationConfig) (prior : ConcentrationPrior)
    (p : Fin C.t → ℝ) (hp : ∀ j, 0 ≤ p j) (hpsum : ∑ j, p j = 1)
    (D rho nu : ℝ) (hD : 0 < D) (hnu : 0 < nu)
    (hrho : 4 * dpK5 C.U C.m C.c C.theta ≤ rho)
    (hA3_int : ∀ q : ℕ, 1 ≤ q → Integrable (fun a : ℝ => a^q * prior.dens a) volume)
    (hA3 : ∀ q : ℕ, 1 ≤ q → (∫ a : ℝ, a^q * prior.dens a ∂volume) <
      D * rho^(-(q:ℤ)) * Real.Gamma (nu+(q:ℝ)+1)) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => dpPinf C.g C.theta p
      {ω | ε < if dpOmega C.c C.theta C.N n ω then
        ∑ s ∈ Finset.Icc 1 (n-C.t), dpRatio C.g C.q0 prior.dens C.t n s ω else 0}) atTop (𝓝 0) := by
  apply tail_of_expectation
  · intro n
    exact Measurable.ite (omega C.c C.theta C.N n)
      (Finset.measurable_sum _ (fun s _ => ratio C.g C.q0 prior.dens C.hg C.hq prior.measurable_dens C.t n s)) measurable_const
  · exact consGeneral_complete C prior p hp hpsum D rho nu hD hnu hrho hA3_int hA3

/-- Density-form A3 version, directly compatible with the source ENNReal moment bound. -/
theorem consGeneral_complete_density (C : LocationConfig) (prior : ConcentrationPrior)
    (p : Fin C.t → ℝ) (hp : ∀ j, 0 ≤ p j) (hpsum : ∑ j, p j = 1)
    (D rho nu : ℝ) (hD : 0 < D) (hnu : 0 < nu)
    (hrho : 4 * dpK5 C.U C.m C.c C.theta ≤ rho)
    (hA3 : ∀ q : ℕ, 1 ≤ q →
      (∫⁻ a in Set.Ioi (0:ℝ), ENNReal.ofReal (a^q * prior.dens a)) ≤
        ENNReal.ofReal (D / rho^q * Real.Gamma (nu+(q:ℝ)+1))) :
    Tendsto (fun n : ℕ => ∫⁻ ω, ENNReal.ofReal (if dpOmega C.c C.theta C.N n ω then
        ∑ s ∈ Finset.Icc 1 (n-C.t), dpRatio C.g C.q0 prior.dens C.t n s ω else 0)
      ∂dpPinf C.g C.theta p) atTop (𝓝 0) := by
  have hlim := ManualDPConsAsymptotic.prior_ratio_bound_sum_tendsto_zero_of_density_A3 C prior D rho nu hD hnu hrho hA3
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall (fun _ => zero_le _))
  filter_upwards [eventually_ge_atTop 3, eventually_ge_atTop C.t] with n hn htn
  exact actual_ratio_sum_bound C prior p hp hpsum n hn htn

end OfflineDPConsGeneral
#print axioms OfflineDPConsGeneral.consGeneral_complete_density
