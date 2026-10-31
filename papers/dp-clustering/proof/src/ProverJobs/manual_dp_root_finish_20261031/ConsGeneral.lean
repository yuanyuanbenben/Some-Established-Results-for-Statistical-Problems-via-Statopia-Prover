import ProverJobs.manual_dp_root_finish_20261031.ConsMeasurability
import ProverJobs.manual_dp_cons_finish_20261031.PosteriorRatio
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
noncomputable section
namespace OfflineDPConsGeneral
attribute [local instance] Classical.propDecidable
open Statlib.Imported ManualDPCons OfflineDPConsMeas

lemma finite_integrand_measurable (C : LocationConfig) (prior : ConcentrationPrior) (n s : ℕ) :
    Measurable (posteriorRatioIntegrand C prior.dens n s) := by
  unfold posteriorRatioIntegrand
  exact Measurable.ite ((omega C.c C.theta C.N n).preimage (prefixPath_measurable n))
    ((ratio C.g C.q0 prior.dens C.hg C.hq prior.measurable_dens C.t n s).comp (prefixPath_measurable n)) measurable_const

lemma prefix_integrand (C : LocationConfig) (prior : ConcentrationPrior) (n s : ℕ) (ω : ℕ → ℝ) :
    posteriorRatioIntegrand C prior.dens n s (dpXseq n ω) =
      if dpOmega C.c C.theta C.N n ω then dpRatio C.g C.q0 prior.dens C.t n s ω else 0 := by
  classical
  unfold posteriorRatioIntegrand
  rw [omega_prefix, ratio_prefix]

/-- Finite-sample sum bound for the actual posterior under the actual infinite iid law. -/
theorem actual_ratio_sum_bound (C : LocationConfig) (prior : ConcentrationPrior)
    (p : Fin C.t → ℝ) (hp : ∀ j, 0 ≤ p j) (hpsum : ∑ j, p j = 1)
    (n : ℕ) (hn : 3 ≤ n) (htn : C.t ≤ n) :
    (∫⁻ ω, ENNReal.ofReal (if dpOmega C.c C.theta C.N n ω then
        ∑ s ∈ Finset.Icc 1 (n-C.t), dpRatio C.g C.q0 prior.dens C.t n s ω else 0)
      ∂dpPinf C.g C.theta p) ≤
      ∑ s ∈ Finset.Icc 1 (n-C.t),
        ENNReal.ofReal (priorRatio prior.dens C.t n s) *
        ENNReal.ofReal (denominatorLoss C n * (dpK5 C.U C.m C.c C.theta)^(C.t+s) / ((C.t+s).factorial : ℝ)) := by
  classical
  haveI := trueLaw_probability C p hp hpsum
  have hpoint (ω : ℕ → ℝ) :
      ENNReal.ofReal (if dpOmega C.c C.theta C.N n ω then
        ∑ s ∈ Finset.Icc 1 (n-C.t), dpRatio C.g C.q0 prior.dens C.t n s ω else 0) ≤
        ∑ s ∈ Finset.Icc 1 (n-C.t), ENNReal.ofReal (posteriorRatioIntegrand C prior.dens n s (dpXseq n ω)) := by
    simp_rw [prefix_integrand]
    split_ifs with h
    · have hsum : ∀ (S : Finset ℕ) (f : ℕ → ℝ), ENNReal.ofReal (∑ s ∈ S, f s) ≤ ∑ s ∈ S, ENNReal.ofReal (f s) := by
        intro S f
        induction S using Finset.induction_on with
        | empty => simp
        | @insert a S ha ih =>
          simp only [Finset.sum_insert ha]
          exact ENNReal.ofReal_add_le.trans (add_le_add le_rfl ih)
      exact hsum _ _
    · simp
  calc
    _ ≤ ∫⁻ ω, ∑ s ∈ Finset.Icc 1 (n-C.t), ENNReal.ofReal (posteriorRatioIntegrand C prior.dens n s (dpXseq n ω)) ∂dpPinf C.g C.theta p := lintegral_mono hpoint
    _ = ∑ s ∈ Finset.Icc 1 (n-C.t), ∫⁻ ω, ENNReal.ofReal (posteriorRatioIntegrand C prior.dens n s (dpXseq n ω)) ∂dpPinf C.g C.theta p := by
      apply lintegral_finset_sum
      intro s hs
      exact ((finite_integrand_measurable C prior n s).ennreal_ofReal.comp
        (measurable_pi_lambda _ (fun i : Fin n => (measurable_pi_apply (i:ℕ) : Measurable (fun ω : ℕ → ℝ => ω (i:ℕ))))))
    _ = ∑ s ∈ Finset.Icc 1 (n-C.t), ∫⁻ x : Fin n → ℝ, ENNReal.ofReal (posteriorRatioIntegrand C prior.dens n s x)
        ∂Measure.pi (fun _ : Fin n => dpPlaw C.g C.theta p) := by
      apply Finset.sum_congr rfl
      intro s hs
      exact prefix_lintegral _ n _ (finite_integrand_measurable C prior n s).ennreal_ofReal
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro s hs
      exact posterior_ratio_expectation_bound C prior p hp hpsum n s hn htn
        (Finset.mem_Icc.mp hs).1 (by have := (Finset.mem_Icc.mp hs).2; omega)

end OfflineDPConsGeneral
#print axioms OfflineDPConsGeneral.actual_ratio_sum_bound
