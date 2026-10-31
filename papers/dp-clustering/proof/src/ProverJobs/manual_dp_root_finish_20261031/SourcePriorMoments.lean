import ProverJobs.manual_dp_root_finish_20261031.NativePosterior
import ProverJobs.manual_dp_cons_asymptotic_20261031.Moments
open MeasureTheory Filter Topology
open scoped ENNReal
open Statlib.Imported ManualDPCons OfflineDPNativePosterior
noncomputable section
namespace OfflineDPSourcePriorMoments

/-- The source A3 measure bound supplies the exact density moments for the honest
positive-supported prior representative. No new moment hypothesis is imposed. -/
theorem source_prior_density_moments (π : Measure ℝ) [IsProbabilityMeasure π]
    (pidens : ℝ → ℝ) (hp : Measurable pidens)
    (hpi : π = volume.withDensity (fun a => ENNReal.ofReal (pidens a)))
    (hpos : ∀ᵐ a ∂π, 0<a) (hA2 : A2Cond pidens)
    (rho : ℝ) (hrho : 0<rho) (hA3 : A3AtRate π rho) :
    let prior := concentrationPriorOf π pidens hp hpi hpos hA2
    ∃ D nu : ℝ, 0<D ∧ 0<nu ∧ ∀ q : ℕ, 1≤q →
      (∫⁻ a in Set.Ioi (0:ℝ), ENNReal.ofReal (a^q * prior.dens a)) ≤
        ENNReal.ofReal (D / rho^q * Real.Gamma (nu+(q:ℝ)+1)) := by
  intro prior
  obtain ⟨D,nu,hD,hnu,hMoment⟩ := hA3
  refine ⟨D,nu,hD,hnu,?_⟩
  apply ManualDPConsAsymptotic.A3_measure_to_density prior.dens prior.measurable_dens
    (fun a => normalizedDensity_nonneg pidens a) D rho nu hrho
  intro q hq
  have hh := hMoment q hq
  rw [prior_eq_concentrationPriorOf π pidens hp hpi hpos hA2] at hh
  simpa only [Real.rpow_natCast] using hh

#print axioms source_prior_density_moments
end OfflineDPSourcePriorMoments
