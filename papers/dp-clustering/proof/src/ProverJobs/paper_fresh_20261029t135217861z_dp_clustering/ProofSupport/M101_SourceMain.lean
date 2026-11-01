import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.Definitions
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M023_SourceConfig
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M066_SourcePriorMoments
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M089_ActualConsistency
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M100_FixedAlpha

/- Original module ProverJobs.manual_dp_root_finish_20261031.SourceMain; genuine source relocated, namespace-isolated only. -/
namespace DPCompletedProof
open _root_.Statlib.Imported
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
noncomputable section
namespace OfflineDPSourceMain
open Statlib.Imported ManualDPCons OfflineDPNativePosterior

/-- Complete current-task Theorem 1 with the omitted source B3 bound restored.
This retains the legacy task analytic assumptions, including A2Cond beta > 0;
it does not assert coverage of every prior allowed by the paper (e.g. beta = 0).
The rate threshold is chosen before the prior.
No posterior, evidence, expectation, or convergence conclusion is a hypothesis. -/
theorem source_theorem_1
    (g q0 : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hg_meas : Measurable g) (hg_nonneg : ∀ x, 0 ≤ g x)
    (hg_density : ∫⁻ x, ENNReal.ofReal (g x) ∂volume = 1)
    (hq0_meas : Measurable q0) (hq0_nonneg : ∀ x, 0 ≤ q0 x)
    (hq0_density : ∫⁻ x, ENNReal.ofReal (q0 x) ∂volume = 1)
    (hT1 : ∃ m M : ℝ, 0 < m ∧ m ≤ M ∧ ∀ x ∈ Set.Icc (-c) c, m ≤ g x ∧ g x ≤ M)
    
    
    (hg_support : ∀ x : ℝ, x ∉ Set.Icc (-c) c → g x = 0)
    (hT2 : DifferentiableOn ℝ g (Set.Ioo (-c) c) ∧
      ∃ Rd : ℝ, 0 < Rd ∧ ∀ x ∈ Set.Ioo (-c) c, |deriv g x / g x| ≤ Rd)
    (hB3 : ∃ B : ℝ, ∀ x, q0 x ≤ B) :
    ( 
     
     
     
     
     
     ∀ (t : ℕ) (P : Measure ℝ) (p : Fin t → ℝ) (Rm : Fin t → Measure ℝ) (θstar : Fin t → ℝ),
        IsDataConfig g q0 c t P p Rm θstar →
        ∃ ρ0 : ℝ, 0 < ρ0 ∧
          ∀ (π : Measure ℝ) (πdens : ℝ → ℝ),
            IsProbabilityMeasure π →
            Measurable πdens →
            
            π = volume.withDensity (fun α => ENNReal.ofReal (πdens α)) →
            (∀ᵐ α ∂π, 0 < α) →
            
            A2Cond πdens →
            
            (∃ ρ : ℝ, ρ0 ≤ ρ ∧ A3AtRate π ρ) →
            TendstoInMeasure (iidLaw P)
              (fun (n : ℕ) (ω : ℕ → ℝ) => postProb g q0 π n t (fun i : Fin n => ω (i : ℕ)))
              atTop (fun _ => (1 : ℝ))) ∧
    ( 
     ∀ (αstar : ℝ), 0 < αstar →
        ∀ (t : ℕ) (P : Measure ℝ) (p : Fin t → ℝ) (Rm : Fin t → Measure ℝ)
          (θstar : Fin t → ℝ),
          IsDataConfig g q0 c t P p Rm θstar →
          ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
            iidLaw P {ω : ℕ → ℝ |
                1 - η <
                  postProb g q0 (Measure.dirac αstar) n t (fun i : Fin n => ω (i : ℕ))} ≤
              ENNReal.ofReal ε)
 := by
  obtain ⟨B,hB⟩ := hB3
  constructor
  · intro t P p Rm theta hData
    obtain ⟨C,hCt,hCc,hCg,hCq,hCtheta,hCU,hCN⟩ :=
      exists_config_from_source g q0 c hc hg_meas hg_nonneg hg_density hg_support
        hq0_meas hq0_nonneg hq0_density hT1 hT2 B hB t P p Rm theta hData
    cases hCt
    cases hCc
    cases hCg
    cases hCq
    cases hCtheta
    let rho0 := max 1 (4*dpK5 C.U C.m C.c C.theta)
    have hrho0 : 0<rho0 := zero_lt_one.trans_le (le_max_left _ _)
    refine ⟨rho0,hrho0,?_⟩
    intro pi pidens hpi_prob hpi_meas hpi_eq hpi_pos hA2 hA3
    haveI := hpi_prob
    obtain ⟨rho,hrho,hA3⟩ := hA3
    have hrhoP : 0<rho := hrho0.trans_le hrho
    let prior := concentrationPriorOf pi pidens hpi_meas hpi_eq hpi_pos hA2
    obtain ⟨D,nu,hD,hnu,hMom⟩ := OfflineDPSourcePriorMoments.source_prior_density_moments
      pi pidens hpi_meas hpi_eq hpi_pos hA2 rho hrhoP hA3
    rcases hData with ⟨ht,hp,hp1,hRprob,hReq,hRinj,hsep,hsupp,hT4,hP⟩
    have hPlaw : dpPlaw C.g C.theta p = P := by
      rw [hP]
      unfold dpPlaw dpRmeasure
      simp_rw [hReq]
    have hActual := OfflineDPRootActual.actual_posterior_consistency C prior p hp hp1 D rho nu hD hnu
      ((le_max_right _ _).trans hrho) hMom
    have heq (n : ℕ) (ω : ℕ → ℝ) : dpPostProb C.g C.q0 prior.dens n C.t ω =
        postProb C.g C.q0 pi n C.t (fun i : Fin n => ω (i:ℕ)) := by
      exact native_sample_posterior_eq C.g C.q0 pi pidens hpi_meas hpi_eq hpi_pos n C.t ω
    simp_rw [heq] at hActual
    simpa only [dpPinf,hPlaw,iidLaw] using hActual
  · have hT3 : ∃ U : ℝ, 0<U ∧ ∀ y ∈ Set.Icc (0:ℝ) (2*c), q0 y+q0 (-y)≤U := by
      refine ⟨2*max 1 B,by positivity,?_⟩
      intro y hy
      have hy1 := hB y
      have hy2 := hB (-y)
      have hBm := le_max_right 1 B
      linarith
    exact OfflineDPRootFixedAlpha.fixed_alpha_inconsistency g q0 c hc hg_meas hg_nonneg hg_density
      hq0_meas hq0_nonneg hq0_density hT1 hg_support hT2 hT3

end OfflineDPSourceMain
end
end DPCompletedProof
