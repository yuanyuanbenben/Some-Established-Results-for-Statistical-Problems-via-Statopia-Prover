import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.Definitions
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M084_LowTail
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M030_NativePosterior

/- Original module ProverJobs.manual_dp_root_finish_20261031.LowTailActual; genuine source relocated, namespace-isolated only. -/
namespace DPCompletedProof
open _root_.Statlib.Imported
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
noncomputable section
namespace OfflineDPRootActual
open Statlib.Imported ManualDPCons OfflineDPNativePosterior

lemma normalized_prior_density (prior : ConcentrationPrior) : normalizedDensity prior.dens = prior.dens := by
  funext a
  by_cases ha : 0<a
  · simp only [normalizedDensity,if_pos ha,max_eq_left (prior.nonneg a ha)]
  · simp only [normalizedDensity,if_neg ha,prior.zero a (not_lt.mp ha)]

lemma prior_positive_support (prior : ConcentrationPrior) :
    ∀ᵐ a ∂volume.withDensity (fun a => ENNReal.ofReal (prior.dens a)), 0<a := by
  apply (ae_withDensity_iff prior.measurable_dens.ennreal_ofReal).mpr
  exact Eventually.of_forall (fun a ha => by
    by_contra h
    exact ha (by rw [prior.zero a (not_lt.mp h),ENNReal.ofReal_zero]))

/-- Low cluster-count posterior mass vanishes for the actual density-form
posterior used by consGeneral, not only a separately defined root posterior. -/
theorem low_tail_probability (C : LocationConfig) (prior : ConcentrationPrior)
    (p : Fin C.t → ℝ) (hp : ∀ j, 0<p j) (hp1 : ∑ j,p j=1) :
    ∀ ε : ℝ, 0<ε → Tendsto (fun n => dpPinf C.g C.theta p
      {ω | ε < ∑ k ∈ Finset.Icc 1 (C.t-1), dpPostProb C.g C.q0 prior.dens n k ω}) atTop (𝓝 0) := by
  let π := volume.withDensity (fun a => ENNReal.ofReal (prior.dens a))
  have hpos : ∀ᵐ a ∂π, 0<a := prior_positive_support prior
  haveI := trueLaw_probability C p (fun j => (hp j).le) hp1
  have heq (n k : ℕ) (ω : ℕ → ℝ) : dpPostProb C.g C.q0 prior.dens n k ω =
      postProb C.g C.q0 π n k (dpXseq n ω) := by
    simpa only [normalized_prior_density] using native_sample_posterior_eq C.g C.q0 π prior.dens prior.measurable_dens rfl hpos n k ω
  simp_rw [heq]
  exact OfflineDPRoot.low_tail_probability C.g C.q0 C.c C.m C.hc C.hm C.hglo C.hgzero C.t C.ht
    (dpPlaw C.g C.theta p) p (dpRmeasure C.g C.theta) C.theta hp (fun _ => rfl) rfl C.hsep π
end OfflineDPRootActual
end
end DPCompletedProof
