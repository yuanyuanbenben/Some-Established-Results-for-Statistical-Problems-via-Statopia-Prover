import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.Definitions
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M075_ConsGeneralComplete
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M076_RemoveGoodEvent
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M081_GoodOmega
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M085_LowTailActual
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M087_NormalizedPosterior
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M088_PosteriorAssembly

/- Original module ProverJobs.manual_dp_root_finish_20261031.ActualConsistency; genuine source relocated, namespace-isolated only. -/
namespace DPCompletedProof
open _root_.Statlib.Imported
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
noncomputable section
namespace OfflineDPRootActual
open Statlib.Imported ManualDPCons OfflineDPConsMeas
attribute [local instance] Classical.propDecidable

/-- The finite true data laws supply actual support and interior conditions on the
infinite observation process; the exceptional endpoint set is null. -/
lemma actual_good_prefix_ae (C : LocationConfig) (p : Fin C.t → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hp1 : ∑ j,p j=1) (n : ℕ) :
    ∀ᵐ ω ∂dpPinf C.g C.theta p,
      (∀ i : Fin n, ∃ j, ω (i:ℕ) ∈ Set.Icc (C.theta j-C.c) (C.theta j+C.c)) ∧
      (∀ j i, i ∈ dpBlock C.c C.theta n ω j → -C.c < ω (i:ℕ)-C.theta j) := by
  haveI := trueLaw_probability C p hp hp1
  have hmp : MeasurePreserving (dpXseq n) (dpPinf C.g C.theta p)
      (Measure.pi (fun _ : Fin n => dpPlaw C.g C.theta p)) :=
    ⟨measurable_pi_lambda _ (fun i => measurable_pi_apply (i:ℕ)), prefix_law _ n⟩
  have hgood := hmp.quasiMeasurePreserving.ae (trueLaw_ae_goodPrefix C p hp hp1 n)
  filter_upwards [hgood] with ω hω
  refine ⟨hω.1, ?_⟩
  intro j i hi
  have hblock : dpBlock C.c C.theta n (prefixPath (dpXseq n ω)) j = dpBlock C.c C.theta n ω j := by
    ext a
    simp [dpBlock,dpXseq]
  exact hω.2 j i (by rw [hblock]; exact hi)

/-- Posterior consistency for the actual partition posterior. All probability
bounds come from the proved model likelihood, A3 moments, and the source good event. -/
theorem actual_posterior_consistency (C : LocationConfig) (prior : ConcentrationPrior)
    (p : Fin C.t → ℝ) (hp : ∀ j, 0<p j) (hp1 : ∑ j,p j=1)
    (D rho nu : ℝ) (hD : 0<D) (hnu : 0<nu)
    (hrho : 4 * dpK5 C.U C.m C.c C.theta ≤ rho)
    (hA3_density : ∀ q : ℕ, 1≤q →
      (∫⁻ a in Set.Ioi (0:ℝ), ENNReal.ofReal (a^q * prior.dens a)) ≤
        ENNReal.ofReal (D / rho^q * Real.Gamma (nu+(q:ℝ)+1))) :
    TendstoInMeasure (dpPinf C.g C.theta p)
      (fun n ω => dpPostProb C.g C.q0 prior.dens n C.t ω) atTop (fun _ => (1:ℝ)) := by
  let μ := dpPinf C.g C.theta p
  haveI := trueLaw_probability C p (fun j => (hp j).le) hp1
  haveI : IsProbabilityMeasure μ := by dsimp [μ,dpPinf]; infer_instance
  let high : ℕ → (ℕ → ℝ) → ℝ := fun n ω =>
    ∑ s ∈ Finset.Icc 1 (n-C.t), dpRatio C.g C.q0 prior.dens C.t n s ω
  let low : ℕ → (ℕ → ℝ) → ℝ := fun n ω =>
    ∑ k ∈ Finset.Icc 1 (C.t-1), dpPostProb C.g C.q0 prior.dens n k ω
  let Ω : ℕ → Set (ℕ → ℝ) := fun n => {ω | dpOmega C.c C.theta C.N n ω}
  have hΩmeas : ∀ n, MeasurableSet (Ω n) := fun n => omega C.c C.theta C.N n
  have hΩprob : Tendsto (fun n => μ (Ω n)) atTop (𝓝 1) :=
    OfflineDPRootGoodOmega.good_omega_probability C p hp hp1
  have hΩcompl := OfflineDPConsGeneral.complement_probability μ Ω hΩmeas hΩprob
  have hhighlocal : ∀ ε : ℝ, 0<ε → Tendsto (fun n => μ {ω | ε < if ω∈Ω n then high n ω else 0}) atTop (𝓝 0) := by
    apply OfflineDPConsGeneral.tail_of_expectation
    · intro n
      exact Measurable.ite (hΩmeas n)
        (Finset.measurable_sum _ (fun s hs => ratio C.g C.q0 prior.dens C.hg C.hq prior.measurable_dens C.t n s)) measurable_const
    · exact OfflineDPConsGeneral.consGeneral_complete_density C prior p (fun j => (hp j).le) hp1 D rho nu hD hnu hrho hA3_density
  have hhigh := OfflineDPConsGeneral.remove_good_event μ Ω hΩmeas hΩprob high hhighlocal
  have hlow : ∀ ε : ℝ, 0<ε → Tendsto (fun n => μ {ω | ε < low n ω}) atTop (𝓝 0) :=
    low_tail_probability C prior p hp hp1
  let G : ℕ → Set (ℕ → ℝ) := fun n => {ω | dpOmega C.c C.theta C.N n ω ∧
      (∀ i : Fin n, ∃ j, ω (i:ℕ) ∈ Set.Icc (C.theta j-C.c) (C.theta j+C.c)) ∧
      (∀ j i, i ∈ dpBlock C.c C.theta n ω j → -C.c < ω (i:ℕ)-C.theta j)}
  have hGeq : ∀ n, μ (G n)ᶜ = μ (Ω n)ᶜ := by
    intro n
    apply measure_congr
    filter_upwards [actual_good_prefix_ae C p (fun j => (hp j).le) hp1 n] with ω hω
    apply propext
    change (¬ (dpOmega C.c C.theta C.N n ω ∧ _ ∧ _)) ↔ ¬ dpOmega C.c C.theta C.N n ω
    constructor
    · intro hbad hOmega
      exact hbad ⟨hOmega,hω.1,hω.2⟩
    · intro hbad hGood
      exact hbad hGood.1
  have hG : Tendsto (fun n => μ (G n)ᶜ) atTop (𝓝 0) := by simpa only [hGeq] using hΩcompl
  apply OfflineDPRoot.posterior_converges_from_tails μ
    (fun n ω => dpPostProb C.g C.q0 prior.dens n C.t ω) low high G hG ?_ hlow hhigh
  filter_upwards [eventually_ge_atTop 3,eventually_ge_atTop (C.t+1)] with n hn htn
  intro ω hω
  exact OfflineDPActualNormalization.actual_posterior_control C prior n hn htn ω hω.1 hω.2.1 hω.2.2

end OfflineDPRootActual
end
end DPCompletedProof
