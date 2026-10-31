import Statlib.StatFoundation.Convergence.AnalysisTools.ConvergenceModes
import ProverJobs.job_paper_2fbfd1902da645daba7b723031e5be32.Vocabulary
import ProverJobs.job_paper_2fbfd1902da645daba7b723031e5be32.ProvedNodes
import ProverJobs.job_paper_2fbfd1902da645daba7b723031e5be32.Base

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators
namespace Statlib.Imported

theorem paper_2fbfd1902da645daba7b723031e5be32
    {X : Type*} [TopologicalSpace X] [MeasureSpace X] [OpensMeasurableSpace X]
    {Θ : Type*} (μ : Measure X) (k : Θ → X → ℝ≥0∞) (t : ℕ)
    (fseq : ℕ → X → ℝ≥0∞) (f : X → ℝ≥0∞)
    (hμ : μ = volume ∨ μ = Measure.count)
    (hk_meas : ∀ θ, Measurable (k θ))
    (hk_prob : ∀ θ, IsProbDensity μ (k θ))
    (hf_mix : ∀ i, ∃ s, 1 ≤ s ∧ s < t ∧ ExactMixture k s (fseq i))
    (hf_prob : ∀ i, IsProbDensity μ (fseq i))
    (hf_prob_lim : IsProbDensity μ f)
    (hconv : Statlib.StatFoundation.Convergence.WeakConvergence
      (fun i => ⟨μ.withDensity (fseq i), hf_prob i⟩)
      ⟨μ.withDensity f, hf_prob_lim⟩) :
    ∃ s' : ℕ, 1 ≤ s' ∧ s' < t ∧
      ∃ (f' : ℕ → X → ℝ≥0∞) (hf'_prob : ∀ i, IsProbDensity μ (f' i)),
        (∀ i, ExactMixture k s' (f' i)) ∧
        Statlib.StatFoundation.Convergence.WeakConvergence
          (fun i => ⟨μ.withDensity (f' i), hf'_prob i⟩)
          ⟨μ.withDensity f, hf_prob_lim⟩
:= by
  /- @proof-region region.root.251b2fa3e257 begin -/
  classical
  choose sval hsval using hf_mix
  let σ : ℕ → Fin t := fun i => ⟨sval i, (hsval i).2.1⟩
  have hσ_pos : ∀ i, 1 ≤ (σ i).val := fun i => (hsval i).1
  have hσ_mix : ∀ i, ExactMixture k (σ i).val (fseq i) := fun i => (hsval i).2.2
  obtain ⟨s', φ, hφ_mono, hφ_const, _hφ_inf, hs'_pos, hs'_lt⟩ :=
    statopia_math_node_3150573278_33848bea t σ hσ_pos
  refine ⟨s'.val, hs'_pos, hs'_lt, (fun n => fseq (φ n)), (fun n => hf_prob (φ n)), ?_, ?_⟩
  · intro n
    have h := hσ_mix (φ n)
    rw [hφ_const n] at h
    exact h
  · unfold Statlib.StatFoundation.Convergence.WeakConvergence at hconv ⊢
    exact hconv.comp hφ_mono.tendsto_atTop
  /- @proof-region region.root.251b2fa3e257 end -/

end Statlib.Imported
