import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.Definitions
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M082_StripsOccupancy
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M083_PartitionLow

/- Original module ProverJobs.manual_dp_root_finish_20261031.LowTail; genuine source relocated, namespace-isolated only. -/
namespace DPCompletedProof
open _root_.Statlib.Imported

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators
open Statlib.Imported
noncomputable section
namespace OfflineDPRoot

/-- The actual finite-partition posterior has vanishing low tail under complete
separation. This does not assume an abstract DP law or posterior consistency. -/
theorem low_tail_probability (g q0 : ℝ → ℝ) (c m : ℝ)
    (hc : 0 < c) (hm : 0 < m)
    (hT1 : ∀ x ∈ Set.Icc (-c) c, m ≤ g x)
    (hsupport : ∀ x : ℝ, x ∉ Set.Icc (-c) c → g x = 0)
    (t : ℕ) (ht : 1 ≤ t) (P : Measure ℝ) [IsProbabilityMeasure P]
    (p : Fin t → ℝ) (Rm : Fin t → Measure ℝ) (θ : Fin t → ℝ)
    (hp : ∀ j, 0 < p j)
    (hRm : ∀ j, Rm j = volume.withDensity (fun x => ENNReal.ofReal (g (x-θ j))))
    (hP : P = ∑ j, ENNReal.ofReal (p j) • Rm j)
    (hsep : ∀ i j, i ≠ j → 2*c < |θ i - θ j|) (π : Measure ℝ) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => (iidLaw P)
      {ω : ℕ → ℝ | ε < ∑ s ∈ Finset.Icc 1 (t-1),
        postProb g q0 π n s (fun i : Fin n => ω (i : ℕ))}) atTop (𝓝 0) := by
  intro ε hε
  have hlim := separated_representatives g c m hc hm hT1 t ht P p Rm θ hp hRm hP hsep
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => zero_le _) (fun n => measure_mono ?_)
  intro ω hω hgood
  obtain ⟨idx,hidx⟩ := hgood
  have hzero := OfflineDPRootPartitionLow.low_tail_sum_zero g q0 c hsupport π
    (fun i : Fin n => ω (i : ℕ)) idx hidx
  exact (not_lt_of_ge (le_of_lt hε)) (hzero ▸ hω)

end OfflineDPRoot
end
end DPCompletedProof
