import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.Definitions
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M031_Vocabulary
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M032_Base
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M033_Node_1445702134_3c8d3810_8f7a15fe
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M034_Node_3224678180_5a630a9f_7124eef7
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M055_Node_3226374292_602af891_fc833d1a
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M036_Node_3788355289_2a3e6b7e_b3f2870a
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M056_Node_3843288360_478d1772_0d519a1c

/- Original module ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.ProvedNodes.Node_4213379669_bb9a52d2_f7733836; genuine source relocated, namespace-isolated only. -/
namespace DPCompletedProof
open _root_.Statlib.Imported



open MeasureTheory
open Statlib.Imported

noncomputable section
open MeasureTheory
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_4213379669_bb9a52d2 : ∀ (t : ℝ) (ht : 1 ≤ t) (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1 / 2)
    (δ β : ℝ) (hδ : 0 < δ) (hβ : 0 < β)
    (π : ℝ → ℝ) (hπ_meas : Measurable π)
    (hπ_nonneg : ∀ α ∈ Set.Ioi (0 : ℝ), 0 ≤ π α)
    (hπ_prob : ∫⁻ α in Set.Ioi (0 : ℝ), ENNReal.ofReal (π α) = 1)
    (hA2 : ∀ α ∈ Set.Ioo (0 : ℝ) ε, δ⁻¹ * α ^ β ≤ π α ∧ π α ≤ δ * α ^ β)
    (m : ℕ) (htm : t ≤ (m : ℝ))
    (hmn : ∀ k : ℕ, t + 1 ≤ (k : ℝ) → (m : ℝ) ≤ (k : ℝ) - 1)
    (K : ℝ) (hK : K = t + β + 1) (n : ℕ) (hn : t + 1 ≤ (n : ℝ)),
    ((∫ a in Set.Ioi ε, a ^ t / risingFac a n * π a) ≤
        Real.exp 1 * ((m + 1).factorial : ℝ) / (ε * (n : ℝ) ^ ε * ((n - 1).factorial : ℝ)))
      ∧ ((δ * 2 ^ K * Real.exp 3)⁻¹ * (min ε (1 / Real.log (n : ℝ))) ^ K / ((n - 1).factorial : ℝ) ≤
        ∫ a in Set.Ioo (0 : ℝ) ε, a ^ t / risingFac a n * π a) := by
  /- @proof-region region.target-node.session.dfa67e7a50dd398e begin -/
  intro t ht ε hε_pos hε_lt δ β hδ hβ π hπ_meas hπ_nonneg hπ_prob hA2 m htm hmn K hK n hn
  constructor
  · exact statopia_math_node_3226374292_602af891 t ht ε hε_pos hε_lt π hπ_meas hπ_nonneg hπ_prob m htm n hn
  · exact statopia_math_node_3843288360_478d1772 t ht ε hε_pos hε_lt δ β hδ hβ π hπ_meas hπ_nonneg hπ_prob hA2 K hK n hn
  /- @proof-region region.target-node.session.dfa67e7a50dd398e end -/

end Statlib.Imported
end
end DPCompletedProof
