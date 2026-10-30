import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q19.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q19.Base

open Msc62GroundTruth

namespace Msc62GroundTruth

set_option autoImplicit false in
theorem statopia_math_node_887293322_4a71d68e : ∀ (n k : ℕ) (f : Fin n → Fin k → ℝ),
    (∑ x : Fin n → Fin k, ∏ t : Fin n, f t (x t))
      = ∏ t : Fin n, ∑ c : Fin k, f t c := by
  /- @proof-region region.target-node.session.b34fa9831e757c87 begin -/
  intro n k f
  have hp : Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset (Fin k))) = Finset.univ := by
    ext x
    simp
  rw [Finset.prod_univ_sum (t := fun _ : Fin n => (Finset.univ : Finset (Fin k)))
    (f := fun t c => f t c), hp]
  /- @proof-region region.target-node.session.b34fa9831e757c87 end -/

end Msc62GroundTruth
