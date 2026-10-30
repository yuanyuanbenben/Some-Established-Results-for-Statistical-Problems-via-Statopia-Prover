import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q33.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q33.Base

open Msc62GroundTruth

namespace Msc62GroundTruth

set_option autoImplicit false in
theorem statopia_math_node_1457182788_f9803ee7 : ∀ (N H : ℕ) (group : Fin N → Fin H) (F : Fin N → ℝ),
    ∑ i : Fin N, F i
      = ∑ g : Fin H, ∑ i ∈ Finset.univ.filter (fun i : Fin N => group i = g), F i := by
  /- @proof-region region.target-node.session.3ea05bd0f049cad4 begin -/
  intro N H group F
  exact (Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
    (g := group) (fun i _ => Finset.mem_univ (group i)) F).symm
  /- @proof-region region.target-node.session.3ea05bd0f049cad4 end -/

end Msc62GroundTruth
