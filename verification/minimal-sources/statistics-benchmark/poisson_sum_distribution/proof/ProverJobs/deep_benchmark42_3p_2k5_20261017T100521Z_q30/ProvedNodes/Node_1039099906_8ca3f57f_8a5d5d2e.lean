import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q30.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q30.Base

open MeasureTheory ProbabilityTheory
open Msc62GroundTruth

open MeasureTheory ProbabilityTheory
namespace Msc62GroundTruth

set_option autoImplicit false in
theorem statopia_math_node_1039099906_8ca3f57f : ∀ (n : ℕ) (m : Fin n → ℕ),
      (Nat.multinomial (Finset.univ : Finset (Fin n)) m) * (∏ i : Fin n, Nat.factorial (m i)) =
        Nat.factorial (∑ i : Fin n, m i) := by
  /- @proof-region region.target-node.session.ae51fa1b150a14b7 begin -/
  intro n m
  have h := Nat.multinomial_spec (Finset.univ : Finset (Fin n)) m
  rw [mul_comm]
  exact h
  /- @proof-region region.target-node.session.ae51fa1b150a14b7 end -/

end Msc62GroundTruth
