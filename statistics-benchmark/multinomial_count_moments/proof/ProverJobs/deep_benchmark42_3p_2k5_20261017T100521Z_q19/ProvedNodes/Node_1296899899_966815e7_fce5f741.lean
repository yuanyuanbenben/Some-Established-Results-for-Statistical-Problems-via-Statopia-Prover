import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q19.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q19.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q19.ProvedNodes.Node_1004106233_18e3d102_94116a57
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q19.ProvedNodes.Node_887293322_4a71d68e_98cac379


open Msc62GroundTruth

namespace Msc62GroundTruth

set_option autoImplicit false in
theorem statopia_math_node_1296899899_966815e7 : ∀ (n k : ℕ) (p : Fin k → ℝ) (hp_sum : (∑ c : Fin k, p c) = 1) (a : Fin k),
    (∑ x : Fin n → Fin k,
        (∏ t : Fin n, p (x t)) *
          ((∑ t : Fin n, if x t = a then (1 : ℕ) else 0) : ℝ)) =
      (n : ℝ) * p a := by
  /- @proof-region region.target-node.session.8c2e8fdc19fac050 begin -/
  intro n k p hp_sum a
  have hcast : ∀ x : Fin n → Fin k,
      ((∑ t : Fin n, if x t = a then (1 : ℕ) else 0) : ℝ)
        = ∑ t : Fin n, (if x t = a then (1 : ℝ) else 0) := by
    intro x
    refine Finset.sum_congr rfl ?_
    intro t _
    by_cases h : x t = a <;> simp [h]
  calc (∑ x : Fin n → Fin k,
        (∏ t : Fin n, p (x t)) *
          ((∑ t : Fin n, if x t = a then (1 : ℕ) else 0) : ℝ))
      = ∑ x : Fin n → Fin k,
          (∏ t : Fin n, p (x t)) *
            (∑ t : Fin n, (if x t = a then (1 : ℝ) else 0)) := by
        refine Finset.sum_congr rfl ?_
        intro x _
        simp only [hcast x]
    _ = ∑ x : Fin n → Fin k, ∑ t : Fin n,
          (∏ u : Fin n, p (x u)) * (if x t = a then (1 : ℝ) else 0) := by
        refine Finset.sum_congr rfl ?_
        intro x _
        simp only [Finset.mul_sum]
    _ = ∑ t : Fin n, ∑ x : Fin n → Fin k,
          (∏ u : Fin n, p (x u)) * (if x t = a then (1 : ℝ) else 0) :=
        Finset.sum_comm
    _ = ∑ t : Fin n, p a := by
        refine Finset.sum_congr rfl ?_
        intro t _
        exact statopia_math_node_1004106233_18e3d102 n k p hp_sum t a
    _ = (n : ℝ) * p a := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  /- @proof-region region.target-node.session.8c2e8fdc19fac050 end -/

end Msc62GroundTruth
