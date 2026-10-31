import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q19.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q19.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q19.ProvedNodes.Node_887293322_4a71d68e_98cac379

open Msc62GroundTruth

namespace Msc62GroundTruth

set_option autoImplicit false in
theorem statopia_math_node_1004106233_18e3d102 : ∀ (n k : ℕ) (p : Fin k → ℝ) (hp_sum : (∑ c : Fin k, p c) = 1)
    (t : Fin n) (a : Fin k),
    (∑ x : Fin n → Fin k,
        (∏ u : Fin n, p (x u)) * (if x t = a then (1 : ℝ) else 0)) = p a := by
  /- @proof-region region.target-node.session.e8cb1c68aceedb4c begin -/
  intro n k p hp_sum t a
  let f : Fin n → Fin k → ℝ := fun u c => if u = t then (if c = a then p c else 0) else p c
  have h_engine :
      (∑ x : Fin n → Fin k, ∏ u : Fin n, f u (x u)) = ∏ u : Fin n, ∑ c : Fin k, f u c :=
    statopia_math_node_887293322_4a71d68e n k f
  have hfac : ∀ (x : Fin n → Fin k) (u : Fin n),
      f u (x u) = p (x u) * (if u = t then (if x t = a then (1 : ℝ) else 0) else 1) := by
    intro x u
    by_cases hu : u = t
    · rw [hu]
      simp [f]
    · have htu : ¬ (t = u) := fun h => hu h.symm
      simp [f, hu, htu]
  have h_point : ∀ x : Fin n → Fin k,
      (∏ u : Fin n, f u (x u)) =
        (∏ u : Fin n, p (x u)) * (if x t = a then (1 : ℝ) else 0) := by
    intro x
    calc (∏ u : Fin n, f u (x u))
        = ∏ u : Fin n, (p (x u) * (if u = t then (if x t = a then (1 : ℝ) else 0) else 1)) :=
          Finset.prod_congr rfl (fun u _ => hfac x u)
      _ = (∏ u : Fin n, p (x u)) *
            (∏ u : Fin n, (if u = t then (if x t = a then (1 : ℝ) else 0) else 1)) :=
          Finset.prod_mul_distrib
      _ = (∏ u : Fin n, p (x u)) * (if x t = a then (1 : ℝ) else 0) := by
          congr 1
          simp
  have h_prod : (∏ u : Fin n, ∑ c : Fin k, f u c) = p a := by
    have h1 : ∀ u : Fin n, (∑ c : Fin k, f u c) = (if u = t then p a else 1) := by
      intro u
      by_cases hu : u = t
      · rw [hu]
        simp [f]
      · have htu : ¬ (t = u) := fun h => hu h.symm
        simp [f, hu, htu, hp_sum]

    rw [Finset.prod_congr rfl (fun u _ => h1 u)]
    simp
  calc (∑ x : Fin n → Fin k,
          (∏ u : Fin n, p (x u)) * (if x t = a then (1 : ℝ) else 0))
      = ∑ x : Fin n → Fin k, ∏ u : Fin n, f u (x u) :=
        Finset.sum_congr rfl (fun x _ => (h_point x).symm)
    _ = ∏ u : Fin n, ∑ c : Fin k, f u c := h_engine
    _ = p a := h_prod
  /- @proof-region region.target-node.session.e8cb1c68aceedb4c end -/

end Msc62GroundTruth
