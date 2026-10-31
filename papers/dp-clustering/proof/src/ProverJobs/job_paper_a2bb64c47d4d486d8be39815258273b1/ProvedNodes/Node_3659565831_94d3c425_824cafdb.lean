import ProverJobs.job_paper_a2bb64c47d4d486d8be39815258273b1.Vocabulary
import ProverJobs.job_paper_a2bb64c47d4d486d8be39815258273b1.Base
import ProverJobs.job_paper_a2bb64c47d4d486d8be39815258273b1.ProvedNodes.Node_506867901_9a1a90e8_6d07b462

open MeasureTheory
open Classical
open Statlib.Imported

open MeasureTheory
open Classical
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_3659565831_94d3c425 : ∀ (c : ℝ) (hc : 0 < c) (g : ℝ → ℝ) (R theta_star : ℝ)
    (n : ℕ) (x : Fin n → ℝ) (S : Finset (Fin n)) (hne : S.Nonempty)
    (hwin : ∀ i ∈ S, x i ∈ Set.Icc (theta_star - c) (theta_star + c))
    (hpos : ∀ y ∈ Set.Icc (-c) c, 0 < g y)
    (hlip : ∀ u ∈ Set.Icc (-c) c, ∀ v ∈ Set.Icc (-c) c,
      |Real.log (g u) - Real.log (g v)| ≤ R * |u - v|)
    (theta : ℝ)
    (htheta_lo : (S.image x).max' (hne.image x) - c ≤ theta)
    (htheta_hi : theta ≤ (S.image x).min' (hne.image x) + c),
    Real.exp (-(R * (S.card : ℝ) * |theta - theta_star|)) ≤
      ∏ i ∈ S, g (x i - theta) / g (x i - theta_star) := by
  /- @proof-region region.target-node.session.5ffc9430bf14dc5c begin -/
  intro c hc g R theta_star n x S hne hwin hpos hlip theta htheta_lo htheta_hi
  have hpt : ∀ i ∈ S,
      Real.exp (-(R * |theta - theta_star|)) ≤ g (x i - theta) / g (x i - theta_star) :=
    fun i hi =>
      statopia_math_node_506867901_9a1a90e8 c hc g R theta_star n x S hne hwin hpos hlip
        theta htheta_lo htheta_hi i hi
  have hnn : ∀ i ∈ S, (0 : ℝ) ≤ Real.exp (-(R * |theta - theta_star|)) :=
    fun _ _ => (Real.exp_pos _).le
  have hprod := Finset.prod_le_prod hnn hpt
  rw [Finset.prod_const] at hprod
  have hexp : Real.exp (-(R * |theta - theta_star|)) ^ S.card =
      Real.exp (-(R * (S.card : ℝ) * |theta - theta_star|)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hexp] at hprod
  exact hprod
  /- @proof-region region.target-node.session.5ffc9430bf14dc5c end -/

end Statlib.Imported
