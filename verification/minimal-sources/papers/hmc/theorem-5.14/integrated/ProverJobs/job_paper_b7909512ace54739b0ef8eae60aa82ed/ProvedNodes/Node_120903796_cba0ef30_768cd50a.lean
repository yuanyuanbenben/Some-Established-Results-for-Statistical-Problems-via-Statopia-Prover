import ProverJobs.job_paper_b7909512ace54739b0ef8eae60aa82ed.Vocabulary
import ProverJobs.job_paper_b7909512ace54739b0ef8eae60aa82ed.Base

namespace PaperProofTasks.job_paper_b7909512ace54739b0ef8eae60aa82ed

open _root_.PaperProofTasks.job_paper_b7909512ace54739b0ef8eae60aa82ed.Statlib.Imported
open Filter Topology

namespace Statlib.Imported

open Filter Topology

set_option autoImplicit false in
theorem statopia_math_node_120903796_cba0ef30 : ∀ (d : ℕ) (hd : 0 < d)
    (U : EuclideanSpace ℝ (Fin d) → ℝ)
    (hU17 : Tendsto (fun x : EuclideanSpace ℝ (Fin d) => ‖gradient U x‖ / ‖x‖)
      (Filter.cocompact (EuclideanSpace ℝ (Fin d))) Filter.atTop)
    (eps : ℝ) (heps : 0 < eps) (delta : ℝ) (hdelta : delta < 1),
    ∀ᶠ x : EuclideanSpace ℝ (Fin d) in Filter.cocompact (EuclideanSpace ℝ (Fin d)),
      5 < (eps ^ 2 / 2) * (‖gradient U x‖ / ‖x‖) ∧ eps * ‖x‖ ^ (delta - 1) < 1 := by
  /- @proof-region region.target-node.session.ad6242b43285c348 begin -/
  intro d hd U hU17 eps heps delta hdelta
  have hlam : 0 < eps ^ 2 / 2 := by positivity
  have hlamne : eps ^ 2 / 2 ≠ 0 := hlam.ne'
  have hmain : ∀ᶠ x : EuclideanSpace ℝ (Fin d) in
      Filter.cocompact (EuclideanSpace ℝ (Fin d)),
      5 < (eps ^ 2 / 2) * (‖gradient U x‖ / ‖x‖) := by
    refine (hU17.eventually_gt_atTop (5 / (eps ^ 2 / 2))).mono ?_
    intro x hx
    have h5 : (eps ^ 2 / 2) * (5 / (eps ^ 2 / 2)) = 5 := by field_simp
    calc 5 = (eps ^ 2 / 2) * (5 / (eps ^ 2 / 2)) := h5.symm
      _ < (eps ^ 2 / 2) * (‖gradient U x‖ / ‖x‖) := mul_lt_mul_of_pos_left hx hlam
  have hsmall : ∀ᶠ x : EuclideanSpace ℝ (Fin d) in
      Filter.cocompact (EuclideanSpace ℝ (Fin d)),
      eps * ‖x‖ ^ (delta - 1) < 1 := by
    have hy : 0 < 1 - delta := by linarith
    have hnorm : Tendsto (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖)
        (Filter.cocompact (EuclideanSpace ℝ (Fin d))) atTop := by
      have h := tendsto_dist_left_cocompact_atTop (0 : EuclideanSpace ℝ (Fin d))
      simpa using h
    have hrpow : Tendsto (fun t : ℝ => t ^ (delta - 1)) atTop (nhds (0 : ℝ)) := by
      have h := tendsto_rpow_neg_atTop hy
      simpa using h
    have hconv : Tendsto (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖ ^ (delta - 1))
        (Filter.cocompact (EuclideanSpace ℝ (Fin d))) (nhds (0 : ℝ)) := hrpow.comp hnorm
    refine (hconv.eventually (show {t : ℝ | t < 1 / eps} ∈ nhds (0 : ℝ) from
      isOpen_Iio.mem_nhds (by rw [Set.mem_Iio]; positivity))).mono ?_
    intro x hx
    have h2 : eps * ‖x‖ ^ (delta - 1) < eps * (1 / eps) := mul_lt_mul_of_pos_left hx heps
    have h3 : eps * (1 / eps) = 1 := by field_simp
    linarith
  exact hmain.and hsmall
  /- @proof-region region.target-node.session.ad6242b43285c348 end -/

end Statlib.Imported

