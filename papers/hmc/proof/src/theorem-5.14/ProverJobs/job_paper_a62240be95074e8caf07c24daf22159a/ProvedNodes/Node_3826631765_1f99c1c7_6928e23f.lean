import ProverJobs.job_paper_a62240be95074e8caf07c24daf22159a.Vocabulary
import ProverJobs.job_paper_a62240be95074e8caf07c24daf22159a.Base

namespace PaperProofTasks.job_paper_a62240be95074e8caf07c24daf22159a

open _root_.PaperProofTasks.job_paper_a62240be95074e8caf07c24daf22159a.Statlib.Imported

namespace Statlib.Imported


set_option autoImplicit false in
theorem statopia_math_node_3826631765_1f99c1c7 : ∀ (d : ℕ)
    (U : EuclideanSpace ℝ (Fin d) → ℝ)
    (h17 : Filter.Tendsto (fun x : EuclideanSpace ℝ (Fin d) => ‖gradient U x‖ / ‖x‖)
      (Filter.cocompact (EuclideanSpace ℝ (Fin d))) Filter.atTop)
    (ε : ℝ) (hε : 0 < ε),
    ∃ R : ℝ, 1 ≤ R ∧
      ∀ x : EuclideanSpace ℝ (Fin d), R < ‖x‖ →
        (16 / 3 : ℝ) ≤ ε ^ 2 * (‖gradient U x‖ / ‖x‖) := by
  /- @proof-region region.target-node.session.45482311d74a1a85 begin -/
  intro d U h17 ε hε
  have hε2 : 0 < ε ^ 2 := by positivity
  have hne : ε ^ 2 ≠ 0 := ne_of_gt hε2
  have hmem : {x : EuclideanSpace ℝ (Fin d) | (16 / (3 * ε ^ 2) : ℝ) < ‖gradient U x‖ / ‖x‖} ∈
      Filter.cocompact (EuclideanSpace ℝ (Fin d)) :=
    Filter.eventually_iff.mp (h17.eventually_gt_atTop (16 / (3 * ε ^ 2)))
  obtain ⟨r, hr⟩ :=
    (Metric.mem_cocompact_iff_closedBall_compl_subset (0 : EuclideanSpace ℝ (Fin d))).1 hmem
  refine ⟨max r 1, le_max_right r 1, ?_⟩
  intro x hx
  have hxr : r < ‖x‖ := lt_of_le_of_lt (le_max_left r 1) hx
  have hxK : x ∉ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) r := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact not_le.2 hxr
  have hgt : (16 / (3 * ε ^ 2) : ℝ) < ‖gradient U x‖ / ‖x‖ := hr hxK
  have hmul : ε ^ 2 * (16 / (3 * ε ^ 2)) < ε ^ 2 * (‖gradient U x‖ / ‖x‖) :=
    mul_lt_mul_of_pos_left hgt hε2
  have hval : ε ^ 2 * (16 / (3 * ε ^ 2)) = 16 / 3 := by
    field_simp
  rw [hval] at hmul
  exact le_of_lt hmul
  /- @proof-region region.target-node.session.45482311d74a1a85 end -/

end Statlib.Imported

