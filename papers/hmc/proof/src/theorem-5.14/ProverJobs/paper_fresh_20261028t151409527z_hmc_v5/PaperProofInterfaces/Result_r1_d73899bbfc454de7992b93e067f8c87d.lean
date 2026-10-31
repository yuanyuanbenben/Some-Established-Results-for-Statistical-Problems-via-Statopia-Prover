import ProverJobs.job_paper_b7909512ace54739b0ef8eae60aa82ed.Vocabulary
import ProverJobs.job_paper_b7909512ace54739b0ef8eae60aa82ed.ProvedNodes
import ProverJobs.job_paper_b7909512ace54739b0ef8eae60aa82ed.Base

namespace PaperProofTasks.job_paper_b7909512ace54739b0ef8eae60aa82ed

namespace Statlib.Imported

open Filter Topology

theorem paper_b7909512ace54739b0ef8eae60aa82ed
    (d : ℕ) (hd : 0 < d)
    (U : EuclideanSpace ℝ (Fin d) → ℝ) (hU : Differentiable ℝ U)
    (hU17 : Tendsto (fun x : EuclideanSpace ℝ (Fin d) => ‖gradient U x‖ / ‖x‖)
      (Filter.cocompact (EuclideanSpace ℝ (Fin d))) Filter.atTop)
    (ε : ℝ) (hε : 0 < ε) (δ : ℝ) (hδ : δ < 1) :
    ∃ η : ℝ, ∀ x0 : EuclideanSpace ℝ (Fin d), η < ‖x0‖ →
      ∀ p0 : EuclideanSpace ℝ (Fin d), ‖p0‖ ≤ ‖x0‖ ^ δ →
        3 * ‖x0‖ < ‖xEps d U ε x0 p0‖
:= by
  /- @proof-region region.root.08600af8e57c begin -/
  have hP : ∀ᶠ x in Filter.cocompact (EuclideanSpace ℝ (Fin d)),
      5 < (ε ^ 2 / 2) * (‖gradient U x‖ / ‖x‖) ∧ ε * ‖x‖ ^ (δ - 1) < 1 :=
    statopia_math_node_120903796_cba0ef30 d hd U hU17 ε hε δ hδ
  obtain ⟨R, hR⟩ :=
    statopia_math_node_3625375570_9c859904 (EuclideanSpace ℝ (Fin d))
      (fun x => 5 < (ε ^ 2 / 2) * (‖gradient U x‖ / ‖x‖) ∧ ε * ‖x‖ ^ (δ - 1) < 1) hP
  refine ⟨max R 0, ?_⟩
  intro x0 hx p0 hp
  have hnpos : 0 < ‖x0‖ := lt_of_le_of_lt (le_max_right R 0) hx
  have hnne : ‖x0‖ ≠ 0 := ne_of_gt hnpos
  have hRle : R ≤ ‖x0‖ := le_trans (le_max_left R 0) hx.le
  have hmain : 5 < (ε ^ 2 / 2) * (‖gradient U x0‖ / ‖x0‖) ∧ ε * ‖x0‖ ^ (δ - 1) < 1 :=
    hR x0 hRle
  obtain ⟨h1, h2⟩ := hmain
  have h1' : 5 * ‖x0‖ < (ε ^ 2 / 2) * ‖gradient U x0‖ := by
    have h := mul_lt_mul_of_pos_right h1 hnpos
    have key : (ε ^ 2 / 2) * (‖gradient U x0‖ / ‖x0‖) * ‖x0‖ = (ε ^ 2 / 2) * ‖gradient U x0‖ := by
      field_simp
    rw [key] at h
    exact h
  have hδeq : ‖x0‖ ^ δ = ‖x0‖ * ‖x0‖ ^ (δ - 1) := by
    calc
      ‖x0‖ ^ δ = ‖x0‖ ^ ((1 : ℝ) + (δ - 1)) := by
        rw [show (1 : ℝ) + (δ - 1) = δ by ring]
      _ = ‖x0‖ ^ (1 : ℝ) * ‖x0‖ ^ (δ - 1) := Real.rpow_add (x := ‖x0‖) hnpos 1 (δ - 1)
      _ = ‖x0‖ * ‖x0‖ ^ (δ - 1) := by rw [Real.rpow_one]
  have hp' : ‖p0‖ ≤ ‖x0‖ * ‖x0‖ ^ (δ - 1) := by
    rw [hδeq] at hp
    exact hp
  have hb_lt : ε * ‖p0‖ < ‖x0‖ :=
    calc ε * ‖p0‖ ≤ ε * (‖x0‖ * ‖x0‖ ^ (δ - 1)) := mul_le_mul_of_nonneg_left hp' hε.le
      _ = (ε * ‖x0‖ ^ (δ - 1)) * ‖x0‖ := by ring
      _ < 1 * ‖x0‖ := mul_lt_mul_of_pos_right h2 hnpos
      _ = ‖x0‖ := one_mul ‖x0‖
  have hlamnn : (0 : ℝ) ≤ ε ^ 2 / 2 := by positivity
  have ha : ‖(ε ^ 2 / 2 : ℝ) • gradient U x0‖ = (ε ^ 2 / 2) * ‖gradient U x0‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hlamnn]
  
  have hb : ‖(ε : ℝ) • p0‖ = ε * ‖p0‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
  have hxE : xEps d U ε x0 p0 = -((ε ^ 2 / 2 : ℝ) • gradient U x0 - (x0 + ε • p0)) := by
    unfold xEps
    abel
  have key : (ε ^ 2 / 2) * ‖gradient U x0‖ - ‖x0‖ - ε * ‖p0‖ ≤ ‖xEps d U ε x0 p0‖ := by
    rw [hxE, norm_neg]
    have htri : ‖x0 + (ε : ℝ) • p0‖ ≤ ‖x0‖ + ε * ‖p0‖ := by
      have h := norm_add_le x0 ((ε : ℝ) • p0)
      rw [hb] at h
      exact h
    have hrev := norm_sub_norm_le ((ε ^ 2 / 2 : ℝ) • gradient U x0) (x0 + (ε : ℝ) • p0)
    rw [ha] at hrev
    linarith
  linarith [key, h1', hb_lt]
  /- @proof-region region.root.08600af8e57c end -/

end Statlib.Imported

