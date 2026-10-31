import ProverJobs.job_paper_a62240be95074e8caf07c24daf22159a.ExternalNodes.Node_567cc40dd9e547558ab9
import ProverJobs.job_paper_a62240be95074e8caf07c24daf22159a.Vocabulary
import ProverJobs.job_paper_a62240be95074e8caf07c24daf22159a.ProvedNodes
import ProverJobs.job_paper_a62240be95074e8caf07c24daf22159a.Base

namespace PaperProofTasks.job_paper_a62240be95074e8caf07c24daf22159a

namespace Statlib.Imported


theorem paper_a62240be95074e8caf07c24daf22159a (d : ℕ)
    (U : EuclideanSpace ℝ (Fin d) → ℝ) (hU : Differentiable ℝ U)
    (h17 : Filter.Tendsto (fun x : EuclideanSpace ℝ (Fin d) => ‖gradient U x‖ / ‖x‖)
      (Filter.cocompact (EuclideanSpace ℝ (Fin d))) Filter.atTop)
    (ε : ℝ) (hε : 0 < ε) (L : ℕ) (hL : 1 ≤ L) (δ : ℝ) (hδ : δ < 1) :
    ∃ η : ℝ, ∀ x0 : EuclideanSpace ℝ (Fin d), η < ‖x0‖ →
      ∀ p0 : EuclideanSpace ℝ (Fin d), ‖p0‖ ≤ ‖x0‖ ^ δ →
        (∀ i ∈ Finset.Icc 1 L,
          (3 : ℝ) * ‖leapfrogPos U ε x0 p0 (i - 1)‖ ≤ ‖leapfrogPos U ε x0 p0 i‖) ∧
        (3 : ℝ) ^ L * ‖x0‖ ≤ ‖leapfrogPos U ε x0 p0 L‖
:= by
  /- @proof-region region.root.51717bf6e12d begin -/
  rcases Nat.eq_zero_or_pos d with hd0 | hd
  · subst hd0
    refine ⟨0, ?_⟩
    intro x0 hx p0 hp
    have hnorm : ‖x0‖ = 0 := by
      rw [norm_eq_zero]
      exact Subsingleton.elim x0 0
    rw [hnorm] at hx
    exact absurd hx (lt_irrefl (0 : ℝ))
  · obtain ⟨R, hR1, hRgrad⟩ := statopia_math_node_3826631765_1f99c1c7 d U h17 ε hε
    obtain ⟨η15, hη15⟩ :=
      PaperProofTasks.job_paper_b7909512ace54739b0ef8eae60aa82ed.Statlib.Imported.paper_b7909512ace54739b0ef8eae60aa82ed
        d hd U hU h17 ε hε δ hδ
    refine ⟨max R η15, ?_⟩
    intro x0 hx p0 hp
    refine statopia_math_node_1508296774_c3a2de09 d U ε hε δ hδ L hL R hR1 hRgrad η15 ?_ x0 hx p0 hp
    intro x1 hx1 p1 hp1
    simpa only [leapfrogPos] using hη15 x1 hx1 p1 hp1
  /- @proof-region region.root.51717bf6e12d end -/

end Statlib.Imported

