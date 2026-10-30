import ProverJobs.job_paper_53e951f48c854f4db91e6ecda697ee2b.ExternalNodes.Node_f4a8bb342d0a4233af1c
import ProverJobs.job_paper_53e951f48c854f4db91e6ecda697ee2b.Vocabulary
import ProverJobs.job_paper_53e951f48c854f4db91e6ecda697ee2b.ProvedNodes
import ProverJobs.job_paper_53e951f48c854f4db91e6ecda697ee2b.Base

noncomputable section
open Filter Topology MeasureTheory
open scoped Topology ENNReal
namespace Statlib.Imported

theorem paper_53e951f48c854f4db91e6ecda697ee2b (d : ℕ) (U : HMCState d → ℝ)
    (hU_nonneg : ∀ x, 0 ≤ U x) (hU_diff : Differentiable ℝ U)
    (h17 : ∀ M : ℝ, ∃ R : ℝ, ∀ x : HMCState d, R ≤ ‖x‖ → M ≤ ‖gradient U x‖ / ‖x‖)
    (h18 : ∃ C : ℝ, ∀ x y : HMCState d, C ≤ 3 * ‖x‖ → 3 * ‖x‖ ≤ ‖y‖ →
      3 * ‖gradient U x‖ ≤ ‖gradient U y‖)
    (ε : ℝ) (hε : 0 < ε) (L : ℕ) (hL : 1 ≤ L)
    (h19 : ∀ B : ℝ, ∃ R : ℝ, ∀ x y : HMCState d, R ≤ ‖x‖ → (2 : ℝ) ^ L * ‖x‖ ≤ ‖y‖ →
      U x - U y - (1 / 2) * ‖x‖ ^ 2 ≤ B) :
    ∀ δ : ℝ, δ < 1 →
      Tendsto
        (fun x0 : HMCState d =>
          ⨆ p0 : {p : HMCState d // ‖p‖ ≤ ‖x0‖ ^ δ}, hmcAcceptance U ε L x0 p0.val)
        (Filter.cocompact (HMCState d)) (𝓝 0) ∧
      (∀ η : ℝ, 0 < η → ∃ R : ℝ, ∀ x0 : HMCState d, R ≤ ‖x0‖ →
        ∀ p0 : HMCState d, ‖p0‖ ≤ ‖x0‖ ^ δ → hmcAcceptance U ε L x0 p0 ≤ η)
:= by
  /- @proof-region region.root.898ad0387fce begin -/
  intro δ hδ
  obtain ⟨Rg, hgrow⟩ := statopia_math_node_2675730550_7175d3dc d U ε hε L hL δ hδ h17
  obtain ⟨Rk, hdrop⟩ := statopia_math_node_2976778130_948d70f1 d U ε hε L hL h17 δ hδ
  have hcocompact : ∀ R : ℝ, {x : HMCState d | R ≤ ‖x‖} ∈ Filter.cocompact (HMCState d) := by
    intro R
    rw [Filter.mem_cocompact]
    refine ⟨Metric.closedBall 0 R, isCompact_closedBall 0 R, ?_⟩
    intro x hx
    rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right] at hx
    exact le_of_lt (not_le.mp hx)
  have key : ∀ η : ℝ, 0 < η → ∃ R : ℝ, ∀ x0 : HMCState d, R ≤ ‖x0‖ →
      ∀ p0 : HMCState d, ‖p0‖ ≤ ‖x0‖ ^ δ → hmcAcceptance U ε L x0 p0 ≤ η := by
    intro η hη
    by_cases hη1 : (1 : ℝ) ≤ η
    · refine ⟨0, ?_⟩
      intro x0 _ p0 _
      rw [(statopia_math_node_1841802883_50746d93 d U ε L x0 p0).1]
      exact le_trans (min_le_left _ _) hη1
    · obtain ⟨R2, hR2⟩ := h19 (Real.log η)
      refine ⟨max (max Rg Rk) R2, ?_⟩
      intro x0 hx0 p0 hp0
      have hg : Rg ≤ ‖x0‖ :=
        le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx0
      have hk : Rk ≤ ‖x0‖ :=
        le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx0
      have hRt : R2 ≤ ‖x0‖ := le_trans (le_max_right _ _) hx0
      obtain ⟨-, -, -, h3L, h23⟩ := hgrow x0 hg p0 hp0
      have h2L : (2 : ℝ) ^ L * ‖x0‖ ≤ ‖leapfrogPosition U ε L x0 p0‖ := le_trans h23 h3L
      have h19app := hR2 x0 (leapfrogPosition U ε L x0 p0) hRt h2L
      have hdropapp := hdrop x0 hk p0 hp0
      have hE : U x0 - U (leapfrogPosition U ε L x0 p0) + (1 / 2) * ‖p0‖ ^ 2 -
          (1 / 2) * ‖leapfrogMomentum U ε L x0 p0‖ ^ 2 ≤ Real.log η := by linarith
      rw [(statopia_math_node_1841802883_50746d93 d U ε L x0 p0).1]
      have hexp : Real.exp (U x0 - U (leapfrogPosition U ε L x0 p0) + (1 / 2) * ‖p0‖ ^ 2 -
          (1 / 2) * ‖leapfrogMomentum U ε L x0 p0‖ ^ 2) ≤ η := by
        rw [← Real.exp_log hη]
        exact Real.exp_le_exp.mpr hE
      exact le_trans (min_le_right _ _) hexp
  constructor
  · rw [Metric.tendsto_nhds]
    intro e he
    obtain ⟨R, hR⟩ := key (e / 2) (by linarith)
    filter_upwards [hcocompact R] with x0 hx0
    change dist (⨆ p : {p : HMCState d // ‖p‖ ≤ ‖x0‖ ^ δ}, hmcAcceptance U ε L x0 p.val) 0 < e
    haveI : Nonempty {p : HMCState d // ‖p‖ ≤ ‖x0‖ ^ δ} :=
      ⟨⟨0, by simpa using Real.rpow_nonneg (norm_nonneg x0) δ⟩⟩
    have hle : (⨆ p : {p : HMCState d // ‖p‖ ≤ ‖x0‖ ^ δ}, hmcAcceptance U ε L x0 p.val) ≤ e / 2 :=
      ciSup_le (fun p => hR x0 hx0 p.val p.property)
    have hbdd : BddAbove (Set.range (fun p : {p : HMCState d // ‖p‖ ≤ ‖x0‖ ^ δ} =>
        hmcAcceptance U ε L x0 p.val)) :=
      ⟨1, by rintro _ ⟨p, rfl⟩; exact (statopia_math_node_1841802883_50746d93 d U ε L x0 p.val).2.2⟩
    have hnonneg : 0 ≤ (⨆ p : {p : HMCState d // ‖p‖ ≤ ‖x0‖ ^ δ}, hmcAcceptance U ε L x0 p.val) := by
      have hmem0 : ‖(0 : HMCState d)‖ ≤ ‖x0‖ ^ δ := by
        simpa using Real.rpow_nonneg (norm_nonneg x0) δ
      exact le_trans (statopia_math_node_1841802883_50746d93 d U ε L x0 0).2.1
        (le_ciSup hbdd ⟨0, hmem0⟩)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
    linarith
  · exact key
  /- @proof-region region.root.898ad0387fce end -/

end Statlib.Imported
