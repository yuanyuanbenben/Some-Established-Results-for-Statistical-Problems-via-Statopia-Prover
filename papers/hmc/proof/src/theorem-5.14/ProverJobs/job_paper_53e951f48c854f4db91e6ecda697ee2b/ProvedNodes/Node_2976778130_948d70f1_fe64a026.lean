import ProverJobs.job_paper_53e951f48c854f4db91e6ecda697ee2b.Vocabulary
import ProverJobs.job_paper_53e951f48c854f4db91e6ecda697ee2b.Base
import ProverJobs.job_paper_53e951f48c854f4db91e6ecda697ee2b.ProvedNodes.Node_204287509_2babc882_a5b3181d
import ProverJobs.job_paper_53e951f48c854f4db91e6ecda697ee2b.ProvedNodes.Node_2675730550_7175d3dc_90a64f7e
import ProverJobs.job_paper_53e951f48c854f4db91e6ecda697ee2b.ExternalNodes.Node_f4a8bb342d0a4233af1c

namespace PaperProofTasks.job_paper_53e951f48c854f4db91e6ecda697ee2b



open Filter Topology MeasureTheory
open scoped Topology ENNReal
open _root_.PaperProofTasks.job_paper_53e951f48c854f4db91e6ecda697ee2b.Statlib.Imported

noncomputable section
open Filter Topology MeasureTheory
open scoped Topology ENNReal
namespace Statlib.Imported


set_option autoImplicit false in
theorem statopia_math_node_2976778130_948d70f1 : ∀ (d : ℕ) (U : HMCState d → ℝ)
    (ε : ℝ) (hε : 0 < ε) (L : ℕ) (hL : 1 ≤ L)
    (h17 : ∀ M : ℝ, ∃ R : ℝ, ∀ x : HMCState d, R ≤ ‖x‖ → M ≤ ‖gradient U x‖ / ‖x‖)
    (δ : ℝ) (hδ : δ < 1),
    ∃ R : ℝ, ∀ x0 : HMCState d, R ≤ ‖x0‖ → ∀ p0 : HMCState d, ‖p0‖ ≤ ‖x0‖ ^ δ →
      (1 / 2) * ‖p0‖ ^ 2 - (1 / 2) * ‖leapfrogMomentum U ε L x0 p0‖ ^ 2
        ≤ -((1 / 2) * ‖x0‖ ^ 2) := by
  /- @proof-region region.target-node.session.7a13f802a86e686e begin -/
  intro d U ε hε L hL h17 δ hδ
  obtain ⟨R₁, hR₁⟩ := h17 (16 / ε + 8 / (3 * ε ^ 2))
  obtain ⟨Rg, hRg⟩ := statopia_math_node_2675730550_7175d3dc d U ε hε L hL δ hδ h17
  refine ⟨max (max R₁ Rg) 1, ?_⟩
  intro x0 hx0 p0 hp0
  have hR₁x : R₁ ≤ ‖x0‖ :=
    le_trans (le_trans (le_max_left R₁ Rg) (le_max_left (max R₁ Rg) 1)) hx0
  have hRgx : Rg ≤ ‖x0‖ :=
    le_trans (le_trans (le_max_right R₁ Rg) (le_max_left (max R₁ Rg) 1)) hx0
  have h1x : (1 : ℝ) ≤ ‖x0‖ := le_trans (le_max_right (max R₁ Rg) 1) hx0
  obtain ⟨hstep, _, hge, _, _⟩ := hRg x0 hRgx p0 hp0
  have hxL_ge : ‖x0‖ ≤ ‖leapfrogPosition U ε L x0 p0‖ := (hge L le_rfl).1
  have hxL_pos : (0 : ℝ) < ‖leapfrogPosition U ε L x0 p0‖ :=
    lt_of_lt_of_le one_pos (le_trans h1x hxL_ge)
  have hgrad :
      (16 / ε + 8 / (3 * ε ^ 2))
        ≤ ‖gradient U (leapfrogPosition U ε L x0 p0)‖
          / ‖leapfrogPosition U ε L x0 p0‖ :=
    hR₁ _ (le_trans hR₁x hxL_ge)
  have hgradM :
      (16 / ε + 8 / (3 * ε ^ 2)) * ‖leapfrogPosition U ε L x0 p0‖
        ≤ ‖gradient U (leapfrogPosition U ε L x0 p0)‖ :=
    (le_div_iff₀ hxL_pos).mp hgrad
  have hstepL :
      3 * ‖leapfrogPosition U ε (L - 1) x0 p0‖ ≤ ‖leapfrogPosition U ε L x0 p0‖ :=
    hstep L hL le_rfl
  have hprev :
      ‖leapfrogPosition U ε (L - 1) x0 p0‖ ≤ ‖leapfrogPosition U ε L x0 p0‖ / 3 := by
    linarith only [hstepL]
  have hdiff :
      ‖leapfrogPosition U ε L x0 p0 - leapfrogPosition U ε (L - 1) x0 p0‖
        ≤ (4 / 3) * ‖leapfrogPosition U ε L x0 p0‖ := by
    have h :=
      norm_sub_le (leapfrogPosition U ε L x0 p0) (leapfrogPosition U ε (L - 1) x0 p0)
    linarith only [h, hprev]
  obtain ⟨_, _, _, _, _, _, hlast⟩ :=
    statopia_math_node_204287509_2babc882 d U ε hε L hL x0 p0
  have hε2 : (0 : ℝ) < ε / 2 := by linarith only [hε]
  have hεinv : (0 : ℝ) < 1 / ε := by positivity
  have hterm1 :
      (ε / 2) * (16 / ε + 8 / (3 * ε ^ 2)) * ‖leapfrogPosition U ε L x0 p0‖
        ≤ (ε / 2) * ‖gradient U (leapfrogPosition U ε L x0 p0)‖ := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hgradM (le_of_lt hε2)
  have hterm2 :
      (1 / ε) * ‖leapfrogPosition U ε L x0 p0 - leapfrogPosition U ε (L - 1) x0 p0‖
        ≤ (1 / ε) * ((4 / 3) * ‖leapfrogPosition U ε L x0 p0‖) :=
    mul_le_mul_of_nonneg_left hdiff (le_of_lt hεinv)
  have hcomb :
      (ε / 2) * (16 / ε + 8 / (3 * ε ^ 2)) * ‖leapfrogPosition U ε L x0 p0‖
          - (1 / ε) * ((4 / 3) * ‖leapfrogPosition U ε L x0 p0‖)
        ≤ ‖leapfrogMomentum U ε L x0 p0‖ := by
    linarith only [hlast, hterm1, hterm2]
  have hc :
      (ε / 2) * (16 / ε + 8 / (3 * ε ^ 2)) - (1 / ε) * (4 / 3) = 8 := by
    have hεne : ε ≠ 0 := ne_of_gt hε
    field_simp
    ring
  have hkey :
      (ε / 2) * (16 / ε + 8 / (3 * ε ^ 2)) * ‖leapfrogPosition U ε L x0 p0‖
          - (1 / ε) * ((4 / 3) * ‖leapfrogPosition U ε L x0 p0‖)
        = 8 * ‖leapfrogPosition U ε L x0 p0‖ := by
    rw [← mul_assoc (1 / ε) (4 / 3) ‖leapfrogPosition U ε L x0 p0‖]
    rw [← sub_mul]
    rw [hc]
  have hpL_ge :
      8 * ‖leapfrogPosition U ε L x0 p0‖ ≤ ‖leapfrogMomentum U ε L x0 p0‖ := by
    rw [← hkey]
    exact hcomb
  have hpL : 8 * ‖x0‖ ≤ ‖leapfrogMomentum U ε L x0 p0‖ := by
    linarith only [hpL_ge, hxL_ge]
  have hp0x : ‖p0‖ ≤ ‖x0‖ :=
    calc
      ‖p0‖ ≤ ‖x0‖ ^ δ := hp0
      _ ≤ ‖x0‖ ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1x hδ.le
      _ = ‖x0‖ := Real.rpow_one ‖x0‖
  have hp0sq : ‖p0‖ ^ 2 ≤ ‖x0‖ ^ 2 := by
    have h := mul_le_mul hp0x hp0x (norm_nonneg p0) (norm_nonneg x0)
    nlinarith only [h]
  have hpLsq :
      (32 : ℝ) * ‖x0‖ ^ 2 ≤ (1 / 2) * ‖leapfrogMomentum U ε L x0 p0‖ ^ 2 := by
    have h8 : (0 : ℝ) ≤ 8 * ‖x0‖ := by positivity
    have hn : (0 : ℝ) ≤ ‖leapfrogMomentum U ε L x0 p0‖ := norm_nonneg _
    have h := mul_le_mul hpL hpL h8 hn
    nlinarith only [h]
  nlinarith only [hp0sq, hpLsq, sq_nonneg ‖x0‖]
  /- @proof-region region.target-node.session.7a13f802a86e686e end -/

end Statlib.Imported
end

