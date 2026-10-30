import ProverJobs.real_main_theorem_d734bdb6a642.Vocabulary
import ProverJobs.real_main_theorem_d734bdb6a642.Base
import ProverJobs.real_main_theorem_d734bdb6a642.ProvedNodes.Node_1648340497_660d8830_976f6e3c
import ProverJobs.real_main_theorem_d734bdb6a642.ProvedNodes.Node_1687727109_97638036_3cee4fac

set_option autoImplicit false in
theorem statopia_math_node_2498287263_10c06cca : ∀ (f : PositiveReal → PositiveReal) (hf : IsAdmissible f)
    (a b : ℝ) (hab_pos : 0 < a) (hab_lt : a < b)
    (u v : PositiveReal)
    (hu_lower : a ≤ (u : ℝ)) (hu_upper : (u : ℝ) ≤ b)
    (hv_lower : a ≤ (v : ℝ)) (hv_upper : (v : ℝ) ≤ b),
    |((f v : ℝ) - (v : ℝ)) - ((f u : ℝ) - (u : ℝ))| ≤
      ((v : ℝ) - (u : ℝ)) ^ 2 / (4 * a) := by
  /- @proof-region region.target-node.session.8a0e89bf6fd5c0bb begin -/
  intro f hf a b hab_pos hab_lt u v hu_lower hu_upper hv_lower hv_upper
  have key : ∀ (p q : PositiveReal), a ≤ (p : ℝ) →
      4 * (f p : ℝ) * (((f q : ℝ) - (q : ℝ)) - ((f p : ℝ) - (p : ℝ))) ≤ ((q : ℝ) - (p : ℝ)) ^ 2 →
      (((f q : ℝ) - (q : ℝ)) - ((f p : ℝ) - (p : ℝ))) ≤ ((q : ℝ) - (p : ℝ)) ^ 2 / (4 * a) := by
    intro p q hp hdisp
    have hfp_ge : a ≤ (f p : ℝ) := le_trans hp (statopia_math_node_1648340497_660d8830 f hf p)
    have ha4 : (0 : ℝ) < 4 * a := by linarith
    by_cases hcase : ((f q : ℝ) - (q : ℝ)) - ((f p : ℝ) - (p : ℝ)) ≤ 0
    · have hQ : (0 : ℝ) ≤ ((q : ℝ) - (p : ℝ)) ^ 2 / (4 * a) :=
        div_nonneg (sq_nonneg _) (le_of_lt ha4)
      linarith
    · push_neg at hcase
      have hmul : a * (((f q : ℝ) - (q : ℝ)) - ((f p : ℝ) - (p : ℝ))) ≤
          (f p : ℝ) * (((f q : ℝ) - (q : ℝ)) - ((f p : ℝ) - (p : ℝ))) :=
        mul_le_mul_of_nonneg_right hfp_ge (le_of_lt hcase)
      have h4 : 4 * a * (((f q : ℝ) - (q : ℝ)) - ((f p : ℝ) - (p : ℝ))) ≤
          ((q : ℝ) - (p : ℝ)) ^ 2 := by
        nlinarith [hdisp, hmul]
      rw [le_div_iff₀ ha4]
      nlinarith [h4]
  have hu_b : (((f v : ℝ) - (v : ℝ)) - ((f u : ℝ) - (u : ℝ))) ≤ ((v : ℝ) - (u : ℝ)) ^ 2 / (4 * a) :=
    key u v hu_lower (statopia_math_node_1687727109_97638036 f hf u v)
  have hv_b : (((f u : ℝ) - (u : ℝ)) - ((f v : ℝ) - (v : ℝ))) ≤ ((v : ℝ) - (u : ℝ)) ^ 2 / (4 * a) := by
    have h := key v u hv_lower (statopia_math_node_1687727109_97638036 f hf v u)
    have hsq : ((u : ℝ) - (v : ℝ)) ^ 2 = ((v : ℝ) - (u : ℝ)) ^ 2 := by ring
    rwa [hsq] at h
  rw [abs_le]
  exact ⟨by linarith, hu_b⟩
  /- @proof-region region.target-node.session.8a0e89bf6fd5c0bb end -/
