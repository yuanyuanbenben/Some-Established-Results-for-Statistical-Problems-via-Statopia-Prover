import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.Vocabulary
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.Base
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.ProvedNodes.Node_1445702134_3c8d3810_8f7a15fe
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.ProvedNodes.Node_3224678180_5a630a9f_7124eef7


open MeasureTheory
open Statlib.Imported

noncomputable section
open MeasureTheory
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_243881079_7797ad4a : ∀ (t eps delta beta : ℝ) (n s : ℕ)
    (ht : 1 ≤ t)
    (heps : 0 < eps) (heps_lt : eps < 1 / 2)
    (hdelta : 0 < delta) (hdelta_one : 1 ≤ delta)
    (hbeta : 0 < beta)
    (hs : 1 ≤ s)
    (hsn : (s : ℝ) + t ≤ (n : ℝ))
    (hB1 : delta * eps ^ (beta + 1) / (beta + 1) ≤ 1 / 2)
    (hW : max (2 * eps ^ (1 - t))
        ((4 / 3) * ((t + beta + 1) * delta) * eps ^ (-(t + beta))) ≤
      Gconst t eps delta beta * (s : ℝ) / eps ^ s *
        (lowerGamma (t + (s : ℝ) + beta) (eps * Real.log (n : ℝ)) /
          (Real.log ((n : ℝ) / (1 + eps))) ^ s)),
    ∃ R : ℝ,
      eps ≤ R ∧
      R ^ s ≤ Gconst t eps delta beta * (s : ℝ) / eps ^ s *
          (lowerGamma (t + (s : ℝ) + beta) (eps * Real.log (n : ℝ)) /
            (Real.log ((n : ℝ) / (1 + eps))) ^ s) *
            (eps ^ (t + (s : ℝ) - 1) / 2) ∧
      R / risingFac R n ≤
        (3 / 4) * (Gconst t eps delta beta * (s : ℝ) / eps ^ s *
          (lowerGamma (t + (s : ℝ) + beta) (eps * Real.log (n : ℝ)) /
            (Real.log ((n : ℝ) / (1 + eps))) ^ s)) *
          (delta⁻¹ * eps ^ (t + beta + 1) /
            ((t + beta + 1) * risingFac eps n)) := by
  /- @proof-region region.target-node.session.4e0e11da2045b51d begin -/
  intro t eps delta beta n s ht heps heps_lt hdelta hdelta_one hbeta hs hsn hB1 hW
  have heps_ne : eps ≠ 0 := ne_of_gt heps
  have hX_pos : 0 < t + beta + 1 := by linarith
  have hX_ne : t + beta + 1 ≠ 0 := ne_of_gt hX_pos
  have hdelta_ne : delta ≠ 0 := ne_of_gt hdelta
  have hR_pos : 0 < risingFac eps n := (statopia_math_node_1445702134_3c8d3810).1 eps n heps
  have hR_ne : risingFac eps n ≠ 0 := ne_of_gt hR_pos
  have hXR_ne : (t + beta + 1) * risingFac eps n ≠ 0 := mul_ne_zero hX_ne hR_ne
  have hd_inv : delta * delta⁻¹ = 1 := mul_inv_cancel₀ hdelta_ne
  have hpow1 : eps ^ (-(t + beta)) * eps ^ (t + beta + 1) = eps := by
    rw [← Real.rpow_add heps]
    rw [show -(t + beta) + (t + beta + 1) = 1 by ring, Real.rpow_one]
  have hpow2 : eps ^ (1 - t) * eps ^ (t + (s : ℝ) - 1) = eps ^ s := by
    rw [← Real.rpow_add heps]
    rw [show 1 - t + (t + (s : ℝ) - 1) = (s : ℝ) by ring]
    exact Real.rpow_natCast eps s
  refine ⟨eps, le_refl eps, ?_, ?_⟩
  · have hW1 := le_trans (le_max_left _ _) hW
    have hb_pos : 0 < eps ^ (t + (s : ℝ) - 1) := Real.rpow_pos_of_pos heps _
    have h1 := mul_le_mul_of_nonneg_right hW1
      (show (0 : ℝ) ≤ eps ^ (t + (s : ℝ) - 1) / 2 by linarith)
    have heq : 2 * eps ^ (1 - t) * (eps ^ (t + (s : ℝ) - 1) / 2) = eps ^ s := by
      rw [show 2 * eps ^ (1 - t) * (eps ^ (t + (s : ℝ) - 1) / 2)
          = eps ^ (1 - t) * eps ^ (t + (s : ℝ) - 1) by ring]
      exact hpow2
    rwa [heq] at h1
  · have hW2 := le_trans (le_max_right _ _) hW
    have key : (t + beta + 1) * eps ≤
        (3 / 4) *
          (Gconst t eps delta beta * (s : ℝ) / eps ^ s *
            (lowerGamma (t + (s : ℝ) + beta) (eps * Real.log (n : ℝ)) /
              (Real.log ((n : ℝ) / (1 + eps))) ^ s)) *
          (delta⁻¹ * eps ^ (t + beta + 1)) := by
      have hstep : (t + beta + 1) * delta * eps ^ (-(t + beta)) ≤
          (3 / 4) *
            (Gconst t eps delta beta * (s : ℝ) / eps ^ s *
              (lowerGamma (t + (s : ℝ) + beta) (eps * Real.log (n : ℝ)) /
                (Real.log ((n : ℝ) / (1 + eps))) ^ s)) := by
        nlinarith [hW2]
      have hfacZ : 0 ≤ delta⁻¹ * eps ^ (t + beta + 1) :=
        le_of_lt (mul_pos (inv_pos.mpr hdelta) (Real.rpow_pos_of_pos heps _))
      have h4 := mul_le_mul_of_nonneg_right hstep hfacZ
      have e : (t + beta + 1) * delta * eps ^ (-(t + beta)) *
            (delta⁻¹ * eps ^ (t + beta + 1)) = (t + beta + 1) * eps := by
        calc (t + beta + 1) * delta * eps ^ (-(t + beta)) *
              (delta⁻¹ * eps ^ (t + beta + 1))
            = (t + beta + 1) * (delta * delta⁻¹) *
                (eps ^ (-(t + beta)) * eps ^ (t + beta + 1)) := by ring
          _ = (t + beta + 1) * eps := by rw [hd_inv, hpow1]; ring
      rw [e] at h4
      exact h4
    have hD : 0 < (t + beta + 1) * risingFac eps n := mul_pos hX_pos hR_pos
    have hleft : eps / risingFac eps n =
        (t + beta + 1) * eps / ((t + beta + 1) * risingFac eps n) := by
      field_simp
    rw [hleft]
    refine le_of_le_of_eq
      (mul_le_mul_of_nonneg_right key
        (show (0 : ℝ) ≤ ((t + beta + 1) * risingFac eps n)⁻¹ by positivity)) ?_
    rw [div_eq_mul_inv]
    ring
  /- @proof-region region.target-node.session.4e0e11da2045b51d end -/

end Statlib.Imported
end
