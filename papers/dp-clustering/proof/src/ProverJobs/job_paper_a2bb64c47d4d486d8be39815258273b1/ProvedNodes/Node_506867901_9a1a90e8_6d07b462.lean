import ProverJobs.job_paper_a2bb64c47d4d486d8be39815258273b1.Vocabulary
import ProverJobs.job_paper_a2bb64c47d4d486d8be39815258273b1.Base
import ProverJobs.job_paper_a2bb64c47d4d486d8be39815258273b1.ProvedNodes.Node_3719821444_17db7983_6a035bd6

open MeasureTheory
open Classical
open Statlib.Imported

open MeasureTheory
open Classical
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_506867901_9a1a90e8 : ∀ (c : ℝ) (hc : 0 < c) (g : ℝ → ℝ) (R theta_star : ℝ)
    (n : ℕ) (x : Fin n → ℝ) (S : Finset (Fin n)) (hne : S.Nonempty)
    (hwin : ∀ i ∈ S, x i ∈ Set.Icc (theta_star - c) (theta_star + c))
    (hpos : ∀ y ∈ Set.Icc (-c) c, 0 < g y)
    (hlip : ∀ u ∈ Set.Icc (-c) c, ∀ v ∈ Set.Icc (-c) c,
      |Real.log (g u) - Real.log (g v)| ≤ R * |u - v|)
    (theta : ℝ)
    (htheta_lo : (S.image x).max' (hne.image x) - c ≤ theta)
    (htheta_hi : theta ≤ (S.image x).min' (hne.image x) + c)
    (i : Fin n) (hi : i ∈ S),
    Real.exp (-(R * |theta - theta_star|)) ≤ g (x i - theta) / g (x i - theta_star) := by
  /- @proof-region region.target-node.session.1c7d5fee78c73a92 begin -/
  intro c hc g R theta_star n x S hne hwin hpos hlip theta htheta_lo htheta_hi i hi
  have hmem : x i ∈ S.image x := Finset.mem_image.mpr ⟨i, hi, rfl⟩
  have hmax : x i ≤ (S.image x).max' (hne.image x) := Finset.le_max' _ _ hmem
  have hmin : (S.image x).min' (hne.image x) ≤ x i := Finset.min'_le _ _ hmem
  have hu : x i - theta ∈ Set.Icc (-c) c := by
    refine ⟨by linarith, by linarith⟩
  have hv : x i - theta_star ∈ Set.Icc (-c) c := by
    have h2 := hwin i hi
    exact ⟨by linarith [h2.1], by linarith [h2.2]⟩
  have habs : |(x i - theta) - (x i - theta_star)| = |theta - theta_star| := by
    rw [show (x i - theta) - (x i - theta_star) = -(theta - theta_star) by ring, abs_neg]
  have hb := hlip _ hu _ hv
  rw [habs] at hb
  have hstep : -(R * |theta - theta_star|)
      ≤ Real.log (g (x i - theta)) - Real.log (g (x i - theta_star)) := by
    have h1 := neg_abs_le (Real.log (g (x i - theta)) - Real.log (g (x i - theta_star)))
    linarith
  have hposu : 0 < g (x i - theta) := hpos _ hu
  have hposv : 0 < g (x i - theta_star) := hpos _ hv
  calc Real.exp (-(R * |theta - theta_star|))
      ≤ Real.exp (Real.log (g (x i - theta)) - Real.log (g (x i - theta_star))) :=
        Real.exp_le_exp.mpr hstep
    _ = g (x i - theta) / g (x i - theta_star) := by
        rw [Real.exp_sub, Real.exp_log hposu, Real.exp_log hposv]
  /- @proof-region region.target-node.session.1c7d5fee78c73a92 end -/

end Statlib.Imported
