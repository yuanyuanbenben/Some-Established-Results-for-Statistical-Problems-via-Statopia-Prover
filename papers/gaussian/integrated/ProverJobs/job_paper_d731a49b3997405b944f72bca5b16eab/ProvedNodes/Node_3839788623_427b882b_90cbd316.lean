import ProverJobs.job_paper_d731a49b3997405b944f72bca5b16eab.Vocabulary
import ProverJobs.job_paper_d731a49b3997405b944f72bca5b16eab.Base

namespace PaperProofTasks.job_paper_d731a49b3997405b944f72bca5b16eab

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open _root_.PaperProofTasks.job_paper_d731a49b3997405b944f72bca5b16eab.Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace Statlib.Imported
open _root_.Statlib

set_option autoImplicit false in
theorem statopia_math_node_3839788623_427b882b : ∀ (eps0 : ℝ) (h_eps0_pos : 0 < eps0) (h_eps0_lt_one : eps0 < 1),
    ∃ c0 : ℝ, 0 < c0 ∧
      ∀ x : ℝ, 0 ≤ x → x ≤ 1 - eps0 →
        Real.log (1 / (1 - (2 / Real.pi) * Real.arcsin x)) ≤ c0 * x := by
  /- @proof-region region.target-node.session.fd3e209402162f48 begin -/
  intro eps0 hpos hlt
  refine ⟨1 / eps0, by positivity, ?_⟩
  intro x hx0 hxle
  have hx1 : x ≤ 1 := by linarith
  set t : ℝ := 2 / Real.pi * Real.arcsin x with ht
  have harc_nonneg : 0 ≤ Real.arcsin x := Real.arcsin_nonneg.mpr hx0
  have harc_le : Real.arcsin x ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two x
  have hsin : Real.sin (Real.arcsin x) = x := Real.sin_arcsin (by linarith) hx1
  have hmul : 2 / Real.pi * Real.arcsin x ≤ x := by
    have h := Real.mul_le_sin harc_nonneg harc_le
    rwa [hsin] at h
  have htx : t ≤ x := by
    rw [ht]
    exact hmul
  have ht_le : t ≤ 1 - eps0 := le_trans htx hxle
  have hden : 0 < 1 - t := by linarith
  have hden_ge : eps0 ≤ 1 - t := by linarith
  have h_inv : 1 / (1 - t) ≤ 1 / eps0 := one_div_le_one_div_of_le hpos hden_ge
  have hfin : t / (1 - t) ≤ (1 / eps0) * x := by
    have hmain : t * (1 / (1 - t)) ≤ x * (1 / eps0) :=
      mul_le_mul htx h_inv (by positivity) hx0
    calc t / (1 - t) = t * (1 / (1 - t)) := by ring
      _ ≤ x * (1 / eps0) := hmain
      _ = (1 / eps0) * x := by ring
  calc Real.log (1 / (1 - t)) ≤ 1 / (1 - t) - 1 := Real.log_le_sub_one_of_pos (by positivity)
    _ = t / (1 - t) := by
          have hne : (1 : ℝ) - t ≠ 0 := ne_of_gt hden
          field_simp
          ring
    _ ≤ (1 / eps0) * x := hfin
  /- @proof-region region.target-node.session.fd3e209402162f48 end -/

end Statlib.Imported

