import ProverJobs.job_paper_f4f73a8b20b648f5b0c28430901a09f4.Vocabulary
import ProverJobs.job_paper_f4f73a8b20b648f5b0c28430901a09f4.Base

open MeasureTheory
open scoped BigOperators
open Classical
open Statlib.Imported

open MeasureTheory
open scoped BigOperators
open Classical
noncomputable section
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_2993697126_ef5aa026 : ∀ (t n : ℕ) (ht : t ≠ 0) (hn : 0 < n)
    (K : ℝ) (hK : 0 < K) (S T : Fin t → ℝ)
    (hS_nonneg : ∀ j : Fin t, 0 ≤ S j)
    (hS_le : ∀ j : Fin t, S j ≤
      (2 * (Real.log (n : ℝ)) ^ ((1 : ℝ) / (2 * (t : ℝ))) /
        K ^ ((1 : ℝ) / (t : ℝ))) * T j),
    ∏ j : Fin t, S j ≤
      ((2 : ℝ) ^ t * Real.sqrt (Real.log (n : ℝ)) / K) * ∏ j : Fin t, T j := by
  /- @proof-region region.target-node.session.97d498568fb49052 begin -/
  intro t n ht hn K hK S T hS_nonneg hS_le
  have htR : (t : ℝ) ≠ 0 := by exact_mod_cast ht
  have hlog0 : (0 : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  have hnum : ((Real.log (n : ℝ)) ^ ((1 : ℝ) / (2 * (t : ℝ)))) ^ t
      = Real.sqrt (Real.log (n : ℝ)) := by
    rw [← Real.rpow_mul_natCast hlog0 ((1 : ℝ) / (2 * (t : ℝ))) t]
    have h2 : (1 : ℝ) / (2 * (t : ℝ)) * (t : ℝ) = 1 / 2 := by
      field_simp
    rw [h2, Real.sqrt_eq_rpow]
  have hden : (K ^ ((1 : ℝ) / (t : ℝ))) ^ t = K := by
    rw [← Real.rpow_mul_natCast (le_of_lt hK) ((1 : ℝ) / (t : ℝ)) t]
    have h1 : (1 : ℝ) / (t : ℝ) * (t : ℝ) = 1 := by
      field_simp
    rw [h1, Real.rpow_one]
  have hct : (2 * (Real.log (n : ℝ)) ^ ((1 : ℝ) / (2 * (t : ℝ))) /
        K ^ ((1 : ℝ) / (t : ℝ))) ^ t
      = (2 : ℝ) ^ t * Real.sqrt (Real.log (n : ℝ)) / K := by
    rw [div_pow, mul_pow, hnum, hden]
  have hstep : ∏ j : Fin t, S j ≤
      ∏ j : Fin t, (2 * (Real.log (n : ℝ)) ^ ((1 : ℝ) / (2 * (t : ℝ))) /
        K ^ ((1 : ℝ) / (t : ℝ))) * T j :=
    Finset.prod_le_prod (fun j _ => hS_nonneg j) (fun j _ => hS_le j)
  have hprod : ∏ j : Fin t, (2 * (Real.log (n : ℝ)) ^ ((1 : ℝ) / (2 * (t : ℝ))) /
        K ^ ((1 : ℝ) / (t : ℝ))) * T j
      = (2 * (Real.log (n : ℝ)) ^ ((1 : ℝ) / (2 * (t : ℝ))) /
        K ^ ((1 : ℝ) / (t : ℝ))) ^ t * ∏ j : Fin t, T j := by
    rw [Finset.prod_mul_distrib, Finset.prod_const]
    simp
  calc ∏ j : Fin t, S j
      ≤ ∏ j : Fin t, (2 * (Real.log (n : ℝ)) ^ ((1 : ℝ) / (2 * (t : ℝ))) /
          K ^ ((1 : ℝ) / (t : ℝ))) * T j := hstep
    _ = (2 * (Real.log (n : ℝ)) ^ ((1 : ℝ) / (2 * (t : ℝ))) /
          K ^ ((1 : ℝ) / (t : ℝ))) ^ t * ∏ j : Fin t, T j := hprod
    _ = (2 : ℝ) ^ t * Real.sqrt (Real.log (n : ℝ)) / K * ∏ j : Fin t, T j := by
        rw [hct]
  /- @proof-region region.target-node.session.97d498568fb49052 end -/

end Statlib.Imported
end
