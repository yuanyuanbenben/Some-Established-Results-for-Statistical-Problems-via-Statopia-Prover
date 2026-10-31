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
theorem statopia_math_node_2986499135_426a7cd5 : ∀ (n : ℕ) (X : Fin n → ℝ) (g q0 : ℝ → ℝ)
    (pj : ℝ) (θstarj : ℝ) (A : Finset (Fin n)),
    paperBlockIntegral g q0 X pj θstarj A =
      ((pj)⁻¹) ^ (A.card) * paperBlockIntegralT g q0 X θstarj A := by
  /- @proof-region region.target-node.session.aeca090ffa2e65b3 begin -/
  intro n X g q0 pj θstarj A
  have hfac : ∀ a b c : ℝ, a / (b * c) = b⁻¹ * (a / c) := by
    intro a b c
    rcases eq_or_ne b 0 with hb | hb
    · subst hb; simp
    · rcases eq_or_ne c 0 with hc | hc
      · subst hc; simp
      · field_simp
  have hpoint : ∀ θ : ℝ, paperNumIntegrand g X pj θstarj A θ
      = (pj)⁻¹ ^ A.card * paperTIntegrand g X θstarj A θ := by
    intro θ
    simp only [paperNumIntegrand, paperTIntegrand, hfac, Finset.prod_mul_distrib,
      Finset.prod_const]
  unfold paperBlockIntegral paperBlockIntegralT
  simp only [hpoint]
  exact MeasureTheory.integral_const_mul _ _
  /- @proof-region region.target-node.session.aeca090ffa2e65b3 end -/

end Statlib.Imported
end
