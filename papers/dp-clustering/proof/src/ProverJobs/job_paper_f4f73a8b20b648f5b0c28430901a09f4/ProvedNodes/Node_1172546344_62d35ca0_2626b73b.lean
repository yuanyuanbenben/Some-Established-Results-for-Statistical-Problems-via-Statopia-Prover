import ProverJobs.job_paper_f4f73a8b20b648f5b0c28430901a09f4.Vocabulary
import ProverJobs.job_paper_f4f73a8b20b648f5b0c28430901a09f4.Base
import ProverJobs.job_paper_f4f73a8b20b648f5b0c28430901a09f4.ProvedNodes.Node_2986499135_426a7cd5_eed1939b

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
theorem statopia_math_node_1172546344_62d35ca0 : ∀ (n : ℕ) (X : Fin n → ℝ) (g q0 : ℝ → ℝ) (pj : ℝ) (hpj : pj ≠ 0)
    (θstarj : ℝ) (C : Finset (Fin n)) (sj : ℕ)
    (P : Finset (Finset (Fin n))) (hP : P ∈ paperTau C sj),
    paperPartWeight C.card P * (∏ A ∈ P, paperBlockIntegral g q0 X pj θstarj A) /
        paperBlockIntegral g q0 X pj θstarj C
      = (paperPartWeight C.card P * (∏ A ∈ P, paperBlockIntegralT g q0 X θstarj A)) *
          (paperBlockIntegralT g q0 X θstarj C)⁻¹ := by
  /- @proof-region region.target-node.session.a8dad61fac090f8b begin -/
  intro n X g q0 pj hpj θstarj C sj P hP
  have hP' := hP
  simp only [paperTau, Finset.mem_filter, Finset.mem_powerset] at hP'
  obtain ⟨_, _, hsubC, hcover, hdisj, _⟩ := hP'
  have hbU : P.biUnion id = C := by
    refine Finset.Subset.antisymm ?_ ?_
    · intro i hi
      rw [Finset.mem_biUnion] at hi
      obtain ⟨A, hA, hiA⟩ := hi
      exact hsubC A hA hiA
    · intro i hi
      obtain ⟨A, hA, hiA⟩ := hcover i hi
      exact Finset.mem_biUnion.mpr ⟨A, hA, by simpa using hiA⟩
  have hsum : ∑ A ∈ P, A.card = C.card := by
    have h := Finset.card_biUnion (s := P) (t := id) (fun x hx y hy hxy => hdisj x hx y hy hxy)
    rw [hbU] at h
    simpa using h.symm
  have hscale : ∀ A : Finset (Fin n),
      paperBlockIntegral g q0 X pj θstarj A
        = (pj⁻¹) ^ A.card * paperBlockIntegralT g q0 X θstarj A :=
    fun A => statopia_math_node_2986499135_426a7cd5 n X g q0 pj θstarj A
  have prodpow : ∀ Q : Finset (Finset (Fin n)),
      (∏ A ∈ Q, (pj⁻¹) ^ A.card) = (pj⁻¹) ^ (∑ A ∈ Q, A.card) := by
    intro Q
    induction Q using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, ← pow_add]
  have hnum : (∏ A ∈ P, paperBlockIntegral g q0 X pj θstarj A)
      = (pj⁻¹) ^ C.card * ∏ A ∈ P, paperBlockIntegralT g q0 X θstarj A := by
    have step : (∏ A ∈ P, paperBlockIntegral g q0 X pj θstarj A)
        = ∏ A ∈ P, ((pj⁻¹) ^ A.card * paperBlockIntegralT g q0 X θstarj A) :=
      Finset.prod_congr rfl (fun A _ => hscale A)
    rw [step, Finset.prod_mul_distrib, prodpow P, hsum]
  rw [hnum, hscale C, div_eq_mul_inv, mul_inv_rev]
  have hxx : (pj⁻¹) ^ C.card * ((pj⁻¹) ^ C.card)⁻¹ = 1 :=
    mul_inv_cancel₀ (pow_ne_zero C.card (inv_ne_zero hpj))
  rw [show paperPartWeight C.card P
        * ((pj⁻¹) ^ C.card * ∏ A ∈ P, paperBlockIntegralT g q0 X θstarj A)
        * ((paperBlockIntegralT g q0 X θstarj C)⁻¹ * ((pj⁻¹) ^ C.card)⁻¹)
      = ((pj⁻¹) ^ C.card * ((pj⁻¹) ^ C.card)⁻¹)
        * (paperPartWeight C.card P * (∏ A ∈ P, paperBlockIntegralT g q0 X θstarj A)
          * (paperBlockIntegralT g q0 X θstarj C)⁻¹) from by ring]
  rw [hxx, one_mul]

  /- @proof-region region.target-node.session.a8dad61fac090f8b end -/

end Statlib.Imported
end
