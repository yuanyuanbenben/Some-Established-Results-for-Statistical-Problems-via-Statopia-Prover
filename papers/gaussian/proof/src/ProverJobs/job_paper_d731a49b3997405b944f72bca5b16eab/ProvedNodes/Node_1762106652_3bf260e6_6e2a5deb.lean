import ProverJobs.job_paper_d731a49b3997405b944f72bca5b16eab.Vocabulary
import ProverJobs.job_paper_d731a49b3997405b944f72bca5b16eab.Base
import ProverJobs.job_paper_d731a49b3997405b944f72bca5b16eab.ProvedNodes.Node_3839788623_427b882b_90cbd316

namespace PaperProofTasks.job_paper_d731a49b3997405b944f72bca5b16eab

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open _root_.PaperProofTasks.job_paper_d731a49b3997405b944f72bca5b16eab.Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace Statlib.Imported


set_option autoImplicit false in
theorem statopia_math_node_1762106652_3bf260e6 : ∀ (eps0 : ℝ) (h_eps0_pos : 0 < eps0) (h_eps0_lt_one : eps0 < 1)
    (C : ℝ) (hC : 0 < C),
    ∃ A : ℝ, 0 < A ∧
      ∀ (m : ℕ), 1 ≤ m →
        ∀ S : Fin m → Fin m → ℝ,
          (∀ i j : Fin m, i ≠ j → 0 ≤ S i j ∧ S i j ≤ 1 - eps0) →
          (∑ p ∈ (Finset.univ.filter (fun p : Fin m × Fin m => p.1 < p.2)),
              S p.1 p.2) ≤ C * (m : ℝ) →
          Real.exp
              (∑ i : Fin m, ∑ j ∈ (Finset.univ.filter (fun j : Fin m => i < j)),
                Real.log (1 / (1 - (2 / Real.pi) * Real.arcsin (S i j))) *
                  Real.exp (-((Real.sqrt (Real.log (m : ℝ))) ^ 2) / (1 + S i j)))
            ≤ Real.exp (A * (m : ℝ) ^ (1 - 1 / (2 - eps0))) := by
  /- @proof-region region.target-node.session.63c24adae9a9e87e begin -/
  intro eps0 h_eps0_pos h_eps0_lt_one C hC
  obtain ⟨c0, hc0_pos, hc0⟩ :=
    statopia_math_node_3839788623_427b882b eps0 h_eps0_pos h_eps0_lt_one
  refine ⟨c0 * C, mul_pos hc0_pos hC, ?_⟩
  intro m hm S hS hSum
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hlognn : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hm1
  have htsq : (Real.sqrt (Real.log (m : ℝ))) ^ 2 = Real.log (m : ℝ) :=
    Real.sq_sqrt hlognn
  have h2 : (2 : ℝ) - eps0 ≠ 0 := by linarith
  rw [Real.exp_le_exp]
  set M : ℝ := (m : ℝ) ^ (-(1 / (2 - eps0))) with hMdef
  have hMpos : 0 < M := by
    rw [hMdef]
    exact Real.rpow_pos_of_pos hmpos _
  have hexpM : Real.exp (-(Real.log (m : ℝ)) / (2 - eps0)) = M := by
    rw [hMdef, Real.rpow_def_of_pos hmpos]
    congr 1
    field_simp <;> ring
  have hL : ∀ i j : Fin m, i ≠ j →
      Real.log (1 / (1 - (2 / Real.pi) * Real.arcsin (S i j))) ≤ c0 * S i j := by
    intro i j hij
    exact hc0 (S i j) (hS i j hij).1 (hS i j hij).2
  have hE : ∀ i j : Fin m, i ≠ j →
      Real.exp (-((Real.sqrt (Real.log (m : ℝ))) ^ 2) / (1 + S i j)) ≤ M := by
    intro i j hij
    have hSij := hS i j hij
    have hdenpos : (0 : ℝ) < 1 + S i j := by linarith [hSij.1]
    have hdenle : 1 + S i j ≤ 2 - eps0 := by linarith [hSij.2]
    have h1 : 1 / (2 - eps0) ≤ 1 / (1 + S i j) := one_div_le_one_div_of_le hdenpos hdenle
    have h1' : (2 - eps0)⁻¹ ≤ (1 + S i j)⁻¹ := by
      simpa only [one_div] using h1
    have hdiv : Real.log (m : ℝ) / (2 - eps0) ≤ Real.log (m : ℝ) / (1 + S i j) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left h1' hlognn
    have harg : -((Real.sqrt (Real.log (m : ℝ))) ^ 2) / (1 + S i j) ≤
        -(Real.log (m : ℝ)) / (2 - eps0) := by
      rw [htsq, neg_div, neg_div]
      exact neg_le_neg hdiv
    calc Real.exp (-((Real.sqrt (Real.log (m : ℝ))) ^ 2) / (1 + S i j))
        ≤ Real.exp (-(Real.log (m : ℝ)) / (2 - eps0)) := Real.exp_le_exp.mpr harg
      _ = M := hexpM
  have hprod : ∀ i j : Fin m, i ≠ j →
      Real.log (1 / (1 - (2 / Real.pi) * Real.arcsin (S i j))) *
        Real.exp (-((Real.sqrt (Real.log (m : ℝ))) ^ 2) / (1 + S i j)) ≤ (c0 * S i j) * M := by
    intro i j hij
    have hSij := hS i j hij
    calc Real.log (1 / (1 - (2 / Real.pi) * Real.arcsin (S i j))) *
          Real.exp (-((Real.sqrt (Real.log (m : ℝ))) ^ 2) / (1 + S i j))
        ≤ (c0 * S i j) *
            Real.exp (-((Real.sqrt (Real.log (m : ℝ))) ^ 2) / (1 + S i j)) :=
          mul_le_mul_of_nonneg_right (hL i j hij) (Real.exp_pos _).le
      _ ≤ (c0 * S i j) * M :=
          mul_le_mul_of_nonneg_left (hE i j hij) (mul_nonneg hc0_pos.le hSij.1)
  have hpair_eq :
      (∑ p ∈ (Finset.univ.filter (fun p : Fin m × Fin m => p.1 < p.2)), S p.1 p.2) =
        ∑ i : Fin m, ∑ j ∈ (Finset.univ.filter (fun j : Fin m => i < j)), S i j := by
    simp only [Finset.sum_filter, Fintype.sum_prod_type]
  have hsumS :
      (∑ i : Fin m, ∑ j ∈ (Finset.univ.filter (fun j : Fin m => i < j)), S i j) ≤
        C * (m : ℝ) := by
    rw [← hpair_eq]
    exact hSum
  have hstep1 :
      (∑ i : Fin m, ∑ j ∈ (Finset.univ.filter (fun j : Fin m => i < j)),
          Real.log (1 / (1 - (2 / Real.pi) * Real.arcsin (S i j))) *
            Real.exp (-((Real.sqrt (Real.log (m : ℝ))) ^ 2) / (1 + S i j)))
        ≤ ∑ i : Fin m, ∑ j ∈ (Finset.univ.filter (fun j : Fin m => i < j)), (c0 * S i j) * M := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j hj
    exact hprod i j (ne_of_lt (Finset.mem_filter.mp hj).2)
  have hfactor :
      (∑ i : Fin m, ∑ j ∈ (Finset.univ.filter (fun j : Fin m => i < j)), (c0 * S i j) * M) =
        (c0 * M) * (∑ i : Fin m, ∑ j ∈ (Finset.univ.filter (fun j : Fin m => i < j)), S i j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hfinal :
      (∑ i : Fin m, ∑ j ∈ (Finset.univ.filter (fun j : Fin m => i < j)), (c0 * S i j) * M) ≤
        (c0 * M) * (C * (m : ℝ)) := by
    rw [hfactor]
    exact mul_le_mul_of_nonneg_left hsumS (mul_nonneg hc0_pos.le hMpos.le)
  have hpow : (m : ℝ) ^ (-(1 / (2 - eps0))) * (m : ℝ) =
      (m : ℝ) ^ (1 - 1 / (2 - eps0)) := by
    calc (m : ℝ) ^ (-(1 / (2 - eps0))) * (m : ℝ)
        = (m : ℝ) ^ (-(1 / (2 - eps0))) * (m : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = (m : ℝ) ^ (-(1 / (2 - eps0)) + 1) := (Real.rpow_add hmpos _ _).symm
      _ = (m : ℝ) ^ (1 - 1 / (2 - eps0)) := by
            congr 1
            field_simp
            ring
  have hAeq : (c0 * M) * (C * (m : ℝ)) = (c0 * C) * (m : ℝ) ^ (1 - 1 / (2 - eps0)) := by
    rw [hMdef]
    rw [show (c0 * (m : ℝ) ^ (-(1 / (2 - eps0)))) * (C * (m : ℝ)) =
        (c0 * C) * ((m : ℝ) ^ (-(1 / (2 - eps0))) * (m : ℝ)) by ring]
    rw [hpow]
  calc (∑ i : Fin m, ∑ j ∈ (Finset.univ.filter (fun j : Fin m => i < j)),
        Real.log (1 / (1 - (2 / Real.pi) * Real.arcsin (S i j))) *
          Real.exp (-((Real.sqrt (Real.log (m : ℝ))) ^ 2) / (1 + S i j)))
      ≤ ∑ i : Fin m, ∑ j ∈ (Finset.univ.filter (fun j : Fin m => i < j)), (c0 * S i j) * M := hstep1
    _ ≤ (c0 * M) * (C * (m : ℝ)) := hfinal
    _ = (c0 * C) * (m : ℝ) ^ (1 - 1 / (2 - eps0)) := hAeq
  /- @proof-region region.target-node.session.63c24adae9a9e87e end -/

end Statlib.Imported

