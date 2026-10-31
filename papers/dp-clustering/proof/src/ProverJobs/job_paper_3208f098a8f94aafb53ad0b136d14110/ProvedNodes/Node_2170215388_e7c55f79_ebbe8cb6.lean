import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.Vocabulary
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.Base
import ProverJobs.job_paper_3208f098a8f94aafb53ad0b136d14110.ProvedNodes.Node_1445702134_3c8d3810_8f7a15fe

open MeasureTheory
open Statlib.Imported

noncomputable section
open MeasureTheory
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_2170215388_e7c55f79 : ∀ (eps : ℝ) (n : ℕ) (heps_pos : 0 < eps)
    (heps_lt_one : eps < 1) (h2n : 2 ≤ n),
    MonotoneOn
      (fun t : ℝ => Real.exp (-(Real.log ((n : ℝ) / (1 + eps)) * t)) * risingFac t n / t)
      (Set.Ioo (0 : ℝ) eps) := by
  /- @proof-region region.target-node.session.9cf14e8a4f9eda17 begin -/
  intro eps n heps_pos heps_lt_one hn
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1eps : (0 : ℝ) < 1 + eps := by linarith
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have hnl : 1 ≤ n := by omega
  have hn_eq : n = (n - 1) + 1 := (Nat.sub_add_cancel hnl).symm
  intro x hx y hy hxy
  obtain ⟨hx0, hxeps⟩ := hx
  obtain ⟨hy0, hyeps⟩ := hy
  set L : ℝ := Real.log ((n : ℝ) / (1 + eps)) with hL
  set P : ℝ → ℝ := fun t => ∏ k ∈ Finset.range (n - 1), (t + ((k : ℝ) + 1)) with hP
  set S : ℝ → ℝ := fun t => ∑ k ∈ Finset.range (n - 1), Real.log (t + ((k : ℝ) + 1)) with hS
  have hfac : ∀ t : ℝ, t ≠ 0 → risingFac t n / t = P t := by
    intro t ht
    have hP' : P t = ∏ k ∈ Finset.range (n - 1), (t + ((k : ℝ) + 1)) := by
      rw [hP]
    have hprod : (∏ k ∈ Finset.range (n - 1), (t + (((k + 1 : ℕ)) : ℝ)))
        = ∏ k ∈ Finset.range (n - 1), (t + ((k : ℝ) + 1)) := by
      apply Finset.prod_congr rfl
      intro k _
      push_cast
      ring
    have h2 : risingFac t n = t * ∏ k ∈ Finset.range (n - 1), (t + (((k + 1 : ℕ)) : ℝ)) := by
      unfold risingFac
      conv_lhs => rw [hn_eq]
      rw [Finset.prod_range_succ']
      simp only [Nat.cast_zero, add_zero]
      ring
    have h3 : risingFac t n = t * P t := by
      rw [h2, hprod, ← hP']
    rw [h3]
    field_simp
  have hexpP : ∀ t : ℝ, 0 < t → Real.exp (-(L * t)) * P t = Real.exp (-(L * t) + S t) := by
    intro t ht
    simp only [hP, hS]
    rw [Real.exp_add, Real.exp_sum]
    congr 1
    apply Finset.prod_congr rfl
    intro k _
    rw [Real.exp_log]
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hterm : ∀ k ∈ Finset.range (n - 1), (y - x) * (1 / (y + ((k : ℝ) + 1)))
      ≤ Real.log (y + ((k : ℝ) + 1)) - Real.log (x + ((k : ℝ) + 1)) := by
    intro k _
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hxj : (0 : ℝ) < x + ((k : ℝ) + 1) := by linarith
    have hyj : (0 : ℝ) < y + ((k : ℝ) + 1) := by linarith
    have hxjn : x + ((k : ℝ) + 1) ≠ 0 := hxj.ne'
    have hyjn : y + ((k : ℝ) + 1) ≠ 0 := hyj.ne'
    have hratio : (0 : ℝ) < (x + ((k : ℝ) + 1)) / (y + ((k : ℝ) + 1)) := div_pos hxj hyj
    have hbound : Real.log ((x + ((k : ℝ) + 1)) / (y + ((k : ℝ) + 1)))
        ≤ (x + ((k : ℝ) + 1)) / (y + ((k : ℝ) + 1)) - 1 := Real.log_le_sub_one_of_pos hratio
    have hlogdiv : Real.log ((x + ((k : ℝ) + 1)) / (y + ((k : ℝ) + 1)))
        = Real.log (x + ((k : ℝ) + 1)) - Real.log (y + ((k : ℝ) + 1)) :=
      Real.log_div hxjn hyjn
    have hone : (x + ((k : ℝ) + 1)) / (y + ((k : ℝ) + 1)) - 1
        = -((y - x) / (y + ((k : ℝ) + 1))) := by
      field_simp
      ring
    have hlast : (y - x) * (1 / (y + ((k : ℝ) + 1))) = (y - x) / (y + ((k : ℝ) + 1)) := by
      rw [mul_one_div]
    linarith
  have hterm_log : ∀ k ∈ Finset.range (n - 1),
      Real.log (eps + ((k : ℝ) + 1) + 1) - Real.log (eps + ((k : ℝ) + 1))
        ≤ 1 / (eps + ((k : ℝ) + 1)) := by
    intro k _
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have h1 : (0 : ℝ) < eps + ((k : ℝ) + 1) := by linarith
    have h2 : (0 : ℝ) < eps + ((k : ℝ) + 1) + 1 := by linarith
    have h1n : eps + ((k : ℝ) + 1) ≠ 0 := h1.ne'
    have h2n : eps + ((k : ℝ) + 1) + 1 ≠ 0 := h2.ne'
    have hratio : (0 : ℝ) < (eps + ((k : ℝ) + 1) + 1) / (eps + ((k : ℝ) + 1)) := div_pos h2 h1
    have hbound : Real.log ((eps + ((k : ℝ) + 1) + 1) / (eps + ((k : ℝ) + 1)))
        ≤ (eps + ((k : ℝ) + 1) + 1) / (eps + ((k : ℝ) + 1)) - 1 :=
      Real.log_le_sub_one_of_pos hratio
    have hlogdiv : Real.log ((eps + ((k : ℝ) + 1) + 1) / (eps + ((k : ℝ) + 1)))
        = Real.log (eps + ((k : ℝ) + 1) + 1) - Real.log (eps + ((k : ℝ) + 1)) :=
      Real.log_div h2n h1n
    have hone : (eps + ((k : ℝ) + 1) + 1) / (eps + ((k : ℝ) + 1)) - 1
        = 1 / (eps + ((k : ℝ) + 1)) := by
      field_simp
      ring
    linarith
  have hsumtel : ∑ k ∈ Finset.range (n - 1),
      (Real.log (eps + ((k : ℝ) + 1) + 1) - Real.log (eps + ((k : ℝ) + 1)))
      = Real.log (eps + (n : ℝ)) - Real.log (eps + 1) := by
    have h := Finset.sum_range_sub (fun k : ℕ => Real.log (eps + ((k : ℝ) + 1))) (n - 1)
    push_cast at h
    have hcast : ((n : ℝ)) = ((n - 1 : ℕ) : ℝ) + 1 := by
      exact_mod_cast hn_eq
    rw [hcast]
    simpa only [add_assoc, zero_add] using h
  have hLle : L ≤ ∑ k ∈ Finset.range (n - 1), 1 / (eps + ((k : ℝ) + 1)) := by
    have hsum_le : ∑ k ∈ Finset.range (n - 1),
        (Real.log (eps + ((k : ℝ) + 1) + 1) - Real.log (eps + ((k : ℝ) + 1)))
        ≤ ∑ k ∈ Finset.range (n - 1), 1 / (eps + ((k : ℝ) + 1)) := Finset.sum_le_sum hterm_log
    have hlog_n : Real.log (n : ℝ) ≤ Real.log (eps + (n : ℝ)) :=
      Real.log_le_log hn_pos (by linarith)
    have hLsplit : L = Real.log (n : ℝ) - Real.log (1 + eps) := by
      rw [hL]
      exact Real.log_div hn_pos.ne' h1eps.ne'
    have h12 : Real.log (eps + 1) = Real.log (1 + eps) := by
      rw [show eps + 1 = 1 + eps by ring]
    linarith
  have hsum2 : ∑ k ∈ Finset.range (n - 1), 1 / (eps + ((k : ℝ) + 1))
      ≤ ∑ k ∈ Finset.range (n - 1), 1 / (y + ((k : ℝ) + 1)) := by
    apply Finset.sum_le_sum
    intro k _
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hpos : (0 : ℝ) < y + ((k : ℝ) + 1) := by linarith
    exact one_div_le_one_div_of_le hpos (by linarith)
  have hsumLower : L ≤ ∑ k ∈ Finset.range (n - 1), 1 / (y + ((k : ℝ) + 1)) :=
    le_trans hLle hsum2
  have hstepB : (y - x) * L ≤ ∑ k ∈ Finset.range (n - 1), (y - x) * (1 / (y + ((k : ℝ) + 1))) := by
    have h1 : (y - x) * L ≤ (y - x) * (∑ k ∈ Finset.range (n - 1), 1 / (y + ((k : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left hsumLower (by linarith)
    rwa [Finset.mul_sum] at h1
  have hSdiff : S y - S x = ∑ k ∈ Finset.range (n - 1),
      (Real.log (y + ((k : ℝ) + 1)) - Real.log (x + ((k : ℝ) + 1))) := by
    simp only [hS]
    rw [Finset.sum_sub_distrib]
  have hgoal_main : L * (y - x) ≤ S y - S x := by
    rw [hSdiff]
    calc L * (y - x) = (y - x) * L := by ring
      _ ≤ ∑ k ∈ Finset.range (n - 1), (y - x) * (1 / (y + ((k : ℝ) + 1))) := hstepB
      _ ≤ ∑ k ∈ Finset.range (n - 1),
            (Real.log (y + ((k : ℝ) + 1)) - Real.log (x + ((k : ℝ) + 1))) :=
          Finset.sum_le_sum hterm
  have hsub : L * (y - x) = L * y - L * x := by ring
  calc Real.exp (-(L * x)) * risingFac x n / x
      = Real.exp (-(L * x)) * (risingFac x n / x) := by rw [mul_div_assoc]
    _ = Real.exp (-(L * x)) * P x := by rw [hfac x hx0.ne']
    _ = Real.exp (-(L * x) + S x) := hexpP x hx0
    _ ≤ Real.exp (-(L * y) + S y) := by
        apply Real.exp_le_exp.mpr
        linarith [hgoal_main, hsub]
    _ = Real.exp (-(L * y)) * P y := (hexpP y hy0).symm
    _ = Real.exp (-(L * y)) * (risingFac y n / y) := by rw [hfac y hy0.ne']
    _ = Real.exp (-(L * y)) * risingFac y n / y := by rw [mul_div_assoc]
  /- @proof-region region.target-node.session.9cf14e8a4f9eda17 end -/

end Statlib.Imported
end
