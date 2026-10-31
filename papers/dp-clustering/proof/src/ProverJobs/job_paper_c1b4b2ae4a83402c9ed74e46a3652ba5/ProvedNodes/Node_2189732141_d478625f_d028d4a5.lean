import ProverJobs.job_paper_c1b4b2ae4a83402c9ed74e46a3652ba5.Vocabulary
import ProverJobs.job_paper_c1b4b2ae4a83402c9ed74e46a3652ba5.Base

open MeasureTheory Filter Topology
open scoped ENNReal
open Statlib.Imported

open MeasureTheory Filter Topology
open scoped ENNReal
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_2189732141_d478625f : ∀ (w : ℕ → ℝ)
    (hw_nonneg : ∀ n, 0 ≤ w n)
    (hw_bdd : ∃ C : ℝ, ∀ n, w n ≤ C)
    (hw_liminf : liminf w atTop = 0),
    ∃ psi : ℕ → ℕ, StrictMono psi ∧ (∀ n, n ≤ psi n) ∧
      Tendsto (fun n => w (psi n)) atTop (nhds 0) := by
  /- @proof-region region.target-node.session.026ccbac31e3a080 begin -/
  intro w hw_nonneg hw_bdd hw_liminf
  have key : ∀ N : ℕ, ∀ ε : ℝ, 0 < ε → ∃ i : ℕ, N ≤ i ∧ w i < ε := by
    intro N ε hε
    by_contra hcon
    push_neg at hcon
    have hge : ∀ᶠ i in atTop, ε ≤ w i := by
      filter_upwards [Filter.Ici_mem_atTop N] with i hi using hcon i hi
    have hcob : IsCoboundedUnder (fun x1 x2 : ℝ => x1 ≥ x2) atTop w := by
      obtain ⟨C, hC⟩ := hw_bdd
      exact Filter.isCoboundedUnder_ge_of_eventually_le atTop (Eventually.of_forall hC)
    have h1 : ε ≤ liminf w atTop := le_liminf_of_le hcob hge
    rw [hw_liminf] at h1
    linarith
  choose g hg using fun (N k : ℕ) => key N (1 / ((k : ℝ) + 1)) (by positivity)
  let psi : ℕ → ℕ := fun n => Nat.rec (g 0 0) (fun k prev => g (prev + 1) (Nat.succ k)) n
  have psi_zero : psi 0 = g 0 0 := rfl
  have psi_succ : ∀ n : ℕ, psi (Nat.succ n) = g (psi n + 1) (Nat.succ n) := fun n => rfl
  have psi_lt : ∀ n : ℕ, psi n < psi (Nat.succ n) := by
    intro n
    rw [psi_succ n]
    exact Nat.lt_of_succ_le (hg (psi n + 1) (Nat.succ n)).1
  have psi_ge : ∀ n : ℕ, n ≤ psi n := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih =>
        rw [psi_succ n]
        exact Nat.le_trans (Nat.succ_le_succ ih) (hg (psi n + 1) (Nat.succ n)).1
  have hbound : ∀ n : ℕ, w (psi n) < 1 / ((n : ℝ) + 1) := by
    intro n
    cases n with
    | zero => simpa [psi_zero] using (hg 0 0).2
    | succ k =>
        rw [psi_succ k]
        exact (hg (psi k + 1) (Nat.succ k)).2
  have hstrict : StrictMono psi := by
    intro m n hmn
    induction n generalizing m with
    | zero => exact absurd hmn (Nat.not_lt_zero m)
    | succ n ih =>
        rcases lt_or_eq_of_le (Nat.le_of_lt_succ hmn) with h | h
        · exact lt_trans (ih h) (psi_lt n)
        · rw [h]
          exact psi_lt n
  exact ⟨psi, hstrict, psi_ge,
    squeeze_zero (fun n => hw_nonneg (psi n)) (fun n => (hbound n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat⟩
  /- @proof-region region.target-node.session.026ccbac31e3a080 end -/

end Statlib.Imported
