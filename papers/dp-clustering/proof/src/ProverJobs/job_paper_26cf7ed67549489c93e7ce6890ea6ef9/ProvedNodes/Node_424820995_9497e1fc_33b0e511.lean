import ProverJobs.job_paper_26cf7ed67549489c93e7ce6890ea6ef9.Vocabulary
import ProverJobs.job_paper_26cf7ed67549489c93e7ce6890ea6ef9.Base

open scoped BigOperators
open Statlib.Imported

open scoped BigOperators
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_424820995_9497e1fc : ∀ (p : ℝ) (hp : 1 < p),
    Summable (fun m : ℕ => 1 / ((m : ℝ) + 1) ^ p) ∧
    0 < zetaSeries p ∧
    (∀ M : ℕ, 1 ≤ M →
      (∑ m ∈ Finset.range M, 1 / ((m : ℝ) + 1) ^ p) < zetaSeries p) ∧
    (∀ M : ℕ, 1 ≤ M →
      (∑ a ∈ Finset.Icc 1 M, 1 / (a : ℝ) ^ p) < zetaSeries p) := by
  /- @proof-region region.target-node.session.12ed2d3658aa955a begin -/
  intro p hp
  have hg : Summable (fun m : ℕ => 1 / ((m : ℝ) + 1) ^ p) := by
    have h1 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ p) := Real.summable_one_div_nat_rpow.2 hp
    have h2 : Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ)) ^ p) :=
      (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ p) 1).2 h1
    simpa only [Nat.cast_add, Nat.cast_one] using h2
  have hiii : ∀ M : ℕ, 1 ≤ M →
      (∑ m ∈ Finset.range M, 1 / ((m : ℝ) + 1) ^ p) < zetaSeries p := by
    intro M hM
    have hshift : Summable (fun i : ℕ => 1 / (((i + M : ℕ) : ℝ) + 1) ^ p) :=
      (summable_nat_add_iff (f := fun m : ℕ => 1 / ((m : ℝ) + 1) ^ p) M).2 hg
    have hsplit : (∑ m ∈ Finset.range M, 1 / ((m : ℝ) + 1) ^ p) +
        (∑' i : ℕ, 1 / (((i + M : ℕ) : ℝ) + 1) ^ p) = zetaSeries p :=
      Summable.sum_add_tsum_nat_add M hg
    have htail : 0 < ∑' i : ℕ, 1 / (((i + M : ℕ) : ℝ) + 1) ^ p := by
      have h := Summable.tsum_lt_tsum_of_nonneg
        (f := fun _ : ℕ => (0 : ℝ))
        (g := fun i : ℕ => 1 / (((i + M : ℕ) : ℝ) + 1) ^ p)
        (i := 0)
        (fun b => le_refl 0) (fun b => by positivity) (by positivity) hshift
      simpa using h
    linarith
  refine ⟨hg, ?_, hiii, ?_⟩
  · have h1 := hiii 1 le_rfl
    have hsum1 : (∑ m ∈ Finset.range 1, 1 / ((m : ℝ) + 1) ^ p) = 1 := by
      simp
    rw [hsum1] at h1
    linarith
  · intro M hM
    have hIcc : (Finset.range M).image (fun m : ℕ => m + 1) = Finset.Icc 1 M := by
      ext x
      simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Icc]
      constructor
      · rintro ⟨m, hm, rfl⟩
        omega
      · rintro ⟨h1, h2⟩
        exact ⟨x - 1, by omega, by omega⟩
    have hreindex : (∑ a ∈ Finset.Icc 1 M, 1 / (a : ℝ) ^ p) =
        (∑ m ∈ Finset.range M, 1 / ((m : ℝ) + 1) ^ p) := by
      rw [← hIcc]
      have hinj : Set.InjOn (fun m : ℕ => m + 1) ↑(Finset.range M) := by
        intro x _ y _ hxy
        have h : x + 1 = y + 1 := hxy
        omega
      rw [Finset.sum_image hinj]
      simp only [Nat.cast_add, Nat.cast_one]
    rw [hreindex]
    exact hiii M hM
  /- @proof-region region.target-node.session.12ed2d3658aa955a end -/

end Statlib.Imported
