import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q11.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q11.Base

open MeasureTheory

open MeasureTheory

set_option autoImplicit false in
theorem statopia_math_node_1586279299_522770ce : ∀ (lambda : ℕ → ℝ) (hlambda_nonneg : ∀ k : ℕ, 0 ≤ lambda k)
    (E : ℝ) (hE : HasSum (fun k : ℕ => lambda k) E),
    ∀ r : ℕ,
      HasSum (fun k : ℕ => if r ≤ k then lambda k else 0)
        (E - ∑ k ∈ Finset.range r, lambda k) ∧
      (∑' k : ℕ, (if r ≤ k then lambda k else 0)) =
        E - ∑ k ∈ Finset.range r, lambda k := by
  /- @proof-region region.target-node.session.f7386c2ec9371a62 begin -/
  intro lambda hlambda_nonneg E hE r
  have hg_nonneg : ∀ k : ℕ, 0 ≤ (if r ≤ k then lambda k else 0) := by
    intro k
    split_ifs with h
    · exact hlambda_nonneg k
    · exact le_rfl
  have hsplit : ∀ n : ℕ, r ≤ n →
      ∑ k ∈ Finset.range n, (if r ≤ k then lambda k else 0)
        = (∑ k ∈ Finset.range n, lambda k) - ∑ k ∈ Finset.range r, lambda k := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
        have hz : ∑ k ∈ Finset.range r, (if r ≤ k then lambda k else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro k hk
          rw [Finset.mem_range] at hk
          exact if_neg (Nat.not_le.mpr hk)
        rw [hz, sub_self]
    | succ m hm ih =>
        have hm' : (if r ≤ m then lambda m else 0) = lambda m := if_pos hm
        calc ∑ k ∈ Finset.range (m + 1), (if r ≤ k then lambda k else 0)
            = (∑ k ∈ Finset.range m, (if r ≤ k then lambda k else 0)) + lambda m := by
                rw [Finset.sum_range_succ, hm']
          _ = ((∑ k ∈ Finset.range m, lambda k) - ∑ k ∈ Finset.range r, lambda k) + lambda m := by
                rw [ih]
          _ = (∑ k ∈ Finset.range (m + 1), lambda k) - ∑ k ∈ Finset.range r, lambda k := by
                rw [Finset.sum_range_succ]
                ring
  have hS : Filter.Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, lambda k) Filter.atTop (nhds E) :=
    (hasSum_iff_tendsto_nat_of_nonneg hlambda_nonneg E).1 hE
  have hev : (fun n : ℕ => (∑ k ∈ Finset.range n, lambda k) - ∑ k ∈ Finset.range r, lambda k)
      =ᶠ[Filter.atTop] (fun n : ℕ => ∑ k ∈ Finset.range n, (if r ≤ k then lambda k else 0)) := by
    filter_upwards [Filter.eventually_atTop.2 ⟨r, fun n hn => hsplit n hn⟩] with n hn
    exact hn.symm
  have htend : Filter.Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, (if r ≤ k then lambda k else 0))
      Filter.atTop (nhds (E - ∑ k ∈ Finset.range r, lambda k)) :=
    Filter.Tendsto.congr' hev (hS.sub_const (∑ k ∈ Finset.range r, lambda k))
  have hHas : HasSum (fun k : ℕ => if r ≤ k then lambda k else 0)
      (E - ∑ k ∈ Finset.range r, lambda k) :=
    (hasSum_iff_tendsto_nat_of_nonneg hg_nonneg _).2 htend
  exact ⟨hHas, hHas.tsum_eq⟩
  /- @proof-region region.target-node.session.f7386c2ec9371a62 end -/
