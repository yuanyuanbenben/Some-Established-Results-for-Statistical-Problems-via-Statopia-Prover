import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q11.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q11.Base

open MeasureTheory

open MeasureTheory

set_option autoImplicit false in
theorem statopia_math_node_2638301687_3687fe5f : ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (phi : ℕ → H) (horth : Orthonormal ℝ phi) (r : ℕ) (x : H),
    let S : H := ∑ k ∈ Finset.range r, (inner ℝ x (phi k)) • phi k
    ‖S‖ ^ 2 = ∑ k ∈ Finset.range r, (inner ℝ x (phi k)) ^ 2 ∧
    ‖x - S‖ ^ 2 = ‖x‖ ^ 2 - ∑ k ∈ Finset.range r, (inner ℝ x (phi k)) ^ 2 ∧
    inner ℝ (x - S) S = 0 ∧
    0 ≤ ∑ k ∈ Finset.range r, (inner ℝ x (phi k)) ^ 2 ∧
    (∑ k ∈ Finset.range r, (inner ℝ x (phi k)) ^ 2) ≤ ‖x‖ ^ 2 ∧
    ‖x - S‖ ≤ ‖x‖ := by
  /- @proof-region region.target-node.session.66147af3ac4f466f begin -/
  intro H _ _ phi horth r x
  dsimp only
  set S : H := ∑ k ∈ Finset.range r, (inner ℝ x (phi k)) • phi k with hS
  have hSS : inner ℝ S S = ∑ k ∈ Finset.range r, (inner ℝ x (phi k)) ^ 2 := by
    rw [hS]
    rw [Orthonormal.inner_sum horth (fun k => inner ℝ x (phi k)) (fun k => inner ℝ x (phi k))
      (Finset.range r)]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp [pow_two]
  have hxS : inner ℝ x S = ∑ k ∈ Finset.range r, (inner ℝ x (phi k)) ^ 2 := by
    rw [hS, inner_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [real_inner_smul_right]
    ring
  have hSx : inner ℝ S x = ∑ k ∈ Finset.range r, (inner ℝ x (phi k)) ^ 2 := by
    rw [real_inner_comm]
    exact hxS
  have h1 : ‖S‖ ^ 2 = ∑ k ∈ Finset.range r, (inner ℝ x (phi k)) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    exact hSS
  have h3 : inner ℝ (x - S) S = 0 := by
    rw [inner_sub_left, hxS, hSS]
    ring
  have h2 : ‖x - S‖ ^ 2 = ‖x‖ ^ 2 - ∑ k ∈ Finset.range r, (inner ℝ x (phi k)) ^ 2 := by
    have hexp : ‖x - S‖ ^ 2 = inner ℝ x x - inner ℝ x S - inner ℝ S x + inner ℝ S S := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [inner_sub_left, inner_sub_right]
      ring
    rw [hexp, hxS, hSS, hSx, ← real_inner_self_eq_norm_sq]
    ring
  have h4 : 0 ≤ ∑ k ∈ Finset.range r, (inner ℝ x (phi k)) ^ 2 :=
    Finset.sum_nonneg (fun k _ => sq_nonneg (inner ℝ x (phi k)))
  have h5 : (∑ k ∈ Finset.range r, (inner ℝ x (phi k)) ^ 2) ≤ ‖x‖ ^ 2 := by
    linarith [h2, sq_nonneg ‖x - S‖]
  have h6 : ‖x - S‖ ≤ ‖x‖ := by
    have hsq : ‖x - S‖ ^ 2 ≤ ‖x‖ ^ 2 := by linarith [h2, h4]
    have hab : |‖x - S‖| ≤ |‖x‖| := sq_le_sq.mp hsq
    rwa [abs_of_nonneg (norm_nonneg (x - S)), abs_of_nonneg (norm_nonneg x)] at hab
  exact ⟨h1, h2, h3, h4, h5, h6⟩

  /- @proof-region region.target-node.session.66147af3ac4f466f end -/
