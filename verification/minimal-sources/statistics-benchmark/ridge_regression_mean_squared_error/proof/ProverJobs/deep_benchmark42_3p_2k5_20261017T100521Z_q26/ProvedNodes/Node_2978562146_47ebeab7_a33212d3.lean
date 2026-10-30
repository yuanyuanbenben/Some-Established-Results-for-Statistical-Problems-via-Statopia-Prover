import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q26.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q26.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q26.ProvedNodes.Node_803344359_2bd487f3_989f23a6

open MeasureTheory Matrix

open MeasureTheory Matrix

set_option autoImplicit false in
theorem statopia_math_node_2978562146_47ebeab7 : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n d : ℕ) (epsilon : Ω → Fin n → ℝ)
    (heps : MemLp epsilon 2 P)
    (L : Matrix (Fin d) (Fin n) ℝ)
    (sigmaSq : ℝ)
    (hcov : ∀ i j : Fin n,
      ∫ ω, epsilon ω i * epsilon ω j ∂P = if i = j then sigmaSq else 0)
    (hint : ∀ i j : Fin n,
      Integrable (fun ω => epsilon ω i * epsilon ω j) P)
    (k : Fin d),
    ∫ ω, (∑ i : Fin n, L k i * epsilon ω i) ^ 2 ∂P
      = sigmaSq * ∑ i : Fin n, (L k i) ^ 2 := by
  /- @proof-region region.target-node.session.9dc49d591736037d begin -/
  intro Ω hms P hP n d epsilon heps L sigmaSq hcov hint k
  have h_expand : ∀ ω, (∑ i : Fin n, L k i * epsilon ω i) ^ 2
      = ∑ i : Fin n, ∑ j : Fin n, (L k i * L k j) * (epsilon ω i * epsilon ω j) := by
    intro ω
    rw [pow_two, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  have hterm : ∀ i j : Fin n,
      Integrable (fun ω => (L k i * L k j) * (epsilon ω i * epsilon ω j)) P :=
    fun i j => (hint i j).const_mul (L k i * L k j)
  calc ∫ ω, (∑ i : Fin n, L k i * epsilon ω i) ^ 2 ∂P
      = ∫ ω, (∑ i : Fin n, ∑ j : Fin n,
          (L k i * L k j) * (epsilon ω i * epsilon ω j)) ∂P := by
        simp only [h_expand]
    _ = ∑ i : Fin n, ∫ ω, (∑ j : Fin n,
          (L k i * L k j) * (epsilon ω i * epsilon ω j)) ∂P := by
        refine integral_finset_sum (s := Finset.univ)
          (f := fun i ω => ∑ j : Fin n, (L k i * L k j) * (epsilon ω i * epsilon ω j)) ?_
        intro i _
        exact integrable_finset_sum Finset.univ (fun j _ => hterm i j)
    _ = ∑ i : Fin n, ∑ j : Fin n,
          (L k i * L k j) * (∫ ω, epsilon ω i * epsilon ω j ∂P) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        refine (integral_finset_sum (s := Finset.univ)
          (f := fun j ω => (L k i * L k j) * (epsilon ω i * epsilon ω j)) ?_).trans ?_
        · intro j _
          exact hterm i j
        · exact Finset.sum_congr rfl
            (fun j _ => integral_const_mul (L k i * L k j) (fun ω => epsilon ω i * epsilon ω j))
    _ = ∑ i : Fin n, (L k i * L k i) * sigmaSq := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        refine (Finset.sum_eq_single (a := i) ?_ ?_).trans ?_
        · intro j _ hj
          rw [hcov i j, if_neg (Ne.symm hj), mul_zero]
        · intro hi
          exact absurd (Finset.mem_univ i) hi
        · rw [hcov i i, if_pos rfl]
    _ = sigmaSq * ∑ i : Fin n, (L k i) ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring)
  /- @proof-region region.target-node.session.9dc49d591736037d end -/
