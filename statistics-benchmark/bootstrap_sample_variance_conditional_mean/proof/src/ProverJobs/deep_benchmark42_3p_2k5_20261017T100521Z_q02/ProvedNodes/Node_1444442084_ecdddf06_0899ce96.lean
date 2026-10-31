import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q02.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q02.Base

open MeasureTheory ProbabilityTheory

open MeasureTheory ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_1444442084_ecdddf06 : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 1 ≤ n)
    (X : Fin n → Ω → ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (i0 : Fin n)
    (hX_ident : ∀ i, IdentDistrib (X i) (X i0) P P)
    (hX_sq : Integrable (fun ω => (X i0 ω) ^ 2) P)
    (I : Fin n → Ω → Fin n)
    (hI_meas : ∀ j, Measurable (I j)),
    (∀ i : Fin n,
        Integrable (fun ω => (X i ω) ^ 2) P ∧ Integrable (X i) P)
      ∧ (∀ j : Fin n,
        Measurable (fun ω => X (I j ω) ω)
          ∧ Integrable (fun ω => X (I j ω) ω) P
          ∧ Integrable (fun ω => (X (I j ω) ω) ^ 2) P) := by
  /- @proof-region region.target-node.session.1e4e778b11ccd1cf begin -/
  intro Ω _ P _ n hn X hX_meas i0 hX_ident hX_sq I hI_meas
  have hbound : ∀ x : ℝ, |x| ≤ x ^ 2 + 1 := by
    intro x
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (x + 1 / 2), sq_nonneg x]
  have hsq : ∀ i : Fin n, Integrable (fun ω => (X i ω) ^ 2) P := fun i =>
    (hX_ident i).sq.integrable_iff.mpr hX_sq
  have hInt1 : ∀ i : Fin n, Integrable (X i) P := by
    intro i
    have hmono : Integrable (fun ω => (X i ω) ^ 2 + 1) P :=
      (hsq i).add (integrable_const (1 : ℝ))
    refine hmono.mono (hX_meas i).aestronglyMeasurable ?_
    filter_upwards with ω
    have h1 : (0 : ℝ) ≤ (X i ω) ^ 2 + 1 := by positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h1]
    exact hbound _
  have hset : ∀ (j i : Fin n), MeasurableSet {ω : Ω | I j ω = i} := fun j i =>
    (hI_meas j) (measurableSet_singleton i)
  have hdec : ∀ (j : Fin n) (ω : Ω),
      (∑ i : Fin n, Set.indicator {ω' : Ω | I j ω' = i} (X i) ω) = X (I j ω) ω := by
    intro j ω
    refine (Finset.sum_eq_single (I j ω) ?_ ?_).trans ?_
    · intro i _ hi
      have hmem : ¬ (I j ω = i) := fun h => hi h.symm
      simp [Set.indicator, hmem]
    · intro h
      exact absurd (Finset.mem_univ (I j ω)) h
    · simp
  have hdec2 : ∀ (j : Fin n) (ω : Ω),
      (∑ i : Fin n, Set.indicator {ω' : Ω | I j ω' = i} (fun ω' => (X i ω') ^ 2) ω)
        = (X (I j ω) ω) ^ 2 := by
    intro j ω
    refine (Finset.sum_eq_single (I j ω) ?_ ?_).trans ?_
    · intro i _ hi
      have hmem : ¬ (I j ω = i) := fun h => hi h.symm
      simp [Set.indicator, hmem]
    · intro h
      exact absurd (Finset.mem_univ (I j ω)) h
    · simp
  have hmeas_star : ∀ j : Fin n, Measurable (fun ω => X (I j ω) ω) := by
    intro j
    have hsum_meas : Measurable
        (fun ω => ∑ i : Fin n, Set.indicator {ω' : Ω | I j ω' = i} (X i) ω) := by
      apply Finset.measurable_sum
      intro i _
      exact (hX_meas i).indicator (hset j i)
    have heq : (fun ω => X (I j ω) ω)
        = (fun ω => ∑ i : Fin n, Set.indicator {ω' : Ω | I j ω' = i} (X i) ω) :=
      (funext (hdec j)).symm
    rw [heq]
    exact hsum_meas
  have hsum_int : ∀ (g : Fin n → Ω → ℝ), (∀ i, Integrable (g i) P) →
      Integrable (fun ω => ∑ i : Fin n, g i ω) P := by
    intro g hg
    have key : ∀ s : Finset (Fin n), Integrable (fun ω => s.sum (fun i => g i ω)) P := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
          simpa using (integrable_const (0 : ℝ) : Integrable (fun _ : Ω => (0 : ℝ)) P)
      | insert a s ha ih =>
          have hfun : (fun ω => (insert a s).sum (fun i => g i ω))
              = fun ω => g a ω + s.sum (fun i => g i ω) := by
            funext ω
            simp only [Finset.sum_insert ha]
          rw [hfun]
          exact (hg a).add ih
    exact key Finset.univ
  have hsum_sq_int : ∀ j : Fin n, Integrable
      (fun ω => ∑ i : Fin n, Set.indicator {ω' : Ω | I j ω' = i} (fun ω' => (X i ω') ^ 2) ω) P := by
    intro j
    refine hsum_int (fun i => Set.indicator {ω' : Ω | I j ω' = i} (fun ω' => (X i ω') ^ 2)) ?_
    intro i
    exact (hsq i).indicator (hset j i)
  have hsq_star : ∀ j : Fin n, Integrable (fun ω => (X (I j ω) ω) ^ 2) P := by
    intro j
    refine (hsum_sq_int j).congr ?_
    filter_upwards with ω
    exact hdec2 j ω
  have hInt_star : ∀ j : Fin n, Integrable (fun ω => X (I j ω) ω) P := by
    intro j
    have hmono : Integrable (fun ω => (X (I j ω) ω) ^ 2 + 1) P :=
      (hsq_star j).add (integrable_const (1 : ℝ))
    refine hmono.mono (hmeas_star j).aestronglyMeasurable ?_
    filter_upwards with ω
    have h1 : (0 : ℝ) ≤ (X (I j ω) ω) ^ 2 + 1 := by positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h1]
    exact hbound _
  exact ⟨fun i => ⟨hsq i, hInt1 i⟩, fun j => ⟨hmeas_star j, hInt_star j, hsq_star j⟩⟩
  /- @proof-region region.target-node.session.1e4e778b11ccd1cf end -/
