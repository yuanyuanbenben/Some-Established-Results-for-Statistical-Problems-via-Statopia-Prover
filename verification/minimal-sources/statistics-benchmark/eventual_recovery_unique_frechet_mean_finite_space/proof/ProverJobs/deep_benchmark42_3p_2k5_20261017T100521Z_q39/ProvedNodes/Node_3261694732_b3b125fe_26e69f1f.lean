import Statlib.StatFoundation.Convergence.LawOfLargeNumbers.UniformStrongLaw
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q39.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q39.Base

open MeasureTheory ProbabilityTheory

open MeasureTheory ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_3261694732_b3b125fe : ∀ {Ω Xs : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Xs] [MeasurableSingletonClass Xs]
    [Fintype Xs] [MetricSpace Xs]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → Xs)
    (hXmeas : Measurable (X 0))
    (z : Xs),
    Statlib.StatFoundation.Convergence.populationMean (P := P) X
        (fun x w => dist w x ^ 2) z =
        ∑ x : Xs, (P {ω | X 0 ω = x}).toReal * dist z x ^ 2 ∧
      ∫ ω, dist z (X 0 ω) ^ 2 ∂P =
        ∑ x : Xs, (P {ω | X 0 ω = x}).toReal * dist z x ^ 2 := by
  /- @proof-region region.target-node.session.ceae4e5ca71f5e68 begin -/
  intro Ω Xs _ _ _ _ _ P _ X hXmeas z
  classical
  have hmeas : ∀ x : Xs, MeasurableSet {ω : Ω | X 0 ω = x} :=
    fun x => hXmeas (measurableSet_singleton x)
  have hfun : ∀ x : Xs, (fun ω : Ω => if X 0 ω = x then dist z x ^ 2 else 0)
      = Set.indicator {ω : Ω | X 0 ω = x} (fun _ : Ω => dist z x ^ 2) := by
    intro x
    funext ω
    by_cases h : X 0 ω = x
    · simp [Set.indicator, h]
    · simp [Set.indicator, h]
  have hInt : ∀ x : Xs, Integrable (fun ω : Ω => if X 0 ω = x then dist z x ^ 2 else 0) P := by
    intro x
    rw [hfun x]
    exact (MeasureTheory.integrable_const (dist z x ^ 2)).indicator (hmeas x)
  have hterm : ∀ x : Xs, ∫ ω, (if X 0 ω = x then dist z x ^ 2 else (0 : ℝ)) ∂P
      = (P {ω | X 0 ω = x}).toReal * dist z x ^ 2 := by
    intro x
    rw [hfun x, MeasureTheory.integral_indicator (hmeas x)]
    simp only [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, smul_eq_mul]
  have hpt : ∀ ω : Ω, dist z (X 0 ω) ^ 2
      = ∑ x : Xs, (if X 0 ω = x then dist z x ^ 2 else (0 : ℝ)) := by
    intro ω
    rw [Finset.sum_eq_single (X 0 ω)]
    · simp
    · intro x _ hx
      exact if_neg (Ne.symm hx)
    · intro h
      exact absurd (Finset.mem_univ (X 0 ω)) h
  have h : ∫ ω, dist z (X 0 ω) ^ 2 ∂P
      = ∑ x : Xs, (P {ω | X 0 ω = x}).toReal * dist z x ^ 2 := by
    rw [show (fun ω : Ω => dist z (X 0 ω) ^ 2)
        = fun ω => ∑ x : Xs, (if X 0 ω = x then dist z x ^ 2 else (0 : ℝ)) from
      funext hpt]
    rw [MeasureTheory.integral_finset_sum Finset.univ (fun x _ => hInt x)]
    exact Finset.sum_congr rfl (fun x _ => hterm x)
  have hmap : ∫ a : Xs, dist z a ^ 2 ∂(Measure.map (X 0) P)
      = ∑ x : Xs, (P {ω | X 0 ω = x}).toReal * dist z x ^ 2 := by
    rw [MeasureTheory.integral_map (f := fun a : Xs => dist z a ^ 2) hXmeas.aemeasurable
      (by measurability)]
    exact h
  exact ⟨by simpa only [Statlib.StatFoundation.Convergence.populationMean] using hmap, h⟩


  /- @proof-region region.target-node.session.ceae4e5ca71f5e68 end -/
