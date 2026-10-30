import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q02.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q02.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q02.ProvedNodes.Node_1444442084_ecdddf06_0899ce96
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q02.ProvedNodes.Node_488559670_a6d524b3_eb071a4e


open MeasureTheory ProbabilityTheory

open MeasureTheory ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_3259429663_3e1e7d56 : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 1 ≤ n)
    (X : Fin n → Ω → ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_int : ∀ i, Integrable (X i) P)
    (hX_sq : ∀ i, Integrable (fun ω => (X i ω) ^ 2) P)
    (I : Fin n → Ω → Fin n)
    (hXstar_meas : ∀ j, Measurable (fun ω => X (I j ω) ω))
    (hXstar_int : ∀ j, Integrable (fun ω => X (I j ω) ω) P)
    (hXstar_sq : ∀ j, Integrable (fun ω => (X (I j ω) ω) ^ 2) P),
    let Xstar : Fin n → Ω → ℝ := fun j ω => X (I j ω) ω
    let mean : Ω → ℝ := fun ω => (n : ℝ)⁻¹ * ∑ i, X i ω
    let meanStar : Ω → ℝ := fun ω => (n : ℝ)⁻¹ * ∑ j, Xstar j ω
    let V : Ω → ℝ := fun ω => (n : ℝ)⁻¹ * ∑ i, (X i ω - mean ω) ^ 2
    let Vstar : Ω → ℝ := fun ω => (n : ℝ)⁻¹ * ∑ j, (Xstar j ω - meanStar ω) ^ 2
    (∀ i k : Fin n, Integrable (fun ω => (X i ω - X k ω) ^ 2) P)
      ∧ (∀ j l : Fin n, Integrable (fun ω => (Xstar j ω - Xstar l ω) ^ 2) P)
      ∧ (Measurable V ∧ Integrable V P)
      ∧ (Measurable Vstar ∧ Integrable Vstar P) := by
  /- @proof-region region.target-node.session.201cf0360b092da2 begin -/
  intro Ω _ P _ n hn X hX_meas hX_int hX_sq I hXstar_meas hXstar_int hXstar_sq
  dsimp only
  have key : ∀ (Y : Fin n → Ω → ℝ), (∀ i, Measurable (Y i)) →
      (∀ i, Integrable (fun ω => (Y i ω) ^ 2) P) →
      (∀ i k : Fin n, Integrable (fun ω => (Y i ω - Y k ω) ^ 2) P) ∧
        Measurable
          (fun ω => (n : ℝ)⁻¹ * ∑ i : Fin n, (Y i ω - (n : ℝ)⁻¹ * ∑ j : Fin n, Y j ω) ^ 2) ∧
        Integrable
          (fun ω => (n : ℝ)⁻¹ * ∑ i : Fin n, (Y i ω - (n : ℝ)⁻¹ * ∑ j : Fin n, Y j ω) ^ 2) P := by
    intro Y hY_meas hY_sq
    have hpairY : ∀ i k : Fin n, Integrable (fun ω => (Y i ω - Y k ω) ^ 2) P := by
      intro i k
      have hbound : Integrable (fun ω => 2 * (Y i ω) ^ 2 + 2 * (Y k ω) ^ 2) P :=
        ((hY_sq i).const_mul 2).add ((hY_sq k).const_mul 2)
      have hmul : Measurable (fun ω => (Y i ω - Y k ω) * (Y i ω - Y k ω)) :=
        ((hY_meas i).sub (hY_meas k)).mul ((hY_meas i).sub (hY_meas k))
      have hfun : (fun ω => (Y i ω - Y k ω) ^ 2)
          = fun ω => (Y i ω - Y k ω) * (Y i ω - Y k ω) := by
        funext ω
        rw [pow_two]
      have hmeas : AEStronglyMeasurable (fun ω => (Y i ω - Y k ω) ^ 2) P := by
        rw [hfun]
        exact hmul.aestronglyMeasurable
      refine hbound.mono' hmeas (Filter.Eventually.of_forall (fun ω => ?_))
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Y i ω - Y k ω))]
      nlinarith [sq_nonneg (Y i ω + Y k ω)]
    refine ⟨hpairY, ?_, ?_⟩
    · have hsum_meas : Measurable (fun ω => ∑ j : Fin n, Y j ω) := by
        simpa using Finset.measurable_sum (Finset.univ : Finset (Fin n)) (fun j _ => hY_meas j)
      have hmean : Measurable (fun ω => (n : ℝ)⁻¹ * ∑ j : Fin n, Y j ω) := hsum_meas.const_mul _
      have hterm : ∀ i : Fin n,
          Measurable (fun ω => (Y i ω - (n : ℝ)⁻¹ * ∑ j : Fin n, Y j ω) ^ 2) := by
        intro i
        have hd : Measurable (fun ω => Y i ω - (n : ℝ)⁻¹ * ∑ j : Fin n, Y j ω) :=
          (hY_meas i).sub hmean
        have hfun : (fun ω => (Y i ω - (n : ℝ)⁻¹ * ∑ j : Fin n, Y j ω) ^ 2)
            = fun ω => (Y i ω - (n : ℝ)⁻¹ * ∑ j : Fin n, Y j ω)
                * (Y i ω - (n : ℝ)⁻¹ * ∑ j : Fin n, Y j ω) := by
          funext ω
          rw [pow_two]
        rw [hfun]
        exact hd.mul hd
      have hsum2 : Measurable
          (fun ω => ∑ i : Fin n, (Y i ω - (n : ℝ)⁻¹ * ∑ j : Fin n, Y j ω) ^ 2) := by
        simpa using Finset.measurable_sum (Finset.univ : Finset (Fin n)) (fun i _ => hterm i)
      exact hsum2.const_mul _
    · have hdbl : Integrable (fun ω => ∑ j : Fin n, ∑ l : Fin n, (Y j ω - Y l ω) ^ 2) P := by
        have h1 : Integrable
            (fun a => ∑ j ∈ (Finset.univ : Finset (Fin n)), ∑ l ∈ (Finset.univ : Finset (Fin n)),
              (Y j a - Y l a) ^ 2) P :=
          MeasureTheory.integrable_finset_sum _
            (fun j _ => MeasureTheory.integrable_finset_sum _ (fun l _ => hpairY j l))
        simpa using h1
      have hc : Integrable
          (fun ω => (2 * (n : ℝ) ^ 2)⁻¹ * ∑ j : Fin n, ∑ l : Fin n, (Y j ω - Y l ω) ^ 2) P :=
        hdbl.const_mul _
      rw [show (fun ω => (n : ℝ)⁻¹ * ∑ i : Fin n, (Y i ω - (n : ℝ)⁻¹ * ∑ j : Fin n, Y j ω) ^ 2)
            = (fun ω => (2 * (n : ℝ) ^ 2)⁻¹ * ∑ j : Fin n, ∑ l : Fin n, (Y j ω - Y l ω) ^ 2) from by
          funext ω
          exact (statopia_math_node_488559670_a6d524b3 n hn (fun i => Y i ω)).symm]
      exact hc
  exact ⟨(key X hX_meas hX_sq).1, (key (fun j ω => X (I j ω) ω) hXstar_meas hXstar_sq).1,
    (key X hX_meas hX_sq).2, (key (fun j ω => X (I j ω) ω) hXstar_meas hXstar_sq).2⟩
  /- @proof-region region.target-node.session.201cf0360b092da2 end -/
