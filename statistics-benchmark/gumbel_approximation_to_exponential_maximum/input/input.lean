import Mathlib

open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem gumbel_approximation_to_exponential_maximum
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 1 ≤ n)
    (X : Fin n → Ω → ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X P)
    (hX_law : ∀ i, IdentDistrib (X i) id P (expMeasure 1)) :
    let i₀ : Fin n := ⟨0, hn⟩
    let hne : (Finset.univ : Finset (Fin n)).Nonempty :=
      ⟨i₀, Finset.mem_univ i₀⟩
    let M : Ω → ℝ :=
      fun ω ↦ Finset.univ.sup' hne (fun i ↦ X i ω)
    sSup
        (Set.range fun x : ℝ ↦
          |ENNReal.toReal (P {ω | M ω - Real.log (n : ℝ) ≤ x}) -
            Real.exp (-Real.exp (-x))|)
      ≤ 1 / (n : ℝ) := by
  sorry
