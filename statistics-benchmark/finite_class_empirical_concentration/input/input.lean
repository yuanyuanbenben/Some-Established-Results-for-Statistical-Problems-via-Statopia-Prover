import Mathlib

open MeasureTheory ProbabilityTheory

namespace Msc62GroundTruth

/-- Hoeffding's finite-class union bound for bounded iid observations. -/
theorem finite_class_empirical_concentration
    {Omega X : Type*} [MeasurableSpace Omega] [MeasurableSpace X]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (n N : ℕ) (hn : 1 ≤ n) (hN : 1 ≤ N)
    (sample : Fin n → Omega → X)
    (h_sample_meas : ∀ i, Measurable (sample i))
    (h_sample_iid : ∀ i j, IdentDistrib (sample i) (sample j) P P)
    (h_sample_indep : iIndepFun (β := fun _ : Fin n => X) sample P)
    (f : Fin N → X → ℝ)
    (h_f_meas : ∀ j, Measurable (f j))
    (h_f_range : ∀ j x, f j x ∈ Set.Icc (0 : ℝ) 1) :
    let empirical (j : Fin N) (omega : Omega) : ℝ :=
      (∑ i : Fin n, f j (sample i omega)) / (n : ℝ)
    let population (j : Fin N) : ℝ :=
      ∫ omega, f j (sample ⟨0, Nat.pos_of_ne_zero (by omega)⟩ omega) ∂P
    ∀ delta : ℝ, 0 < delta → delta < 1 →
      (P {omega |
        (Finset.univ.sup'
          ⟨⟨0, hN⟩, Finset.mem_univ _⟩
          (fun j : Fin N =>
            |empirical j omega - population j|)) ≤
          Real.sqrt (Real.log (2 * (N : ℝ) / delta) / (2 * (n : ℝ))) }).toReal
        ≥ 1 - delta := by
  sorry

end Msc62GroundTruth
