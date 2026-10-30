import Mathlib

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

theorem uniform_endpoint_mle_limit
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (θ : ℝ) (hθ : 0 < θ)
    (X : ℕ → Ω → ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X P)
    (hX_uniform : ∀ i, MeasureTheory.pdf.IsUniform (X i) (Set.Ioo 0 θ) P)
    (Z : Ω → ℝ) (hZ_meas : Measurable Z)
    (hZ_law : HasLaw Z (expMeasure θ⁻¹) P) :
    let M : ℕ → Ω → ℝ := fun r ω ↦
      (Finset.univ : Finset (Fin (r + 1))).sup'
        Finset.univ_nonempty (fun i ↦ X i.1 ω)
    TendstoInDistribution
      (fun r ω ↦ ((r + 1 : ℕ) : ℝ) * (θ - M r ω))
      atTop Z P := by
  sorry
