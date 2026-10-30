import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q01.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q01.Base

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

set_option autoImplicit false in
theorem statopia_math_node_3608758345_cf56cc49 : ∀ (d : ℕ) (hd : 1 ≤ d)
    (nu : ℕ → Measure (EuclideanSpace ℝ (Fin d)))
    (hnu : ∀ r, IsProbabilityMeasure (nu r))
    (mu : Measure (EuclideanSpace ℝ (Fin d)))
    (hmu : IsProbabilityMeasure mu)
    (hchar : ∀ t : EuclideanSpace ℝ (Fin d),
      Tendsto (fun r => charFun (nu r) t) atTop (𝓝 (charFun mu t)))
    (hcont : ContinuousAt (charFun mu) 0),
    ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, Continuous f →
      (∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) →
        Tendsto (fun r => ∫ x, f x ∂(nu r)) atTop (𝓝 (∫ x, f x ∂mu)) := by
  /- @proof-region region.target-node.session.4afdf8c189f0f3cd begin -/
  intro d hd nu hnu mu hmu hchar hcont f hf hfb
  obtain ⟨C, hC⟩ := hfb
  haveI : IsProbabilityMeasure mu := hmu
  haveI : OpensMeasurableSpace (EuclideanSpace ℝ (Fin d)) := inferInstance
  have hg0 : charFun mu 0 = 1 := by
    rw [MeasureTheory.charFun_apply]
    simp
  have hconv : ∀ t : EuclideanSpace ℝ (Fin d),
      Tendsto (fun n => charFun (↑(⟨nu n, hnu n⟩ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)))) t)
        atTop (𝓝 (charFun mu t)) := by
    intro t
    simpa using hchar t
  obtain ⟨μ₀, hchar₀, htend⟩ :=
    Statlib.StatFoundation.Convergence.CramerWold.cramer_wold_charFun
      (f := fun t : EuclideanSpace ℝ (Fin d) => charFun mu t) hconv hg0 hcont
  have hlim : μ₀ = (⟨mu, hmu⟩ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) := by
    apply Statlib.StatFoundation.Convergence.CramerWold.probMeasure_eq_of_charFun_eq_inner
    intro t
    simpa using hchar₀ t
  have hF := (MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto
    (μs := fun r => (⟨nu r, hnu r⟩ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))))
    (μ := (⟨mu, hmu⟩ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)))) (F := atTop)).mp
      (hlim ▸ htend)
  have hdist : ∀ x y : EuclideanSpace ℝ (Fin d), dist (f x) (f y) ≤ 2 * C := by
    intro x y
    have h1 : dist (f x) (f y) ≤ ‖f x‖ + ‖f y‖ := by
      calc dist (f x) (f y) ≤ dist (f x) 0 + dist 0 (f y) := dist_triangle _ _ _
        _ = ‖f x‖ + ‖f y‖ := by simp
    have h2 : ‖f x‖ + ‖f y‖ ≤ C + C := add_le_add (hC x) (hC y)
    linarith
  have hfin := hF (⟨⟨f, hf⟩, 2 * C, hdist⟩ :
    BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ)
  simpa using hfin
  /- @proof-region region.target-node.session.4afdf8c189f0f3cd end -/
