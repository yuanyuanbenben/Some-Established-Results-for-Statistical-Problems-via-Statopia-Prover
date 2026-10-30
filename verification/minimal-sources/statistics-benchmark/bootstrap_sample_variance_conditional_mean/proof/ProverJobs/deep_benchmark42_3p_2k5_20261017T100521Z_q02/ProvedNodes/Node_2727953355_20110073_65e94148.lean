import Statlib.HypothesisTesting.Nonparametric.MannWhitney
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q02.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q02.Base

open MeasureTheory ProbabilityTheory

open MeasureTheory ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_2727953355_20110073 : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {β : Type*} [MeasurableSpace β]
    {γ : Type*} [MeasurableSpace γ]
    (f : Ω → β) (g : Ω → γ)
    (hf : Measurable f) (hg : Measurable g)
    (hindep : IndepFun f g P)
    (s : Set β) (hs : MeasurableSet s)
    (h : γ → ℝ) (hh : Measurable h)
    (hint : Integrable (fun ω => h (g ω)) P),
    condExp (MeasurableSpace.comap g (inferInstance : MeasurableSpace γ)) P
        (fun ω => (s.indicator (fun _ => (1 : ℝ))) (f ω) * h (g ω))
      =ᵐ[P] fun ω => (P (f ⁻¹' s)).toReal * h (g ω) := by
  /- @proof-region region.target-node.session.453017dd860fa579 begin -/
  intro Ω _ P _ β _ γ _ f g hf hg hindep s hs h hh hint
  classical
  have hm : MeasurableSpace.comap g (inferInstance : MeasurableSpace γ) ≤
      (inferInstance : MeasurableSpace Ω) := by
    intro t ht
    rw [MeasurableSpace.measurableSet_comap] at ht
    obtain ⟨u, hu, hgu⟩ := ht
    rw [← hgu]
    exact hg hu
  have hF_int : Integrable (fun ω => (s.indicator (fun _ => (1 : ℝ))) (f ω) * h (g ω)) P := by
    have hEq : (fun ω => (s.indicator (fun _ => (1 : ℝ))) (f ω) * h (g ω))
        = (f ⁻¹' s).indicator (fun ω => h (g ω)) := by
      funext ω
      by_cases hmem : f ω ∈ s <;> simp [Set.mem_preimage, hmem]
    rw [hEq]
    exact hint.indicator (hf hs)
  have hG_int : Integrable (fun ω => (P (f ⁻¹' s)).toReal * h (g ω)) P :=
    hint.const_mul _
  have hcg : Measurable[MeasurableSpace.comap g (inferInstance : MeasurableSpace γ)]
      (fun ω => h (g ω)) := by
    intro t ht
    rw [MeasurableSpace.measurableSet_comap]
    exact ⟨h ⁻¹' t, hh ht, rfl⟩
  have hG_meas : AEStronglyMeasurable[MeasurableSpace.comap g (inferInstance : MeasurableSpace γ)]
      (fun ω => (P (f ⁻¹' s)).toReal * h (g ω)) P :=
    (hcg.const_mul _).aestronglyMeasurable
  have hInt_on : ∀ t : Set Ω,
      @MeasurableSet Ω (MeasurableSpace.comap g (inferInstance : MeasurableSpace γ)) t →
      P t < ⊤ → IntegrableOn (fun ω => (P (f ⁻¹' s)).toReal * h (g ω)) t P :=
    fun t _ _ => hG_int.integrableOn
  have key : ∀ t : Set Ω,
      @MeasurableSet Ω (MeasurableSpace.comap g (inferInstance : MeasurableSpace γ)) t →
      P t < ⊤ → ∫ ω in t, (P (f ⁻¹' s)).toReal * h (g ω) ∂P
        = ∫ ω in t, (s.indicator (fun _ => (1 : ℝ))) (f ω) * h (g ω) ∂P := by
    intro t ht _
    rw [MeasurableSpace.measurableSet_comap] at ht
    obtain ⟨u, hu, hgu⟩ := ht
    rw [← hgu]
    have hL : ∫ ω in g ⁻¹' u, (P (f ⁻¹' s)).toReal * h (g ω) ∂P
        = (P (f ⁻¹' s)).toReal * ∫ ω in g ⁻¹' u, h (g ω) ∂P := by
      simpa only [smul_eq_mul] using
        (MeasureTheory.integral_const_mul (μ := P.restrict (g ⁻¹' u))
          (P (f ⁻¹' s)).toReal (fun ω => h (g ω)))
    have hφ : Measurable (s.indicator (fun _ => (1 : ℝ))) :=
      Measurable.indicator measurable_const hs
    have hψ : Measurable (fun y : γ => (u.indicator (fun _ => (1 : ℝ))) y * h y) := by
      have hEq : (fun y : γ => (u.indicator (fun _ => (1 : ℝ))) y * h y) = u.indicator h := by
        funext y
        by_cases hy : y ∈ u <;> simp [hy]
      rw [hEq]
      exact Measurable.indicator hh hu
    have hXm : AEStronglyMeasurable (fun ω => (s.indicator (fun _ => (1 : ℝ))) (f ω)) P :=
      (hφ.comp hf).aestronglyMeasurable
    have hYm : AEStronglyMeasurable
        (fun ω => (u.indicator (fun _ => (1 : ℝ))) (g ω) * h (g ω)) P :=
      (hψ.comp hg).aestronglyMeasurable
    have hind : IndepFun (fun ω => (s.indicator (fun _ => (1 : ℝ))) (f ω))
        (fun ω => (u.indicator (fun _ => (1 : ℝ))) (g ω) * h (g ω)) P := by
      have h0 := hindep.comp (φ := fun y => s.indicator (fun _ => (1 : ℝ)) y)
        (ψ := fun y => (u.indicator (fun _ => (1 : ℝ))) y * h y) hφ hψ
      simpa only [Function.comp_def] using h0
    have hXint : ∫ ω, (fun ω => (s.indicator (fun _ => (1 : ℝ))) (f ω)) ω ∂P
        = (P (f ⁻¹' s)).toReal := by
      have hfun : (fun ω => (s.indicator (fun _ => (1 : ℝ))) (f ω))
          = (f ⁻¹' s).indicator (fun x => (1 : ℝ)) := by
        funext ω
        by_cases hmem : f ω ∈ s <;> simp [Set.mem_preimage, hmem]
      rw [hfun]
      exact (Statlib.HypothesisTesting.measure_eq_integral_indicator (μ := P) (hf hs)).symm
    have hYint : ∫ ω, (fun ω => (u.indicator (fun _ => (1 : ℝ))) (g ω) * h (g ω)) ω ∂P
        = ∫ ω in g ⁻¹' u, h (g ω) ∂P := by
      have hfun : (fun ω => (u.indicator (fun _ => (1 : ℝ))) (g ω) * h (g ω))
          = (g ⁻¹' u).indicator (fun ω => h (g ω)) := by
        funext ω
        by_cases hmem : g ω ∈ u <;> simp [Set.mem_preimage, hmem]
      rw [hfun, MeasureTheory.integral_indicator (hg hu)]
    have hpt : (g ⁻¹' u).indicator
          (fun ω => (s.indicator (fun _ => (1 : ℝ))) (f ω) * h (g ω))
        = (fun ω => (s.indicator (fun _ => (1 : ℝ))) (f ω)) *
            (fun ω => (u.indicator (fun _ => (1 : ℝ))) (g ω) * h (g ω)) := by
      funext ω
      show (g ⁻¹' u).indicator
          (fun ω => (s.indicator (fun _ => (1 : ℝ))) (f ω) * h (g ω)) ω
        = (s.indicator (fun _ => (1 : ℝ))) (f ω) *
            ((u.indicator (fun _ => (1 : ℝ))) (g ω) * h (g ω))
      by_cases h1 : f ω ∈ s <;> by_cases h2 : g ω ∈ u <;> simp [Set.mem_preimage, h1, h2]
    have hR : ∫ ω in g ⁻¹' u, (s.indicator (fun _ => (1 : ℝ))) (f ω) * h (g ω) ∂P
        = (P (f ⁻¹' s)).toReal * ∫ ω in g ⁻¹' u, h (g ω) ∂P := by
      calc ∫ ω in g ⁻¹' u, (s.indicator (fun _ => (1 : ℝ))) (f ω) * h (g ω) ∂P
          = ∫ ω, (g ⁻¹' u).indicator
              (fun ω => (s.indicator (fun _ => (1 : ℝ))) (f ω) * h (g ω)) ω ∂P := by
            rw [MeasureTheory.integral_indicator (hg hu)]
        _ = ∫ ω, ((fun ω => (s.indicator (fun _ => (1 : ℝ))) (f ω)) *
              (fun ω => (u.indicator (fun _ => (1 : ℝ))) (g ω) * h (g ω))) ω ∂P := by
            rw [hpt]
        _ = (∫ ω, (fun ω => (s.indicator (fun _ => (1 : ℝ))) (f ω)) ω ∂P) *
              ∫ ω, (fun ω => (u.indicator (fun _ => (1 : ℝ))) (g ω) * h (g ω)) ω ∂P :=
            ProbabilityTheory.IndepFun.integral_mul_eq_mul_integral hind hXm hYm
        _ = (P (f ⁻¹' s)).toReal * ∫ ω in g ⁻¹' u, h (g ω) ∂P := by
            rw [hXint, hYint]
    rw [hL, hR]
  exact (MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq hm hF_int hInt_on
    (fun t ht hPt => key t ht hPt) hG_meas).symm
  /- @proof-region region.target-node.session.453017dd860fa579 end -/
