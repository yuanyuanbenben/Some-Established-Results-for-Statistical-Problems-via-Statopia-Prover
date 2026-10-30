import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q01.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q01.ProvedNodes
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q01.Base

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

theorem two_sample_multivariate_central_limit_theorem
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (d : ℕ) (hd : 1 ≤ d)
    (X Y : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (G : Ω → EuclideanSpace ℝ (Fin d))
    (cov : Matrix (Fin d) (Fin d) ℝ)
    (m n : ℕ → ℕ)
    (hX_meas : ∀ i, Measurable (X i))
    (hY_meas : ∀ i, Measurable (Y i))
    (hX_indep : iIndepFun X P)
    (hY_indep : iIndepFun Y P)
    (hXY_indep :
      IndepFun (fun ω i ↦ X i ω) (fun ω i ↦ Y i ω) P)
    (hX_ident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hY_ident : ∀ i, IdentDistrib (Y i) (Y 0) P P)
    (hXY_ident : IdentDistrib (X 0) (Y 0) P P)
    (hX_second : Integrable (fun ω ↦ ‖X 0 ω‖ ^ 2) P)
    (hX_cov : ∀ j k,
      ∫ ω,
          (X 0 ω j - (∫ ω, X 0 ω ∂P) j) *
            (X 0 ω k - (∫ ω, X 0 ω ∂P) k) ∂P =
        cov j k)
    (hG_meas : Measurable G)
    (hG_gaussian : IsGaussian (P.map G))
    (hG_mean : ∫ ω, G ω ∂P = 0)
    (hG_cov : ∀ j k, ∫ ω, G ω j * G ω k ∂P = cov j k)
    (hm_pos : ∀ r, 0 < m r)
    (hn_pos : ∀ r, 0 < n r)
    (hm_lim : Tendsto m atTop atTop)
    (hn_lim : Tendsto n atTop atTop) :
    TendstoInDistribution
      (fun r ω ↦
        Real.sqrt
            (((m r : ℝ) * (n r : ℝ)) /
              ((m r : ℝ) + (n r : ℝ))) •
          (((m r : ℝ)⁻¹) •
              ∑ i ∈ Finset.range (m r), X i ω -
            ((n r : ℝ)⁻¹) •
              ∑ i ∈ Finset.range (n r), Y i ω))
      atTop G P
:= by
  /- @proof-region region.root.f0e6271254d2 begin -/
  set T : ℕ → Ω → EuclideanSpace ℝ (Fin d) :=
    fun r ω =>
      Real.sqrt (((m r : ℝ) * (n r : ℝ)) / ((m r : ℝ) + (n r : ℝ))) •
        (((m r : ℝ)⁻¹ • ∑ i ∈ Finset.range (m r), X i ω) -
          ((n r : ℝ)⁻¹ • ∑ i ∈ Finset.range (n r), Y i ω)) with hT
  have hT_meas : ∀ r, Measurable (T r) := by
    intro r
    have h1 : Measurable fun ω => ∑ i ∈ Finset.range (m r), X i ω := by
      apply Finset.measurable_sum
      intro i _
      exact hX_meas i
    have h2 : Measurable fun ω => ∑ i ∈ Finset.range (n r), Y i ω := by
      apply Finset.measurable_sum
      intro i _
      exact hY_meas i
    have h3 : Measurable fun ω =>
        ((m r : ℝ)⁻¹ • ∑ i ∈ Finset.range (m r), X i ω) -
          ((n r : ℝ)⁻¹ • ∑ i ∈ Finset.range (n r), Y i ω) :=
      (h1.const_smul ((m r : ℝ)⁻¹)).sub (h2.const_smul ((n r : ℝ)⁻¹))
    have h4 : Measurable fun ω =>
        Real.sqrt (((m r : ℝ) * (n r : ℝ)) / ((m r : ℝ) + (n r : ℝ))) •
          (((m r : ℝ)⁻¹ • ∑ i ∈ Finset.range (m r), X i ω) -
            ((n r : ℝ)⁻¹ • ∑ i ∈ Finset.range (n r), Y i ω)) :=
      h3.const_smul
        (Real.sqrt (((m r : ℝ) * (n r : ℝ)) / ((m r : ℝ) + (n r : ℝ))))
    simpa only [hT] using h4
  have hT_prob : ∀ r, IsProbabilityMeasure (P.map (T r)) := fun r =>
    MeasureTheory.Measure.isProbabilityMeasure_map (hT_meas r).aemeasurable
  have hG_prob : IsProbabilityMeasure (P.map G) :=
    MeasureTheory.Measure.isProbabilityMeasure_map hG_meas.aemeasurable
  have hconv := statopia_math_node_744776411_c0fb087e P d X Y cov m n
    hX_meas hY_meas hX_indep hY_indep hXY_indep hX_ident hY_ident hXY_ident
    hX_second hX_cov hm_pos hn_pos hm_lim hn_lim
  have hGchar : ∀ t : EuclideanSpace ℝ (Fin d),
      charFun (P.map G) t =
        Complex.exp
          (-(1 / 2 : ℂ) * ↑(∑ j : Fin d, ∑ k : Fin d, t j * t k * cov j k)) :=
    fun t =>
      (statopia_math_node_1384096660_897ab94b P d hd G cov hG_meas hG_gaussian hG_mean
        hG_cov t).2
  have hchar : ∀ t : EuclideanSpace ℝ (Fin d),
      Tendsto (fun r => charFun (P.map (T r)) t) atTop (𝓝 (charFun (P.map G) t)) := by
    intro t
    simpa only [hT, hGchar t] using hconv t
  have hcont : ContinuousAt (charFun (P.map G)) 0 := by
    haveI : IsProbabilityMeasure (P.map G) := hG_prob
    exact (Statlib.StatFoundation.Convergence.CramerWold.continuous_charFun (P.map G)).continuousAt
  have hbc : ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, Continuous f →
      (∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) →
        Tendsto (fun r => ∫ x, f x ∂(P.map (T r))) atTop (𝓝 (∫ x, f x ∂(P.map G))) :=
    statopia_math_node_3608758345_cf56cc49 d hd (fun r => P.map (T r)) hT_prob (P.map G)
      hG_prob hchar hcont
  have hw : Statlib.StatFoundation.Convergence.WeakConvergence
      (fun r => (⟨P.map (T r), hT_prob r⟩ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))))
      (⟨P.map G, hG_prob⟩ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) := by
    unfold Statlib.StatFoundation.Convergence.WeakConvergence
    rw [MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    exact hbc ⇑f f.continuous ⟨‖f‖, fun x => f.norm_coe_le_norm x⟩
  exact Statlib.StatFoundation.Convergence.tendstoInDistribution_of_weakConvergence_law P T G
    (fun r => (hT_meas r).aemeasurable) hG_meas.aemeasurable hw
  /- @proof-region region.root.f0e6271254d2 end -/
