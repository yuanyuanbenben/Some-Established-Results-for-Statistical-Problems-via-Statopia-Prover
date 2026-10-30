import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q07.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q07.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q07.ProvedNodes.Node_1861819959_faf8835a_83b5e2a4
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q07.ProvedNodes.Node_41308827_d98f99c7_b68d8124

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

set_option autoImplicit false in
theorem statopia_math_node_3270619228_393e5828 : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ)
    (mean varianceSq fourthMoment : ℝ)
    (G : Ω → ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X P)
    (hX_ident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hfourth_integrable : Integrable (fun ω ↦ |X 0 ω| ^ 4) P)
    (hmean : ∫ ω, X 0 ω ∂P = mean)
    (hvariance : ∫ ω, (X 0 ω - mean) ^ 2 ∂P = varianceSq)
    (hfourth : ∫ ω, (X 0 ω - mean) ^ 4 ∂P = fourthMoment)
    (hgap : varianceSq ^ 2 < fourthMoment)
    (hG_meas : Measurable G)
    (hG_law :
      IdentDistrib G id P
        (gaussianReal 0
          ⟨fourthMoment - varianceSq ^ 2, sub_nonneg.mpr hgap.le⟩)),
    TendstoInDistribution
      (fun (n : ℕ) ω ↦
        (Real.sqrt (n : ℝ))⁻¹ *
          ∑ i ∈ Finset.range n, ((X i ω - mean) ^ 2 - varianceSq))
      atTop G P := by
  /- @proof-region region.target-node.session.515998652d59d2e1 begin -/
  intro Ω instΩ P instP X mean varianceSq fourthMoment G hX_meas hX_indep hX_ident
    hfourth_integrable hmean hvariance hfourth hgap hG_meas hG_law
  obtain ⟨hY_meas, hY_indep, hY_ident, hY_memLp, hY_sq, hY_mean, hvar_eq, hvar_val, hvar_nonneg⟩ :=
    statopia_math_node_1861819959_faf8835a P X mean varianceSq fourthMoment
      hX_meas hX_indep hX_ident hfourth_integrable hmean hvariance hfourth
  have hGlaw : Measure.map G P =
      gaussianReal 0 ⟨fourthMoment - varianceSq ^ 2, sub_nonneg.mpr hgap.le⟩ := by
    ext s hs
    rw [Measure.map_apply hG_meas hs]
    simpa using hG_law.measure_mem_eq hs
  have hvarpos : 0 < fourthMoment - varianceSq ^ 2 := sub_pos.mpr hgap
  have hvarid : ∫ ω, ((X 0 ω - mean) ^ 2) ^ 2 ∂P - varianceSq ^ 2
      = fourthMoment - varianceSq ^ 2 := by
    have h1 : (∫ ω, ((X 0 ω - mean) ^ 2) ^ 2 ∂P) = fourthMoment := hY_sq
    rw [h1]
  have hWeak := statopia_math_node_41308827_d98f99c7 (Ω := Ω) P
    (fun i ω => (X i ω - mean) ^ 2) varianceSq (fourthMoment - varianceSq ^ 2)
    hY_meas hY_indep hY_ident hY_memLp hY_mean hvarpos hvarid
  have hWeak' : Statlib.StatFoundation.Convergence.WeakConvergence
      (fun n : ℕ => ⟨Measure.map (fun ω =>
        (Real.sqrt (n : ℝ))⁻¹ * ∑ i ∈ Finset.range n,
          ((X i ω - mean) ^ 2 - varianceSq)) P,
        Measure.isProbabilityMeasure_map (by measurability)⟩)
      ⟨Measure.map G P, Measure.isProbabilityMeasure_map hG_meas.aemeasurable⟩ := by
    simpa only [hGlaw] using hWeak
  exact Statlib.StatFoundation.Convergence.tendstoInDistribution_of_weakConvergence_law P
    (fun n ω => (Real.sqrt (n : ℝ))⁻¹ * ∑ i ∈ Finset.range n,
      ((X i ω - mean) ^ 2 - varianceSq)) G
    (fun n => by measurability) hG_meas.aemeasurable hWeak'
  /- @proof-region region.target-node.session.515998652d59d2e1 end -/
