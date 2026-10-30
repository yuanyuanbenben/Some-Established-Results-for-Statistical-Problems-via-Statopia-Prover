import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q07.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q07.ProvedNodes
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q07.Base

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

theorem asymptotic_normality_of_sample_variance
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ)
    (mean varianceSq fourthMoment : ℝ)
    (G : Ω → ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X P)
    (hX_ident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hfourth_integrable : Integrable (fun ω ↦ |X 0 ω| ^ 4) P)
    (hmean : ∫ ω, X 0 ω ∂P = mean)
    (hvariance :
      ∫ ω, (X 0 ω - mean) ^ 2 ∂P = varianceSq)
    (hfourth :
      ∫ ω, (X 0 ω - mean) ^ 4 ∂P = fourthMoment)
    (hgap : varianceSq ^ 2 < fourthMoment)
    (hG_meas : Measurable G)
    (hG_law :
      IdentDistrib G id P
        (gaussianReal 0
          ⟨fourthMoment - varianceSq ^ 2, sub_nonneg.mpr hgap.le⟩)) :
    let Xbar : ℕ → Ω → ℝ :=
      fun n ω ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, X i ω
    let V : ℕ → Ω → ℝ :=
      fun n ω ↦
        (n : ℝ)⁻¹ *
          ∑ i ∈ Finset.range n, (X i ω - Xbar n ω) ^ 2
    TendstoInDistribution
      (fun (n : ℕ) ω ↦ Real.sqrt (n : ℝ) * (V n ω - varianceSq))
      atTop G P
:= by
  /- @proof-region region.root.eb0570780931 begin -/
  dsimp only
  let clt : ℕ → Ω → ℝ := fun n ω =>
    (Real.sqrt (n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, ((X i ω - mean) ^ 2 - varianceSq)
  let corr : ℕ → Ω → ℝ := fun n ω =>
    -(Real.sqrt (n : ℝ) * (((n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, X i ω)) - mean) ^ 2)
  have hCLT : TendstoInDistribution clt atTop G P :=
    statopia_math_node_3270619228_393e5828 P X mean varianceSq fourthMoment G
      hX_meas hX_indep hX_ident hfourth_integrable hmean hvariance hfourth hgap hG_meas hG_law
  have hcorr := statopia_math_node_3098910026_8cbaa9f6 P X mean varianceSq
    hX_meas hX_indep hX_ident hfourth_integrable hmean hvariance
  dsimp only at hcorr
  obtain ⟨-, -, -, hTIM⟩ := hcorr
  have hmeas : ∀ n, AEMeasurable (corr n) P := by
    intro n
    have hsum : Measurable (fun ω => ∑ i ∈ Finset.range n, X i ω) :=
      Finset.measurable_sum _ (fun i _ => hX_meas i)
    have hD : Measurable (fun ω => (n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, X i ω) - mean) :=
      (measurable_const.mul hsum).sub measurable_const
    exact (measurable_const.mul (hD.pow_const 2)).neg.aemeasurable
  have hadd : TendstoInDistribution (fun n => clt n + corr n) atTop (fun ω => G ω + 0) P :=
    Statlib.StatFoundation.Convergence.tendstoInDistribution_add_of_tendstoInMeasure_const
      hCLT hTIM hmeas
  have hadd' : TendstoInDistribution (fun n => clt n + corr n) atTop G P :=
    Statlib.StatFoundation.Convergence.tendstoInDistribution_congr_right
      (Eventually.of_forall (fun ω => by simp)) hadd
  have hbridge := statopia_math_node_2992835122_67aeacbc X mean varianceSq
  dsimp only at hbridge
  refine Statlib.StatFoundation.Convergence.tendstoInDistribution_congr_left
    (X := fun n => clt n + corr n) ?_ hadd'
  intro n
  filter_upwards with ω
  simp only [Pi.add_apply, clt, corr]
  exact (sub_eq_add_neg _ _).symm.trans (hbridge n ω).symm
  /- @proof-region region.root.eb0570780931 end -/
