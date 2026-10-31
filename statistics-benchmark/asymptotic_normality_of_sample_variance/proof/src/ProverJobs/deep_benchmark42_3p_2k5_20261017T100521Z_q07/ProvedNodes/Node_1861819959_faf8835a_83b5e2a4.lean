import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q07.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q07.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q07.ProvedNodes.Node_4173812781_fb083835_9423f68b

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

set_option autoImplicit false in
theorem statopia_math_node_1861819959_faf8835a : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ)
    (mean varianceSq fourthMoment : ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X P)
    (hX_ident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hfourth_integrable : Integrable (fun ω => |X 0 ω| ^ 4) P)
    (hmean : ∫ ω, X 0 ω ∂P = mean)
    (hvariance : ∫ ω, (X 0 ω - mean) ^ 2 ∂P = varianceSq)
    (hfourth : ∫ ω, (X 0 ω - mean) ^ 4 ∂P = fourthMoment),
    let Y : ℕ → Ω → ℝ := fun i ω => (X i ω - mean) ^ 2
    (∀ i : ℕ, Measurable (Y i)) ∧
      iIndepFun Y P ∧
      (∀ i : ℕ, IdentDistrib (Y i) (Y 0) P P) ∧
      MemLp (Y 0) 2 P ∧
      (∫ ω, (Y 0 ω) ^ 2 ∂P = fourthMoment) ∧
      (∀ i : ℕ, ∫ ω, Y i ω ∂P = varianceSq) ∧
      (variance (Y 0) P =
        (∫ ω, (Y 0 ω) ^ 2 ∂P) - (∫ ω, Y 0 ω ∂P) ^ 2) ∧
      (variance (Y 0) P = fourthMoment - varianceSq ^ 2) ∧
      (0 ≤ variance (Y 0) P) := by
  /- @proof-region region.target-node.session.eb1cac06c7152e2a begin -/
  intro Ω _ P _ X mean varianceSq fourthMoment hX_meas hX_indep hX_ident hfourth_integrable hmean hvariance hfourth
  obtain ⟨_, hZ⟩ :=
    statopia_math_node_4173812781_fb083835 P X mean varianceSq hX_meas hX_indep hX_ident
      hfourth_integrable hmean hvariance
  dsimp only
  have hpt : ∀ ω : Ω, ((X 0 ω - mean) ^ 2) ^ 2 = (X 0 ω - mean) ^ 4 := fun ω => by ring
  have hX0 : Measurable (fun ω : Ω => X 0 ω - mean) := (hZ 0).1
  have hmeas : ∀ i : ℕ, Measurable (fun ω : Ω => (X i ω - mean) ^ 2) := fun i => by fun_prop
  have hindep : iIndepFun (fun i ω => (X i ω - mean) ^ 2) P :=
    hX_indep.comp (fun _ x => (x - mean) ^ 2) (fun _ => by fun_prop)
  have hident : ∀ i : ℕ,
      IdentDistrib (fun ω : Ω => (X i ω - mean) ^ 2) (fun ω : Ω => (X 0 ω - mean) ^ 2) P P :=
    fun i => (hX_ident i).comp (u := fun x => (x - mean) ^ 2) (by fun_prop)
  have hmeanY : ∀ i : ℕ, ∫ ω, (X i ω - mean) ^ 2 ∂P = varianceSq := fun i => (hZ i).2.2.2.1
  have hY0int : Integrable (fun ω : Ω => (X 0 ω - mean) ^ 2) P :=
    (MeasureTheory.memLp_two_iff_integrable_sq hX0.aestronglyMeasurable).mp (hZ 0).2.1
  have hbound : ∀ ω : Ω, |(X 0 ω - mean) ^ 4| ≤ 8 * (|X 0 ω| ^ 4 + |mean| ^ 4) := by
    intro ω
    have h1 : |X 0 ω - mean| ≤ |X 0 ω| + |mean| := by
      have h := abs_add_le (X 0 ω) (-mean)
      simpa [sub_eq_add_neg] using h
    have h2 : (X 0 ω - mean) ^ 4 = |X 0 ω - mean| ^ 4 := by
      rw [← abs_pow, abs_of_nonneg (by positivity)]
    rw [h2, abs_of_nonneg (by positivity)]
    calc |X 0 ω - mean| ^ 4 ≤ (|X 0 ω| + |mean|) ^ 4 := by gcongr
      _ ≤ 8 * (|X 0 ω| ^ 4 + |mean| ^ 4) := by
          have key : (0 : ℝ) ≤ (|X 0 ω| - |mean|) ^ 2 *
              (6 * (|X 0 ω| + |mean|) ^ 2 + (|X 0 ω| - |mean|) ^ 2) := by positivity
          nlinarith [key]
  have h4int : Integrable (fun ω : Ω => (X 0 ω - mean) ^ 4) P := by
    have hg : Integrable (fun ω : Ω => 8 * (|X 0 ω| ^ 4 + |mean| ^ 4)) P := by
      have h1 : Integrable (fun ω : Ω => |X 0 ω| ^ 4 + |mean| ^ 4) P :=
        hfourth_integrable.add (integrable_const (|mean| ^ 4))
      simpa [smul_eq_mul, mul_add] using h1.const_mul 8
    have hf : AEStronglyMeasurable (fun ω : Ω => (X 0 ω - mean) ^ 4) P :=
      (by fun_prop : Measurable (fun ω : Ω => (X 0 ω - mean) ^ 4)).aestronglyMeasurable
    refine Integrable.mono' hg hf ?_
    filter_upwards with ω
    simpa only [Real.norm_eq_abs] using hbound ω
  have hsq_int : Integrable (fun ω : Ω => ((X 0 ω - mean) ^ 2) ^ 2) P := by
    simpa only [hpt] using h4int
  have hmemLp : MemLp (fun ω : Ω => (X 0 ω - mean) ^ 2) 2 P :=
    (MeasureTheory.memLp_two_iff_integrable_sq (hmeas 0).aestronglyMeasurable).mpr hsq_int
  have hsq_integral : ∫ ω, ((X 0 ω - mean) ^ 2) ^ 2 ∂P = fourthMoment := by
    simp only [hpt, hfourth]
  have hvar1 : variance (fun ω : Ω => (X 0 ω - mean) ^ 2) P
      = ∫ ω, ((X 0 ω - mean) ^ 2) ^ 2 ∂P - (∫ ω, (X 0 ω - mean) ^ 2 ∂P) ^ 2 :=
    variance_eq_sub hmemLp
  have hvar2 : variance (fun ω : Ω => (X 0 ω - mean) ^ 2) P = fourthMoment - varianceSq ^ 2 := by
    rw [hvar1, hsq_integral, hmeanY 0]
  have hvar3 : 0 ≤ variance (fun ω : Ω => (X 0 ω - mean) ^ 2) P := variance_nonneg _ _
  exact ⟨hmeas, hindep, hident, hmemLp, hsq_integral, hmeanY, hvar1, hvar2, hvar3⟩
  /- @proof-region region.target-node.session.eb1cac06c7152e2a end -/
