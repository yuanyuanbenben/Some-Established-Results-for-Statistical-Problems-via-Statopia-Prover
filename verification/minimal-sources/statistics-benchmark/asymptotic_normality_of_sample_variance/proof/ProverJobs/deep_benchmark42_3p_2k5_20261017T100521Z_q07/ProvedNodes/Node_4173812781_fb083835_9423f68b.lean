import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q07.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q07.Base

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

set_option autoImplicit false in
theorem statopia_math_node_4173812781_fb083835 : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ)
    (mean varianceSq : ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X P)
    (hX_ident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hfourth_integrable : Integrable (fun ω => |X 0 ω| ^ 4) P)
    (hmean : ∫ ω, X 0 ω ∂P = mean)
    (hvariance : ∫ ω, (X 0 ω - mean) ^ 2 ∂P = varianceSq),
    0 ≤ varianceSq ∧
      ∀ i : ℕ,
        Measurable (fun ω => X i ω - mean) ∧
        MemLp (fun ω => X i ω - mean) 2 P ∧
        (∫ ω, (X i ω - mean) ∂P = 0) ∧
        (∫ ω, (X i ω - mean) ^ 2 ∂P = varianceSq) ∧
        iIndepFun (fun i ω => X i ω - mean) P ∧
        (∀ a b : ℕ, a ≠ b →
          IndepFun (fun ω => X a ω - mean) (fun ω => X b ω - mean) P) := by
  /- @proof-region region.target-node.session.12a7a8e0711844ec begin -/
  intro Ω _ P _ X mean varianceSq hX_meas hX_indep hX_ident hfourth_integrable hmean hvariance
  have hsq_bound : ∀ x : ℝ, x ^ 2 ≤ 1 + |x| ^ 4 := by
    intro x
    rw [← sq_abs]
    nlinarith [sq_nonneg (|x| ^ 2 - 1 / 2)]
  have hlin : ∀ x : ℝ, |x| ≤ 1 + |x| ^ 4 := by
    intro x
    nlinarith [sq_nonneg (|x| ^ 2 - 1 / 2), sq_nonneg (|x| - 1 / 2)]
  have hZ_sq_bound : ∀ x : ℝ, (x - mean) ^ 2 ≤
      (1 + |x| ^ 4 + mean ^ 2) + (1 + |x| ^ 4 + mean ^ 2) := by
    intro x
    have h1 : x ^ 2 ≤ 1 + |x| ^ 4 := hsq_bound x
    nlinarith [h1, sq_nonneg (x + mean)]
  have hsub_meas : Measurable (fun x : ℝ => x - mean) :=
    measurable_id.sub measurable_const
  have hZ0_meas : Measurable (fun ω => X 0 ω - mean) :=
    (hX_meas 0).sub measurable_const
  have hZ0sq_meas : Measurable (fun ω => (X 0 ω - mean) ^ 2) := by
    simpa [sq] using hZ0_meas.mul hZ0_meas
  have hgX : Integrable (fun ω => 1 + |X 0 ω| ^ 4) P :=
    (integrable_const (1 : ℝ)).add hfourth_integrable
  have hX0_int : Integrable (X 0) P := by
    refine Integrable.mono' hgX (hX_meas 0).aestronglyMeasurable (Filter.Eventually.of_forall ?_)
    intro ω
    simpa [Real.norm_eq_abs] using hlin (X 0 ω)
  have h2 : Integrable (fun ω => 1 + |X 0 ω| ^ 4 + mean ^ 2) P :=
    hgX.add (integrable_const (mean ^ 2))
  have hgZ : Integrable
      (fun ω => (1 + |X 0 ω| ^ 4 + mean ^ 2) + (1 + |X 0 ω| ^ 4 + mean ^ 2)) P :=
    h2.add h2
  have hZ0_sq_int : Integrable (fun ω => (X 0 ω - mean) ^ 2) P := by
    refine Integrable.mono' hgZ hZ0sq_meas.aestronglyMeasurable (Filter.Eventually.of_forall ?_)
    intro ω
    have hb := hZ_sq_bound (X 0 ω)
    simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (X 0 ω - mean))] using hb
  have hZ0_memLp : MemLp (fun ω => X 0 ω - mean) 2 P :=
    (memLp_two_iff_integrable_sq hZ0_meas.aestronglyMeasurable).mpr hZ0_sq_int
  have hZ0_integral : ∫ ω, (X 0 ω - mean) ∂P = 0 := by
    rw [integral_sub hX0_int (integrable_const (mean : ℝ)), hmean, integral_const]
    simp [Measure.real, measure_univ]
  have hZ_indep : iIndepFun (fun i ω => X i ω - mean) P := by
    simpa [Function.comp] using
      hX_indep.comp (fun _ x => x - mean) (fun _ => hsub_meas)
  refine ⟨?_, ?_⟩
  · rw [← hvariance]
    exact integral_nonneg (fun ω => sq_nonneg (X 0 ω - mean))
  · intro i
    have hZi_meas : Measurable (fun ω => X i ω - mean) :=
      (hX_meas i).sub measurable_const
    have hZi_ident : IdentDistrib (fun ω => X i ω - mean) (fun ω => X 0 ω - mean) P P := by
      simpa [Function.comp] using (hX_ident i).comp hsub_meas
    have hu : Measurable (fun x : ℝ => x ^ 2) := by
      simpa [sq] using (measurable_id.mul measurable_id : Measurable (fun x : ℝ => x * x))
    refine ⟨hZi_meas, ?_, ?_, ?_, hZ_indep, ?_⟩
    · exact hZi_ident.memLp_iff.mpr hZ0_memLp
    · rw [hZi_ident.integral_eq, hZ0_integral]
    · have hZi_sq_ident : IdentDistrib (fun ω => (X i ω - mean) ^ 2)
          (fun ω => (X 0 ω - mean) ^ 2) P P := by
        simpa [Function.comp] using hZi_ident.comp hu
      rw [hZi_sq_ident.integral_eq, hvariance]
    · intro a b hab
      simpa using hZ_indep.indepFun hab
  /- @proof-region region.target-node.session.12a7a8e0711844ec end -/
