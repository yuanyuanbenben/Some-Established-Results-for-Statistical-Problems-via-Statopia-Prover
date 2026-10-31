import Statlib.StatFoundation.Concentration.ExponentialType.hoeffding_mgf_le
import Statlib.StatFoundation.Concentration.ExponentialType.hoeffding_sum_meas_abs_ge_le_two_exp
import ProverJobs.job_paper_b0cf39bbf6c845c9a6b30a5db43f8efa.Vocabulary
import ProverJobs.job_paper_b0cf39bbf6c845c9a6b30a5db43f8efa.Base

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal MeasureTheory Topology BigOperators
open Statlib.Imported
open Statlib.Imported.DPMModel

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal MeasureTheory Topology BigOperators
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_2358127001_21193b79 : ∀ (n : ℕ) (hn : 0 < n) (M : ℝ) (hM : 0 < M)
    (Ω : Fin n → Type*) [∀ i, MeasurableSpace (Ω i)]
    (μ : (i : Fin n) → Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (Y : (i : Fin n) → Ω i → ℝ) (hY : ∀ i, Measurable (Y i))
    (hYb : ∀ (i : Fin n) (ω : Ω i), |Y i ω| ≤ M)
    (t : ℝ) (ht : 0 < t),
    Measure.pi μ {ω : (i : Fin n) → Ω i |
        t ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, Y i (ω i)) -
             (n : ℝ)⁻¹ * (∑ i : Fin n, ∫ x, Y i x ∂(μ i))|}
      ≤ ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * t ^ 2 / (2 * M ^ 2))) := by
  /- @proof-region region.target-node.session.b6a4f8f479c52f18 begin -/
  intro n hn M hM Ω _ μ _ Y hY hYb t ht
  classical
  haveI : IsProbabilityMeasure (Measure.pi μ) := inferInstance
  set m : Fin n → ℝ := fun i => ∫ x, Y i x ∂μ i with hm
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hnt : (0 : ℝ) < (n : ℝ) * t := mul_pos hnpos ht
  have hmeas : ∀ i, Measurable (fun ω : (i : Fin n) → Ω i => Y i (ω i) - m i) := by
    intro i
    exact ((hY i).comp (measurable_pi_apply i)).sub
      (measurable_const : Measurable fun _ : (i : Fin n) → Ω i => m i)
  have hintY : ∀ i, Integrable (Y i) (μ i) := by
    intro i
    refine Integrable.of_bound (hY i).aestronglyMeasurable M ?_
    filter_upwards with x
    simpa [Real.norm_eq_abs] using hYb i x
  have hmabs : ∀ i, |m i| ≤ M := by
    intro i
    have hle : ∫ x, Y i x ∂μ i ≤ M := by
      have h := integral_mono_ae (hintY i) (integrable_const M)
        (Eventually.of_forall (fun x => (abs_le.mp (hYb i x)).2))
      simpa using h
    have hge : -M ≤ ∫ x, Y i x ∂μ i := by
      have h := integral_mono_ae (integrable_const (-M)) (hintY i)
        (Eventually.of_forall (fun x => (abs_le.mp (hYb i x)).1))
      simpa using h
    have hmval : m i = ∫ x, Y i x ∂μ i := by rw [hm]
    rw [hmval, abs_le]
    exact ⟨hge, hle⟩
  have hintPi : ∀ i, Integrable (fun x : (j : Fin n) → Ω j => Y i (x i)) (Measure.pi μ) := by
    intro i
    refine Integrable.of_bound ((hY i).comp (measurable_pi_apply i)).aestronglyMeasurable M ?_
    filter_upwards with x
    simpa [Real.norm_eq_abs] using hYb i (x i)
  have hmean : ∀ i, ∫ ω : (i : Fin n) → Ω i, (Y i (ω i) - m i) ∂(Measure.pi μ) = 0 := by
    intro i
    have hmap : Measure.map (Function.eval i) (Measure.pi μ) = μ i := by
      rw [Measure.pi_map_eval]
      simp
    have hcomp : ∫ ω : (i : Fin n) → Ω i, Y i (ω i) ∂(Measure.pi μ) = m i := by
      have hi : ∫ y, Y i y ∂(Measure.map (Function.eval i) (Measure.pi μ)) =
          ∫ x, Y i (Function.eval i x) ∂(Measure.pi μ) :=
        integral_map (measurable_pi_apply i).aemeasurable (hY i).aestronglyMeasurable
      rw [hmap] at hi
      rw [hm]
      exact hi.symm
    calc ∫ ω : (i : Fin n) → Ω i, (Y i (ω i) - m i) ∂(Measure.pi μ)
        = (∫ ω : (i : Fin n) → Ω i, Y i (ω i) ∂(Measure.pi μ)) -
            ∫ ω : (i : Fin n) → Ω i, m i ∂(Measure.pi μ) :=
          integral_sub (hintPi i) (integrable_const (m i))
      _ = m i - m i := by rw [hcomp]; simp
      _ = 0 := by ring
  have hindep : iIndepFun (fun i (x : (j : Fin n) → Ω j) => Y i (x i) - m i) (Measure.pi μ) := by
    unfold iIndepFun
    exact iIndepFun_pi
      (fun i => ((hY i).sub (measurable_const : Measurable fun _ : Ω i => m i)).aemeasurable)
  have hsub : ∀ i, HasSubgaussianMGF (fun x : (i : Fin n) → Ω i => Y i (x i) - m i)
      ⟨M ^ 2, sq_nonneg M⟩ (Measure.pi μ) := by
    intro i
    refine Statlib.StatFoundation.Concentration.ExponentialType.hoeffding_mgf_le (Measure.pi μ)
      (fun x : (i : Fin n) → Ω i => Y i (x i) - m i) (hmeas i) (-M - m i) (M - m i) ?_ (hmean i)
      ⟨M ^ 2, sq_nonneg M⟩ ?_
    · filter_upwards with x
      have h1 := abs_le.mp (hYb i (x i))
      have h2 := abs_le.mp (hmabs i)
      constructor <;> linarith
    · have hd : M - m i - (-M - m i) = 2 * M := by ring
      rw [hd]
      push_cast
      ring
  have hstep := Statlib.StatFoundation.Concentration.ExponentialType.hoeffding_sum_meas_abs_ge_le_two_exp
    (Measure.pi μ) n (fun i (x : (i : Fin n) → Ω i) => Y i (x i) - m i) (fun _ => M)
    (fun _ => ⟨M ^ 2, sq_nonneg M⟩) (fun i => rfl) hindep hsub ((n : ℝ) * t) hnt
  have hset : {ω : (i : Fin n) → Ω i |
        t ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, Y i (ω i)) -
             (n : ℝ)⁻¹ * (∑ i : Fin n, ∫ x, Y i x ∂μ i)|} ⊆
      {ω : (i : Fin n) → Ω i | (n : ℝ) * t ≤ |∑ i : Fin n, (Y i (ω i) - m i)|} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    have hsumsub : ∑ i : Fin n, (Y i (ω i) - m i) =
        (∑ i : Fin n, Y i (ω i)) - (∑ i : Fin n, m i) :=
      Finset.sum_sub_distrib (s := Finset.univ) (f := fun i => Y i (ω i)) (g := fun i => m i)
    have hmval : (∑ i : Fin n, m i) = (∑ i : Fin n, ∫ x, Y i x ∂μ i) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [hm]
    rw [hsumsub, hmval]
    have hfac : (n : ℝ)⁻¹ * (∑ i : Fin n, Y i (ω i)) -
          (n : ℝ)⁻¹ * (∑ i : Fin n, ∫ x, Y i x ∂μ i) =
        (n : ℝ)⁻¹ * ((∑ i : Fin n, Y i (ω i)) - (∑ i : Fin n, ∫ x, Y i x ∂μ i)) := by ring
    rw [hfac] at hω
    have habs : |(n : ℝ)⁻¹ * ((∑ i : Fin n, Y i (ω i)) -
          (∑ i : Fin n, ∫ x, Y i x ∂μ i))| =
        (n : ℝ)⁻¹ * |(∑ i : Fin n, Y i (ω i)) - (∑ i : Fin n, ∫ x, Y i x ∂μ i)| := by
      rw [abs_mul, abs_of_pos (inv_pos.mpr hnpos)]
    rw [habs] at hω
    have hmul := mul_le_mul_of_nonneg_left hω (le_of_lt hnpos)
    rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hnpos), one_mul] at hmul
  refine le_trans (measure_mono hset) ?_
  refine le_trans hstep ?_
  have hsum : ∑ i : Fin n, M ^ 2 = (n : ℝ) * M ^ 2 := by
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcalc : -((n : ℝ) * t) ^ 2 / (2 * ((n : ℝ) * M ^ 2)) =
      -(n : ℝ) * t ^ 2 / (2 * M ^ 2) := by
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    have hM0 : M ≠ 0 := ne_of_gt hM
    field_simp
  rw [hsum, hcalc]
  /- @proof-region region.target-node.session.b6a4f8f479c52f18 end -/

end Statlib.Imported
