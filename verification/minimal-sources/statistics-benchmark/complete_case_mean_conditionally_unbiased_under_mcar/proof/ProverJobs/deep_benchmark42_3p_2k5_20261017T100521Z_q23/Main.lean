import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q23.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q23.ProvedNodes
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q23.Base

open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem complete_case_mean_conditionally_unbiased_under_mcar
    {Ω : Type*}
    [MeasurableSpace Ω]
    (P : Measure Ω)
    [IsProbabilityMeasure P]
    (n : ℕ)
    (hn : 1 ≤ n)
    (μ : ℝ)
    (Y : Fin n → Ω → ℝ)
    (R : Fin n → Ω → Bool)
    (hYmeas : ∀ i, Measurable (Y i))
    (hYint : ∀ i, Integrable (Y i) P)
    (hYmean : ∀ i, ∫ ω, Y i ω ∂P = μ)
    (hRmeas : ∀ i, Measurable (R i))
    (hIndep :
      IndepFun (fun ω i ↦ R i ω) (fun ω i ↦ Y i ω) P) :
    let K : Ω → ℕ := fun ω ↦ ∑ i, if R i ω then 1 else 0
    let μhat : Ω → ℝ := fun ω ↦
      if 0 < K ω then
        (∑ i, if R i ω then Y i ω else 0) / (K ω : ℝ)
      else 0
    0 < P {ω | 0 < K ω} →
      (∫ ω, if 0 < K ω then μhat ω else 0 ∂P) /
          (P {ω | 0 < K ω}).toReal = μ
:= by
  /- @proof-region region.root.006d9e291629 begin -/
  dsimp only
  intro hA
  have hW := statopia_math_node_1923180180_68958706 (Ω := Ω) n R hRmeas
  dsimp only at hW
  obtain ⟨_, hXvec_meas, hpsi_meas, hw_meas, _, _, hw_abs, hA_meas, _⟩ := hW
  let K : Ω → ℕ := fun ω => ∑ i, if R i ω = true then (1:ℕ) else 0
  let psi : Fin n → (Fin n → Bool) → ℝ := fun i b =>
    if 0 < (∑ j, if b j = true then (1:ℕ) else 0) then
      ((if b i = true then (1:ℝ) else 0) / (↑(∑ j, if b j = true then (1:ℕ) else 0))) else 0
  let w : Fin n → Ω → ℝ := fun i ω => psi i (fun j => R j ω)
  have hYvec_meas : Measurable (fun ω j => Y j ω) := measurable_pi_iff.mpr hYmeas
  have hKpos : ∀ ω, 0 < K ω → (K ω : ℝ) ≠ 0 := by
    intro ω hω
    have h2 : (0:ℝ) < (K ω : ℝ) := by exact_mod_cast hω
    exact ne_of_gt h2
  have hKcast : ∀ ω, (K ω : ℝ) = ∑ i, (if R i ω = true then (1:ℝ) else 0) := by
    intro ω
    simp only [K]
    push_cast
    exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
  have hYsum : ∀ ω, (∑ i, if R i ω = true then Y i ω else 0)
      = ∑ i, (if R i ω = true then (1:ℝ) else 0) * Y i ω := by
    intro ω
    exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
  have hw_form : ∀ i ω, w i ω = if 0 < K ω then
      ((if R i ω = true then (1:ℝ) else 0) / (K ω : ℝ)) else 0 := by
    intro i ω
    simp only [w, psi, K]
  have hsum_w : ∀ ω, (∑ i, w i ω) = if 0 < K ω then (1:ℝ) else 0 := by
    intro ω
    by_cases hω : 0 < K ω
    · have h1 : (∑ i, w i ω)
          = ∑ i, (if R i ω = true then (1:ℝ) else 0) / (K ω : ℝ) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hw_form i ω, if_pos hω]
      rw [h1, ← Finset.sum_div, ← hKcast ω, div_self (hKpos ω hω), if_pos hω]
    · have h1 : (∑ i, w i ω) = ∑ i : Fin n, (0:ℝ) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hw_form i ω, if_neg hω]
      rw [h1, Finset.sum_const_zero, if_neg hω]
  have hpoint : ∀ ω, (if 0 < K ω then (if 0 < K ω then
      (∑ i, if R i ω = true then Y i ω else 0) / (K ω : ℝ) else 0) else 0)
      = ∑ i, w i ω * Y i ω := by
    intro ω
    by_cases hω : 0 < K ω
    · rw [if_pos hω, if_pos hω]
      rw [hYsum ω, Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hw_form i ω, if_pos hω]
      ring
    · rw [if_neg hω]
      have h1 : (∑ i, w i ω * Y i ω) = ∑ i : Fin n, (0:ℝ) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hw_form i ω, if_neg hω, zero_mul]
      rw [h1, Finset.sum_const_zero]
  have hw_int : ∀ i, Integrable (w i) P := by
    intro i
    have hb := Integrable.bdd_mul (μ := P) (f := w i) (g := fun _ => (1:ℝ)) (c := 1)
      (integrable_const (1:ℝ)) (hw_meas i).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hw_abs i ω)
    simpa using hb
  have hprod_int : ∀ i, Integrable (fun ω => w i ω * Y i ω) P := by
    intro i
    exact Integrable.bdd_mul (f := w i) (g := Y i) (c := 1) (hYint i)
      (hw_meas i).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hw_abs i ω)
  have hfac : ∀ i, ∫ ω, w i ω * Y i ω ∂P
      = (∫ ω, w i ω ∂P) * (∫ ω, Y i ω ∂P) := by
    intro i
    have hkey := ProbabilityTheory.IndepFun.integral_fun_comp_mul_comp
      (X := fun ω j => R j ω) (Y := fun ω j => Y j ω)
      (f := psi i) (g := fun y : Fin n → ℝ => y i) hIndep
      hXvec_meas.aemeasurable hYvec_meas.aemeasurable
      (hpsi_meas i).aestronglyMeasurable (measurable_pi_apply i).aestronglyMeasurable
    simpa [w] using hkey
  have h_ind : ∫ ω, (if 0 < K ω then (1:ℝ) else 0) ∂P = (P {ω | 0 < K ω}).toReal := by
    have hfun : (fun ω => if 0 < K ω then (1:ℝ) else 0)
        = {ω | 0 < K ω}.indicator (fun _ => (1:ℝ)) := by
      funext ω
      by_cases hω : 0 < K ω <;> simp [hω]
    rw [hfun, integral_indicator hA_meas]
    simp only [K, MeasureTheory.setIntegral_one_eq_measureReal, MeasureTheory.measureReal_def]
  have hApos : 0 < (P {ω | 0 < K ω}).toReal := by
    exact ENNReal.toReal_pos hA.ne' (measure_ne_top P _)
  have hmain1 : ∫ ω, (if 0 < K ω then (if 0 < K ω then
      (∑ i, if R i ω = true then Y i ω else 0) / (K ω : ℝ) else 0) else 0) ∂P
      = ∫ ω, (∑ i, w i ω * Y i ω) ∂P := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    exact hpoint ω
  have hmain2 : ∫ ω, (∑ i, w i ω * Y i ω) ∂P
      = ∑ i, ∫ ω, w i ω * Y i ω ∂P := by
    rw [integral_finset_sum]
    exact fun i _ => hprod_int i
  have hmain3 : (∑ i, ∫ ω, w i ω * Y i ω ∂P)
      = ∑ i, (∫ ω, w i ω ∂P) * μ := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hfac i, hYmean i]
  have hmain4 : (∑ i, (∫ ω, w i ω ∂P) * μ) = (∑ i, ∫ ω, w i ω ∂P) * μ := by
    exact (Finset.sum_mul Finset.univ (fun i => ∫ ω, w i ω ∂P) μ).symm
  have hmain5 : ∫ ω, (∑ i, w i ω) ∂P = ∑ i, ∫ ω, w i ω ∂P := by
    rw [integral_finset_sum]
    exact fun i _ => hw_int i
  have hmain6 : ∫ ω, (∑ i, w i ω) ∂P = ∫ ω, (if 0 < K ω then (1:ℝ) else 0) ∂P := by
    exact integral_congr_ae (Filter.Eventually.of_forall hsum_w)
  have hInt : ∫ ω, (if 0 < K ω then (if 0 < K ω then
      (∑ i, if R i ω = true then Y i ω else 0) / (K ω : ℝ) else 0) else 0) ∂P
      = (P {ω | 0 < K ω}).toReal * μ := by
    rw [hmain1, hmain2, hmain3, hmain4, ← hmain5, hmain6, h_ind]
  have hfinal : (∫ ω, (if 0 < K ω then (if 0 < K ω then
      (∑ i, if R i ω = true then Y i ω else 0) / (K ω : ℝ) else 0) else 0) ∂P)
      / (P {ω | 0 < K ω}).toReal = μ := by
    rw [hInt, div_eq_iff hApos.ne']
    exact mul_comm _ _
  exact hfinal
  /- @proof-region region.root.006d9e291629 end -/
