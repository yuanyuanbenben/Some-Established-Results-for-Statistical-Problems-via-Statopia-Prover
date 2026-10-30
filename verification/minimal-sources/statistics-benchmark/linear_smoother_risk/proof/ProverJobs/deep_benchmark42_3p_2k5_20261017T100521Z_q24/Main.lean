import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q24.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q24.ProvedNodes
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q24.Base

open MeasureTheory

theorem linear_smoother_risk
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 1 ≤ n)
    (f : Fin n → ℝ)
    (xi : Ω → Fin n → ℝ)
    (hxi_meas : Measurable xi)
    (hxi_sq_int : Integrable (fun ω ↦ ∑ i, (xi ω i) ^ 2) P)
    (sigma2 : ℝ) (hsigma2 : 0 ≤ sigma2)
    (hxi_mean : ∀ i, ∫ ω, xi ω i ∂P = 0)
    (hxi_cov : ∀ i j,
      ∫ ω, xi ω i * xi ω j ∂P = if i = j then sigma2 else 0)
    (S : Matrix (Fin n) (Fin n) ℝ) :
    let Y : Ω → Fin n → ℝ := fun ω i ↦ f i + xi ω i
    let estimate : Ω → Fin n → ℝ := fun ω ↦ S.mulVec (Y ω)
    let normSq : (Fin n → ℝ) → ℝ := fun v ↦
      (n : ℝ)⁻¹ * ∑ i, (v i) ^ 2
    ∫ ω, normSq (estimate ω - f) ∂P =
      normSq (S.mulVec f - f) +
        sigma2 * (n : ℝ)⁻¹ * Matrix.trace (S.transpose * S)
:= by
  /- @proof-region region.root.a27c18c756a0 begin -/
  have hsub : ∀ (u : Fin n → ℝ) (i : Fin n), (u - f) i = u i - f i := fun u i => rfl
  have hmulVec : ∀ (v : Fin n → ℝ) (i : Fin n), (S.mulVec v) i = ∑ j, S i j * v j := by
    intro v i
    rfl
  have hpoint : ∀ (ω : Ω) (i : Fin n),
      (S.mulVec (fun j => f j + xi ω j) - f) i
        = ((S.mulVec f - f) i) + ∑ j, S i j * xi ω j := by
    intro ω i
    simp only [hsub, hmulVec, mul_add, Finset.sum_add_distrib]
    ring
  have hxi_j : ∀ j : Fin n, Measurable (fun ω : Ω => xi ω j) :=
    fun j => (measurable_pi_apply j).comp hxi_meas
  have hmeasL : ∀ i : Fin n, Measurable (fun ω : Ω => ∑ j, S i j * xi ω j) := by
    intro i
    have hconst : ∀ j : Fin n, Measurable (fun _ : Ω => S i j) := fun j => measurable_const
    have h := Finset.measurable_sum (f := fun j (ω : Ω) => S i j * xi ω j)
      (Finset.univ : Finset (Fin n))
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => (hconst j).mul (hxi_j j))
    simpa using h
  have hLint : ∀ i : Fin n, Integrable (fun ω : Ω => (∑ j, S i j * xi ω j) ^ 2) P := by
    intro i
    have hdom : Integrable (fun ω : Ω => (∑ j, (S i j) ^ 2) * ∑ j, (xi ω j) ^ 2) P :=
      hxi_sq_int.const_mul _
    have hmeas : Measurable (fun ω : Ω => (∑ j, S i j * xi ω j) ^ 2) := by
      simpa only [pow_two] using (hmeasL i).mul (hmeasL i)
    refine hdom.mono hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    have hS : (0 : ℝ) ≤ ∑ j, (S i j) ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
    have hx : (0 : ℝ) ≤ ∑ j, (xi ω j) ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
    have h1 : ‖(∑ j, S i j * xi ω j) ^ 2‖ = (∑ j, S i j * xi ω j) ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h2 : ‖(∑ j, (S i j) ^ 2) * ∑ j, (xi ω j) ^ 2‖
        = (∑ j, (S i j) ^ 2) * ∑ j, (xi ω j) ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hS hx)]
    rw [h1, h2]
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => S i j) (fun j => xi ω j)
  have hEint : ∀ i : Fin n,
      Integrable (fun ω : Ω => ((S.mulVec (fun j => f j + xi ω j) - f) i) ^ 2) P := by
    intro i
    have hgoal : (fun ω : Ω => ((S.mulVec (fun j => f j + xi ω j) - f) i) ^ 2)
        = fun ω : Ω => (((S.mulVec f - f) i) + ∑ j, S i j * xi ω j) ^ 2 := by
      funext ω
      rw [hpoint ω i]
    rw [hgoal]
    have hdom : Integrable
        (fun ω : Ω => 2 * ((S.mulVec f - f) i) ^ 2 + 2 * (∑ j, S i j * xi ω j) ^ 2) P :=
      (integrable_const (2 * ((S.mulVec f - f) i) ^ 2)).add ((hLint i).const_mul 2)
    have hc : Measurable (fun ω : Ω => ((S.mulVec f - f) i) + ∑ j, S i j * xi ω j) :=
      measurable_const.add (hmeasL i)
    have hmeas : Measurable
        (fun ω : Ω => (((S.mulVec f - f) i) + ∑ j, S i j * xi ω j) ^ 2) := by
      simpa only [pow_two] using hc.mul hc
    refine hdom.mono hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    have h1 : ‖(((S.mulVec f - f) i) + ∑ j, S i j * xi ω j) ^ 2‖
        = (((S.mulVec f - f) i) + ∑ j, S i j * xi ω j) ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h2 : ‖2 * ((S.mulVec f - f) i) ^ 2 + 2 * (∑ j, S i j * xi ω j) ^ 2‖
        = 2 * ((S.mulVec f - f) i) ^ 2 + 2 * (∑ j, S i j * xi ω j) ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [h1, h2]
    nlinarith [sq_nonneg (((S.mulVec f - f) i) - ∑ j, S i j * xi ω j)]
  have hpull : ∫ ω, (n : ℝ)⁻¹ * ∑ i, ((S.mulVec (fun j => f j + xi ω j) - f) i) ^ 2 ∂P
      = (n : ℝ)⁻¹ * ∫ ω, ∑ i, ((S.mulVec (fun j => f j + xi ω j) - f) i) ^ 2 ∂P :=
    integral_const_mul (n : ℝ)⁻¹ _
  have hsplit : ∫ ω, ∑ i, ((S.mulVec (fun j => f j + xi ω j) - f) i) ^ 2 ∂P
      = ∑ i, ∫ ω, ((S.mulVec (fun j => f j + xi ω j) - f) i) ^ 2 ∂P := by
    have h := integral_finset_sum (Finset.univ : Finset (Fin n))
      (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hEint i)
    simpa using h
  have hcoord : ∀ i : Fin n,
      ∫ ω, ((S.mulVec (fun j => f j + xi ω j) - f) i) ^ 2 ∂P
        = ((S.mulVec f - f) i) ^ 2 + sigma2 * ∑ j, (S i j) ^ 2 :=
    fun i =>
      statopia_math_node_667819182_4a89c02f P n hn f xi hxi_meas hxi_sq_int sigma2 hsigma2
        hxi_mean hxi_cov S i
  have hcoordsum : (∑ i, ∫ ω, ((S.mulVec (fun j => f j + xi ω j) - f) i) ^ 2 ∂P)
      = ∑ i, (((S.mulVec f - f) i) ^ 2 + sigma2 * ∑ j, (S i j) ^ 2) :=
    Finset.sum_congr rfl (fun i _ => hcoord i)
  have hsplit2 : (∑ i, (((S.mulVec f - f) i) ^ 2 + sigma2 * ∑ j, (S i j) ^ 2))
      = ∑ i, ((S.mulVec f - f) i) ^ 2 + sigma2 * ∑ i, ∑ j, (S i j) ^ 2 := by
    rw [Finset.sum_add_distrib]
    simp only [Finset.mul_sum]
  have hfinal : (n : ℝ)⁻¹ * (∑ i, ((S.mulVec f - f) i) ^ 2 + sigma2 * ∑ i, ∑ j, (S i j) ^ 2)
      = (n : ℝ)⁻¹ * ∑ i, ((S.mulVec f - f) i) ^ 2
        + sigma2 * (n : ℝ)⁻¹ * Matrix.trace (S.transpose * S) := by
    rw [statopia_math_node_1492331787_7aa815be n S]
    ring
  have hstep2 : (n : ℝ)⁻¹ * ∫ ω, ∑ i, ((S.mulVec (fun j => f j + xi ω j) - f) i) ^ 2 ∂P
      = (n : ℝ)⁻¹ * (∑ i, ((S.mulVec f - f) i) ^ 2 + sigma2 * ∑ i, ∑ j, (S i j) ^ 2) := by
    rw [hsplit, hcoordsum, hsplit2]
  exact hpull.trans (hstep2.trans hfinal)
  /- @proof-region region.root.a27c18c756a0 end -/
