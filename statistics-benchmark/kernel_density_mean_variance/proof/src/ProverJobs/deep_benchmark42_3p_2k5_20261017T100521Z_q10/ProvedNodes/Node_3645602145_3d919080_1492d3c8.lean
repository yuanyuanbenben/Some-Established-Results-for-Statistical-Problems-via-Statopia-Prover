import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q10.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q10.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q10.ProvedNodes.Node_710480633_ddaff62b_787260ba

open MeasureTheory ProbabilityTheory
set_option maxRecDepth 10000

open MeasureTheory ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_3645602145_3d919080 : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 1 ≤ n)
    (X : Fin n → Ω → ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun (β := fun _ ↦ ℝ) X P)
    (p : ℝ → ℝ) (hp_meas : Measurable p)
    (hX_law : ∀ i,
      HasLaw (X i) ((volume : Measure ℝ).withDensity (fun y : ℝ ↦ ENNReal.ofReal (p y))) P)
        (pmax : ℝ) (hpmax : 0 ≤ pmax)
        (hp_nonneg : ∀ᵐ y ∂volume, 0 ≤ p y)
        (hp_bound : ∀ᵐ y ∂volume, p y ≤ pmax)
        (K : ℝ → ℝ) (hK_meas : Measurable K)
        (hK_nonneg : ∀ u : ℝ, 0 ≤ K u)
        (hK_int : Integrable K volume)
        (hK_sq_int : Integrable (fun u : ℝ ↦ (K u) ^ (2 : ℕ)) volume)
        (x h : ℝ) (hh : 0 < h),
          Integrable (fun u : ℝ ↦ K u * p (x + h * u)) volume ∧
            Integrable (fun u : ℝ ↦ (K u) ^ (2 : ℕ) * p (x + h * u)) volume ∧
              (∀ i j : Fin n,
                Integrable (fun ω : Ω ↦ K ((X i ω - x) / h) * K ((X j ω - x) / h)) P ∧
                  (∫ ω, K ((X i ω - x) / h) * K ((X j ω - x) / h) ∂P
                    = if i = j then h * (∫ u, (K u) ^ (2 : ℕ) * p (x + h * u) ∂volume)
                      else h ^ (2 : ℕ) * (∫ u, K u * p (x + h * u) ∂volume) ^ (2 : ℕ))) := by
  /- @proof-region region.target-node.session.bfb0abc3df95fa77 begin -/
  intro Ω _ P _ n hn X hX_meas hX_indep p hp_meas hX_law pmax hpmax hp_nonneg hp_bound K hK_meas hK_nonneg hK_int hK_sq_int x h hh
  have hK2_meas : Measurable (fun u : ℝ => (K u) ^ (2 : ℕ)) := by
    simpa only [sq] using hK_meas.mul hK_meas
  have htrK : ∀ i : Fin n,
      Integrable (fun u : ℝ => K u * p (x + h * u)) volume ∧
        Integrable (fun ω : Ω => K ((X i ω - x) / h)) P ∧
        (∫ ω, K ((X i ω - x) / h) ∂P = h * ∫ u, K u * p (x + h * u) ∂volume) := by
    intro i
    have hmain := statopia_math_node_710480633_ddaff62b P p hp_meas pmax hpmax hp_nonneg hp_bound (X i) (hX_meas i) (hX_law i) K hK_meas hK_int x h hh
    exact ⟨hmain.2.1, hmain.2.2.1, hmain.2.2.2⟩
  have htrK2 : ∀ i : Fin n,
      Integrable (fun u : ℝ => (K u) ^ (2 : ℕ) * p (x + h * u)) volume ∧
        Integrable (fun ω : Ω => (K ((X i ω - x) / h)) ^ (2 : ℕ)) P ∧
        (∫ ω, (K ((X i ω - x) / h)) ^ (2 : ℕ) ∂P = h * ∫ u, (K u) ^ (2 : ℕ) * p (x + h * u) ∂volume) := by
    intro i
    have hmain := statopia_math_node_710480633_ddaff62b P p hp_meas pmax hpmax hp_nonneg hp_bound (X i) (hX_meas i) (hX_law i) (fun u : ℝ => (K u) ^ (2 : ℕ)) hK2_meas hK_sq_int x h hh
    exact ⟨hmain.2.1, hmain.2.2.1, hmain.2.2.2⟩
  have hA_int : Integrable (fun u : ℝ => K u * p (x + h * u)) volume := (htrK ⟨0, by omega⟩).1
  have hB_int : Integrable (fun u : ℝ => (K u) ^ (2 : ℕ) * p (x + h * u)) volume := (htrK2 ⟨0, by omega⟩).1
  refine ⟨hA_int, hB_int, ?_⟩
  intro i j
  by_cases hij : i = j
  · subst j
    have hint : Integrable (fun ω : Ω => K ((X i ω - x) / h) * K ((X i ω - x) / h)) P := by
      simpa only [sq] using (htrK2 i).2.1
    refine ⟨hint, ?_⟩
    have hsq : (fun ω : Ω => K ((X i ω - x) / h) * K ((X i ω - x) / h)) = (fun ω => (K ((X i ω - x) / h)) ^ (2 : ℕ)) := by
      funext ω; rw [sq]
    rw [hsq, (htrK2 i).2.2, if_pos rfl]
  · have hXij : IndepFun (X i) (X j) P := hX_indep.indepFun hij
    have hψ : Measurable (fun y : ℝ => K ((y - x) / h)) := by measurability
    have hYind : IndepFun (fun ω : Ω => K ((X i ω - x) / h)) (fun ω : Ω => K ((X j ω - x) / h)) P := by
      have hcomp := hXij.comp hψ hψ
      simpa only [Function.comp_def] using hcomp
    have hprodint : Integrable (fun ω : Ω => K ((X i ω - x) / h) * K ((X j ω - x) / h)) P :=
      hYind.integrable_mul (htrK i).2.1 (htrK j).2.1
    refine ⟨hprodint, ?_⟩
    have hprod : (∫ ω, K ((X i ω - x) / h) * K ((X j ω - x) / h) ∂P)
        = (∫ ω, K ((X i ω - x) / h) ∂P) * ∫ ω, K ((X j ω - x) / h) ∂P :=
      hYind.integral_mul_eq_mul_integral (htrK i).2.1.aestronglyMeasurable (htrK j).2.1.aestronglyMeasurable
    rw [hprod, (htrK i).2.2, (htrK j).2.2, if_neg hij]
    ring
  /- @proof-region region.target-node.session.bfb0abc3df95fa77 end -/
