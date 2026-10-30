import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q10.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q10.ProvedNodes
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q10.Base

open MeasureTheory ProbabilityTheory

theorem kernel_density_mean_variance
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 1 ≤ n)
    (X : Fin n → Ω → ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X P)
    (p : ℝ → ℝ) (hp_meas : Measurable p)
    (hX_law : ∀ i,
      HasLaw (X i) (volume.withDensity (fun x ↦ ENNReal.ofReal (p x))) P)
    (pmax : ℝ) (hpmax : 0 ≤ pmax)
    (hp_nonneg : ∀ᵐ x ∂volume, 0 ≤ p x)
    (hp_bound : ∀ᵐ x ∂volume, p x ≤ pmax)
    (K : ℝ → ℝ) (hK_meas : Measurable K)
    (hK_nonneg : ∀ u, 0 ≤ K u)
    (hK_int : Integrable K)
    (hK_one : ∫ u, K u = 1)
    (hK_sq_int : Integrable (fun u ↦ (K u) ^ 2))
    (x h : ℝ) (hh : 0 < h) :
    let estimate : Ω → ℝ := fun ω ↦
      ((n : ℝ) * h)⁻¹ * ∑ i, K ((X i ω - x) / h)
    (∫ ω, estimate ω ∂P = ∫ u, K u * p (x + h * u)) ∧
      variance estimate P =
        ((n : ℝ) * h)⁻¹ * (∫ u, (K u) ^ 2 * p (x + h * u)) -
          (n : ℝ)⁻¹ * (∫ u, K u * p (x + h * u)) ^ 2
:= by
  /- @proof-region region.root.226758b178cb begin -/
  have key :
      (∫ ω, (fun ω ↦ ((n : ℝ) * h)⁻¹ * ∑ i, K ((X i ω - x) / h)) ω ∂P
          = ∫ u, K u * p (x + h * u)) ∧
        variance (fun ω ↦ ((n : ℝ) * h)⁻¹ * ∑ i, K ((X i ω - x) / h)) P =
          ((n : ℝ) * h)⁻¹ * (∫ u, (K u) ^ 2 * p (x + h * u)) -
            (n : ℝ)⁻¹ * (∫ u, K u * p (x + h * u)) ^ 2 := by
    set estimate : Ω → ℝ := fun ω ↦ ((n : ℝ) * h)⁻¹ * ∑ i, K ((X i ω - x) / h) with hest
    set A : ℝ := ∫ u, K u * p (x + h * u) with hA
    set B : ℝ := ∫ u, (K u) ^ 2 * p (x + h * u) with hB
    obtain ⟨hAint, hBint, hoff⟩ :=
      statopia_math_node_3645602145_3d919080 P n hn X hX_meas hX_indep p hp_meas hX_law pmax hpmax hp_nonneg hp_bound K hK_meas hK_nonneg hK_int hK_sq_int x h hh
    have hY_meas : ∀ i, Measurable (fun ω => K ((X i ω - x) / h)) := by
      intro i
      have h_aff : Measurable (fun y : ℝ => (y - x) / h) :=
        (by continuity : Continuous (fun y : ℝ => (y - x) / h)).measurable
      exact hK_meas.comp (h_aff.comp (hX_meas i))
    have hY_int : ∀ i, Integrable (fun ω => K ((X i ω - x) / h)) P := by
      intro i
      have hsq : Integrable (fun ω => (K ((X i ω - x) / h)) ^ 2) P := by
        have h := (hoff i i).1
        simpa [pow_two] using h
      have hdom : Integrable (fun ω => ((K ((X i ω - x) / h)) ^ 2 + 1) / 2) P := by
        have h1 : Integrable (fun ω => (K ((X i ω - x) / h)) ^ 2 + 1) P :=
          hsq.add (integrable_const (1 : ℝ))
        have h := h1.const_mul (1 / 2)
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
      refine hdom.mono' (hY_meas i).aestronglyMeasurable ?_
      filter_upwards with ω
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨by nlinarith [sq_nonneg (K ((X i ω - x) / h) + 1)],
             by nlinarith [sq_nonneg (K ((X i ω - x) / h) - 1)]⟩
    have hn0 : (n : ℝ) ≠ 0 := by
      have hpos : (0 : ℝ) < (n : ℝ) := by
        have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
      exact ne_of_gt hpos
    have hh0 : h ≠ 0 := ne_of_gt hh
    have hnh0 : (n : ℝ) * h ≠ 0 := mul_ne_zero hn0 hh0
    have hY_mean : ∀ i : Fin n, ∫ ω, K ((X i ω - x) / h) ∂P = h * A := by
      intro i
      obtain ⟨-, -, -, hYmean_eq⟩ :=
        statopia_math_node_710480633_ddaff62b P p hp_meas pmax hpmax hp_nonneg hp_bound (X i) (hX_meas i) (hX_law i) K hK_meas hK_int x h hh
      rw [hYmean_eq, hA.symm]
    have hmean : ∫ ω, estimate ω ∂P = A := by
      have hstep : ∫ ω, estimate ω ∂P = ((n : ℝ) * h)⁻¹ * (∑ i : Fin n, h * A) := by
        simp only [hest]
        rw [MeasureTheory.integral_const_mul]
        congr 1
        rw [MeasureTheory.integral_finset_sum (Finset.univ) (fun i _ => hY_int i)]
        exact Finset.sum_congr rfl (fun i _ => hY_mean i)
      rw [hstep, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    constructor
    · exact hmean
    · have hpair_int : ∀ i j : Fin n,
          Integrable (fun ω => K ((X i ω - x) / h) * K ((X j ω - x) / h)) P :=
        fun i j => (hoff i j).1
      have hpt : ∀ ω, (estimate ω) ^ 2
          = ((n : ℝ) * h)⁻¹ ^ 2 * ∑ i : Fin n, ∑ j : Fin n, K ((X i ω - x) / h) * K ((X j ω - x) / h) := by
        intro ω
        simp only [hest]
        rw [mul_pow]
        congr 1
        rw [pow_two, Finset.sum_mul_sum]
      have hfin : Integrable (fun ω => ∑ i : Fin n, ∑ j : Fin n, K ((X i ω - x) / h) * K ((X j ω - x) / h)) P :=
        integrable_finset_sum Finset.univ (fun i _ => integrable_finset_sum Finset.univ (fun j _ => hpair_int i j))
      have h_est_sq_int : Integrable (fun ω => (estimate ω) ^ 2) P := by
        have hEq : (fun ω => (estimate ω) ^ 2)
            = fun ω => ((n : ℝ) * h)⁻¹ ^ 2 * ∑ i : Fin n, ∑ j : Fin n, K ((X i ω - x) / h) * K ((X j ω - x) / h) :=
          funext hpt
        rw [hEq]
        simpa only [smul_eq_mul] using hfin.const_mul (((n : ℝ) * h)⁻¹ ^ 2)
      have hsum_meas : Measurable (fun ω => ∑ i : Fin n, K ((X i ω - x) / h)) :=
        Finset.measurable_sum _ (fun i _ => hY_meas i)
      have hest_meas : Measurable estimate := by
        rw [hest]
        exact measurable_const.mul hsum_meas
      have hmlp : MemLp estimate 2 P :=
        (memLp_two_iff_integrable_sq hest_meas.aestronglyMeasurable).2 h_est_sq_int
      have hpair_val : ∀ i j : Fin n, ∫ ω, K ((X i ω - x) / h) * K ((X j ω - x) / h) ∂P
          = if i = j then h * B else h ^ 2 * A ^ 2 := by
        intro i j
        simpa only [hA.symm, hB.symm] using (hoff i j).2
      have hdouble : (∑ i : Fin n, ∑ j : Fin n, (if i = j then h * B else h ^ 2 * A ^ 2))
          = (n : ℝ) * (h * B) + ((n : ℝ) * (n : ℝ) - (n : ℝ)) * (h ^ 2 * A ^ 2) := by
        have hinner : ∀ i : Fin n, (∑ j : Fin n, (if i = j then h * B else h ^ 2 * A ^ 2))
            = (n : ℝ) * (h ^ 2 * A ^ 2) + (h * B - h ^ 2 * A ^ 2) := by
          intro i
          have hsplit : ∀ j : Fin n, (if i = j then h * B else h ^ 2 * A ^ 2)
              = h ^ 2 * A ^ 2 + (if i = j then (h * B - h ^ 2 * A ^ 2) else 0) := by
            intro j
            by_cases hc : i = j
            · simp only [if_pos hc]; ring
            · simp only [if_neg hc]; ring
          rw [Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_add_distrib]
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ i)]
        rw [Finset.sum_congr rfl (fun i _ => hinner i), Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
      have hsecond : ∫ ω, (estimate ω) ^ 2 ∂P = B / ((n : ℝ) * h) + (1 - (n : ℝ)⁻¹) * A ^ 2 := by
        have hinner_int : ∀ i : Fin n,
            Integrable (fun ω => ∑ j : Fin n, K ((X i ω - x) / h) * K ((X j ω - x) / h)) P :=
          fun i => integrable_finset_sum Finset.univ (fun j _ => hpair_int i j)
        calc ∫ ω, (estimate ω) ^ 2 ∂P
            = ∫ ω, ((n : ℝ) * h)⁻¹ ^ 2 * ∑ i : Fin n, ∑ j : Fin n, K ((X i ω - x) / h) * K ((X j ω - x) / h) ∂P := by
                simp only [hpt]
          _ = ((n : ℝ) * h)⁻¹ ^ 2 * ∫ ω, ∑ i : Fin n, ∑ j : Fin n, K ((X i ω - x) / h) * K ((X j ω - x) / h) ∂P := by
                rw [MeasureTheory.integral_const_mul]
          _ = ((n : ℝ) * h)⁻¹ ^ 2 * ∑ i : Fin n, ∫ ω, ∑ j : Fin n, K ((X i ω - x) / h) * K ((X j ω - x) / h) ∂P := by
                rw [MeasureTheory.integral_finset_sum Finset.univ (fun i _ => hinner_int i)]
          _ = ((n : ℝ) * h)⁻¹ ^ 2 * ∑ i : Fin n, ∑ j : Fin n, ∫ ω, K ((X i ω - x) / h) * K ((X j ω - x) / h) ∂P := by
                congr 1
                refine Finset.sum_congr rfl (fun i _ => ?_)
                rw [MeasureTheory.integral_finset_sum Finset.univ (fun j _ => hpair_int i j)]
          _ = ((n : ℝ) * h)⁻¹ ^ 2 * ∑ i : Fin n, ∑ j : Fin n, (if i = j then h * B else h ^ 2 * A ^ 2) := by
                congr 1
                refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hpair_val i j))
          _ = B / ((n : ℝ) * h) + (1 - (n : ℝ)⁻¹) * A ^ 2 := by
                rw [hdouble]
                field_simp <;> ring
      rw [variance_eq_sub hmlp]
      simp only [Pi.pow_apply]
      rw [hsecond, hmean]
      field_simp <;> ring
  exact key
  /- @proof-region region.root.226758b178cb end -/
