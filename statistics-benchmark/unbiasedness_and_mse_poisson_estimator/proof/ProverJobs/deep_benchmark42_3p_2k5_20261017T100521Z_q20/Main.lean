import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q20.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q20.ProvedNodes
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q20.Base

open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem unbiasedness_and_mse_poisson_estimator
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (theta a : ℝ) (htheta : 0 < theta) (ha : 0 < a)
    (X : ℕ → Ω → ℕ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X P)
    (n : ℕ) (hn : a < (n : ℝ)) :
    let rate : NNReal := ⟨theta, htheta.le⟩
    (∀ i, IdentDistrib (X i) id P (poissonMeasure rate)) →
    let S : Ω → ℕ :=
      fun ω ↦ ∑ i ∈ Finset.range n, X i ω
    let T : Ω → ℝ :=
      fun ω ↦ (1 - a / (n : ℝ)) ^ S ω
    (∫ ω, T ω ∂P = Real.exp (-a * theta)) ∧
      (∫ ω, (T ω - Real.exp (-a * theta)) ^ 2 ∂P) =
        Real.exp (-2 * a * theta) *
          (Real.exp (a ^ 2 * theta / (n : ℝ)) - 1)
:= by
  /- @proof-region region.root.8c06be9a25c2 begin -/
  intro rate hX_id
  have hrate : (rate : ℝ) = theta := rfl
  have hnR : (0 : ℝ) < (n : ℝ) := by linarith
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnR
  set c : ℝ := 1 - a / (n : ℝ) with hc_def
  set m : ℝ := Real.exp (-a * theta) with hm_def
  have hc0 : 0 < c := by
    have h : a / (n : ℝ) < 1 := by
      rw [div_lt_one hnR]
      exact hn
    rw [hc_def]
    linarith
  have hc1 : c < 1 := by
    have h : 0 < a / (n : ℝ) := div_pos ha hnR
    rw [hc_def]
    linarith
  have hc0' : 0 ≤ c := le_of_lt hc0
  have hc1' : c ≤ 1 := le_of_lt hc1
  have hc2' : 0 ≤ c ^ 2 := sq_nonneg c
  have hc2'' : c ^ 2 ≤ 1 := pow_le_one₀ hc0' hc1'
  have exp_pow_eq : ∀ (x : ℝ) (k : ℕ), Real.exp x ^ k = Real.exp ((k : ℝ) * x) := by
    intro x k
    induction k with
    | zero => simp
    | succ j ih =>
        rw [pow_succ, ih, ← Real.exp_add]
        congr 1
        push_cast
        ring
  have hYmeas : ∀ (r : ℝ) (i : ℕ), Measurable (fun ω : Ω => r ^ (X i ω)) := by
    intro r i
    exact Measurable.const_pow (hX_meas i) r
  have hYindep : ∀ r : ℝ, iIndepFun (fun (i : ℕ) (ω : Ω) => r ^ (X i ω)) P := by
    intro r
    exact hX_indep.comp (fun (_ : ℕ) (k : ℕ) => r ^ k)
      (fun _ => (measurable_id : Measurable (id : ℕ → ℕ)).const_pow r)
  have hYint : ∀ (r : ℝ), 0 ≤ r → r ≤ 1 → ∀ i : ℕ, Integrable (fun ω : Ω => r ^ (X i ω)) P := by
    intro r hr0 hr1 i
    refine Integrable.of_bound (hYmeas r i).aestronglyMeasurable 1 ?_
    filter_upwards with ω
    have hpos : (0 : ℝ) ≤ r ^ (X i ω) := pow_nonneg hr0 _
    have hle : r ^ (X i ω) ≤ 1 := pow_le_one₀ hr0 hr1
    rwa [Real.norm_eq_abs, abs_of_nonneg hpos]
  have hgen : ∀ (r : ℝ), 0 ≤ r → r ≤ 1 →
      ∫ ω : Ω, r ^ (∑ i ∈ Finset.range n, X i ω) ∂P
        = Real.exp ((n : ℝ) * theta * (r - 1)) := by
    intro r hr0 hr1
    have hnode := statopia_math_node_3985505336_4606d4cd P (fun (i : ℕ) (ω : Ω) => r ^ (X i ω))
      (hYindep r) (hYmeas r) (hYint r hr0 hr1) (Finset.range n)
    have hsingle : ∀ i : ℕ, ∫ ω : Ω, r ^ (X i ω) ∂P = Real.exp (theta * (r - 1)) := by
      intro i
      have hcomp : IdentDistrib (fun ω : Ω => r ^ (X i ω)) (fun k : ℕ => r ^ k)
          P (poissonMeasure rate) :=
        (hX_id i).comp ((measurable_id : Measurable (id : ℕ → ℕ)).const_pow r)
      rw [hcomp.integral_eq]
      rw [(statopia_math_node_4239247027_57d53a0d rate r hr0 hr1).2]
      rw [hrate]
    have hfun : (fun ω : Ω => r ^ (∑ i ∈ Finset.range n, X i ω))
        = fun ω : Ω => ∏ i ∈ Finset.range n, r ^ (X i ω) := by
      funext ω
      exact (Finset.prod_pow_eq_pow_sum (Finset.range n) (fun i => X i ω) r).symm
    calc ∫ ω : Ω, r ^ (∑ i ∈ Finset.range n, X i ω) ∂P
        = ∫ ω : Ω, (∏ i ∈ Finset.range n, r ^ (X i ω)) ∂P := by rw [hfun]
      _ = ∏ i ∈ Finset.range n, (∫ ω : Ω, r ^ (X i ω) ∂P) := hnode.2
      _ = ∏ i ∈ Finset.range n, Real.exp (theta * (r - 1)) :=
          Finset.prod_congr rfl (fun i _ => hsingle i)
      _ = (Real.exp (theta * (r - 1))) ^ n := by rw [Finset.prod_const, Finset.card_range]
      _ = Real.exp ((n : ℝ) * theta * (r - 1)) := by
          rw [exp_pow_eq]
          congr 1
          ring
  have harg1 : (n : ℝ) * theta * (c - 1) = -a * theta := by
    rw [hc_def]
    have h1 : (↑n : ℝ) * (a / ↑n) = a := by
      simpa [mul_comm] using div_mul_cancel₀ a hnne
    calc (↑n : ℝ) * theta * (1 - a / ↑n - 1) = -((↑n : ℝ) * (a / ↑n)) * theta := by ring
      _ = -a * theta := by rw [h1]
  have harg2 : (n : ℝ) * theta * (c ^ 2 - 1) = -2 * a * theta + a ^ 2 * theta / (n : ℝ) := by
    rw [hc_def]
    field_simp
    ring
  have hTint : Integrable (fun ω : Ω => c ^ (∑ i ∈ Finset.range n, X i ω)) P := by
    have hnode := statopia_math_node_3985505336_4606d4cd P (fun (i : ℕ) (ω : Ω) => c ^ (X i ω))
      (hYindep c) (hYmeas c) (hYint c hc0' hc1') (Finset.range n)
    refine hnode.1.congr (Filter.Eventually.of_forall ?_)
    intro ω
    exact Finset.prod_pow_eq_pow_sum (Finset.range n) (fun i => X i ω) c
  have hfirst : ∫ ω : Ω, c ^ (∑ i ∈ Finset.range n, X i ω) ∂P = m := by
    rw [hm_def, hgen c hc0' hc1', harg1]
  have hsq_eq : ∀ ω : Ω, (c ^ (∑ i ∈ Finset.range n, X i ω)) ^ 2
      = (c ^ 2) ^ (∑ i ∈ Finset.range n, X i ω) := by
    intro ω
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  have hT2int : Integrable (fun ω : Ω => (c ^ (∑ i ∈ Finset.range n, X i ω)) ^ 2) P := by
    have hnode := statopia_math_node_3985505336_4606d4cd P (fun (i : ℕ) (ω : Ω) => (c ^ 2) ^ (X i ω))
      (hYindep (c ^ 2)) (hYmeas (c ^ 2)) (hYint (c ^ 2) hc2' hc2'') (Finset.range n)
    refine hnode.1.congr (Filter.Eventually.of_forall ?_)
    intro ω
    exact (Finset.prod_pow_eq_pow_sum (Finset.range n) (fun i => X i ω) (c ^ 2)).trans (hsq_eq ω).symm
  have hsq : ∫ ω : Ω, (c ^ (∑ i ∈ Finset.range n, X i ω)) ^ 2 ∂P
      = Real.exp (-2 * a * theta + a ^ 2 * theta / (n : ℝ)) := by
    have hfun : (fun ω : Ω => (c ^ (∑ i ∈ Finset.range n, X i ω)) ^ 2)
        = fun ω : Ω => (c ^ 2) ^ (∑ i ∈ Finset.range n, X i ω) := by
      funext ω
      exact hsq_eq ω
    rw [← harg2, hfun, ← hgen (c ^ 2) hc2' hc2'']
  have hm2 : ∫ ω : Ω, m ^ 2 ∂P = m ^ 2 := by
    rw [MeasureTheory.integral_const]
    simp
  have hm_sq : m ^ 2 = Real.exp (-2 * a * theta) := by
    rw [hm_def]
    calc Real.exp (-a * theta) ^ 2 = Real.exp ((2 : ℝ) * (-a * theta)) := exp_pow_eq _ 2
      _ = Real.exp (-2 * a * theta) := by
          congr 1
          ring
  have hIntA : Integrable (fun ω : Ω => (2 * m) * (c ^ (∑ i ∈ Finset.range n, X i ω))) P :=
    hTint.const_mul (2 * m)
  have hIntB : Integrable (fun ω : Ω =>
      (2 * m) * (c ^ (∑ i ∈ Finset.range n, X i ω)) - m ^ 2) P :=
    hIntA.sub (integrable_const (m ^ 2))
  have hstep : ∫ ω : Ω, (2 * m) * (c ^ (∑ i ∈ Finset.range n, X i ω)) - m ^ 2 ∂P
      = (2 * m) * (∫ ω : Ω, c ^ (∑ i ∈ Finset.range n, X i ω) ∂P) - m ^ 2 := by
    rw [MeasureTheory.integral_sub
      (f := fun ω : Ω => (2 * m) * (c ^ (∑ i ∈ Finset.range n, X i ω)))
      (g := fun _ : Ω => m ^ 2) hIntA (integrable_const (m ^ 2))]
    rw [MeasureTheory.integral_const_mul]
    rw [hm2]
  have hmain : ∫ ω : Ω, (c ^ (∑ i ∈ Finset.range n, X i ω) - m) ^ 2 ∂P
      = ∫ ω : Ω, (c ^ (∑ i ∈ Finset.range n, X i ω)) ^ 2 ∂P - m ^ 2 := by
    have hfun : (fun ω : Ω => (c ^ (∑ i ∈ Finset.range n, X i ω) - m) ^ 2)
        = fun ω : Ω => (c ^ (∑ i ∈ Finset.range n, X i ω)) ^ 2
            - ((2 * m) * (c ^ (∑ i ∈ Finset.range n, X i ω)) - m ^ 2) := by
      funext ω
      ring
    rw [hfun]
    rw [MeasureTheory.integral_sub
      (f := fun ω : Ω => (c ^ (∑ i ∈ Finset.range n, X i ω)) ^ 2)
      (g := fun ω : Ω => (2 * m) * (c ^ (∑ i ∈ Finset.range n, X i ω)) - m ^ 2)
      hT2int hIntB]
    rw [hstep, hfirst]
    ring
  refine ⟨hfirst, ?_⟩
  rw [hmain, hsq, hm_sq, Real.exp_add]
  ring
  /- @proof-region region.root.8c06be9a25c2 end -/
