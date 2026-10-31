import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q11.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q11.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q11.ProvedNodes.Node_2870967343_8e3526df_c0be3033
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q11.ProvedNodes.Node_714068217_742cf005_d2274bfe


open MeasureTheory

open MeasureTheory

set_option autoImplicit false in
theorem statopia_math_node_2667375641_f736d674 : ∀ {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → H)
    (hXmeas : StronglyMeasurable X)
    (hXsq : Integrable (fun ω => ‖X ω‖ ^ 2) P)
    (C : H →L[ℝ] H)
    (phi : ℕ → H) (lambda : ℕ → ℝ)
    (horth : Orthonormal ℝ phi)
    (hcomplete : Dense (Submodule.span ℝ (Set.range phi) : Set H))
    (heigen : ∀ k, C (phi k) = lambda k • phi k)
    (hC : ∀ h : H,
      C h =
        ∫ ω, (inner ℝ (X ω - ∫ z, X z ∂P) h) •
          (X ω - ∫ z, X z ∂P) ∂P)
    (hlambda_eq : ∀ k : ℕ,
      lambda k = ∫ ω, (inner ℝ (X ω - ∫ z, X z ∂P) (phi k)) ^ 2 ∂P)
    (hlambda_nonneg : ∀ k : ℕ, 0 ≤ lambda k),
      HasSum (fun k : ℕ => lambda k) (∫ ω, ‖X ω - ∫ z, X z ∂P‖ ^ 2 ∂P) ∧
        ∑' k : ℕ, lambda k = ∫ ω, ‖X ω - ∫ z, X z ∂P‖ ^ 2 ∂P := by
  /- @proof-region region.target-node.session.3356f33ee788c362 begin -/
  intro Ω H _ _ _ _ P _ X hXmeas hXsq C phi lambda horth hcomplete heigen hC hlam hlambda_nonneg
  obtain ⟨_, _, hYint2, _, _⟩ := statopia_math_node_714068217_742cf005 P X hXmeas hXsq
  have hk := fun k : ℕ =>
    statopia_math_node_2870967343_8e3526df P X hXmeas hXsq C phi lambda horth heigen hC k
  have haemeas : ∀ k : ℕ,
      AEStronglyMeasurable (fun ω => inner ℝ (X ω - ∫ z, X z ∂P) (phi k)) P := fun k => (hk k).1
  have hint : ∀ k : ℕ,
      Integrable (fun ω => (inner ℝ (X ω - ∫ z, X z ∂P) (phi k)) ^ 2) P := fun k => (hk k).2.1
  have hspan : (⊤ : Submodule ℝ H) ≤ (Submodule.span ℝ (Set.range phi)).topologicalClosure :=
    ((Submodule.dense_iff_topologicalClosure_eq_top).1 hcomplete).ge
  obtain ⟨b, hbk⟩ : ∃ b : HilbertBasis ℕ ℝ H, ∀ k, b k = phi k :=
    ⟨HilbertBasis.mk horth hspan, fun k => congrFun (HilbertBasis.coe_mk horth hspan) k⟩
  have hparseval : ∀ ω : Ω, HasSum (fun k => (inner ℝ (X ω - ∫ z, X z ∂P) (phi k)) ^ 2)
      (‖X ω - ∫ z, X z ∂P‖ ^ 2) := by
    intro ω
    have h := b.hasSum_inner_mul_inner (X ω - ∫ z, X z ∂P) (X ω - ∫ z, X z ∂P)
    have hcongr : ∀ k : ℕ,
        inner ℝ (X ω - ∫ z, X z ∂P) (b k) * inner ℝ (b k) (X ω - ∫ z, X z ∂P)
          = (inner ℝ (X ω - ∫ z, X z ∂P) (phi k)) ^ 2 := by
      intro k
      rw [hbk k, (real_inner_comm (phi k) (X ω - ∫ z, X z ∂P)).symm, pow_two]
    have hval : inner ℝ (X ω - ∫ z, X z ∂P) (X ω - ∫ z, X z ∂P)
        = ‖X ω - ∫ z, X z ∂P‖ ^ 2 := real_inner_self_eq_norm_sq _
    simpa [hcongr, hval] using h
  set F : ℕ → Ω → ℝ :=
    fun n ω => ∑ k ∈ Finset.range n, (inner ℝ (X ω - ∫ z, X z ∂P) (phi k)) ^ 2 with hF
  have hFnonneg : ∀ n ω, 0 ≤ F n ω := by
    intro n ω
    simp only [hF]
    exact Finset.sum_nonneg fun k _ => sq_nonneg (inner ℝ (X ω - ∫ z, X z ∂P) (phi k))
  have hFle : ∀ n ω, F n ω ≤ ‖X ω - ∫ z, X z ∂P‖ ^ 2 := by
    intro n ω
    have hbessel := Orthonormal.sum_inner_products_le (X ω - ∫ z, X z ∂P)
      (v := phi) (s := Finset.range n) horth
    have hFrw : F n ω =
        ∑ k ∈ Finset.range n, (inner ℝ (X ω - ∫ z, X z ∂P) (phi k)) ^ 2 := by
      simp [hF]
    have hsummand : ∑ k ∈ Finset.range n, (inner ℝ (X ω - ∫ z, X z ∂P) (phi k)) ^ 2
        = ∑ k ∈ Finset.range n, ‖inner ℝ (phi k) (X ω - ∫ z, X z ∂P)‖ ^ 2 :=
      Finset.sum_congr rfl (fun k _ => by
        rw [real_inner_comm (X ω - ∫ z, X z ∂P) (phi k), Real.norm_eq_abs, sq_abs])
    rw [hFrw, hsummand]
    exact hbessel
  have hFmeas : ∀ n : ℕ, AEStronglyMeasurable (F n) P := by
    intro n
    induction n with
    | zero =>
      have h0 : F 0 = fun _ => (0 : ℝ) := by
        funext ω
        simp [hF]
      rw [h0]
      exact aestronglyMeasurable_const
    | succ n ih =>
      have hstep : F (n + 1) =
          F n + fun ω => (inner ℝ (X ω - ∫ z, X z ∂P) (phi n)) ^ 2 := by
        funext ω
        simp [hF, Finset.sum_range_succ]
      rw [hstep]
      have hsq : AEStronglyMeasurable
          (fun ω => (inner ℝ (X ω - ∫ z, X z ∂P) (phi n)) ^ 2) P := by
        have h1 := haemeas n
        simpa [pow_two] using h1.mul h1
      exact ih.add hsq
  have htendsto : ∀ᵐ ω ∂P, Filter.Tendsto (fun n => F n ω) Filter.atTop
      (nhds (‖X ω - ∫ z, X z ∂P‖ ^ 2)) := by
    refine Filter.Eventually.of_forall (fun ω => ?_)
    simpa [hF] using (hparseval ω).tendsto_sum_nat
  have hDCT : Filter.Tendsto (fun n => ∫ ω, F n ω ∂P) Filter.atTop
      (nhds (∫ ω, ‖X ω - ∫ z, X z ∂P‖ ^ 2 ∂P)) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence
      (f := fun ω => ‖X ω - ∫ z, X z ∂P‖ ^ 2) (fun ω => ‖X ω - ∫ z, X z ∂P‖ ^ 2)
      hFmeas hYint2 ?_ htendsto
    intro n
    refine Filter.Eventually.of_forall (fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hFnonneg n ω)]
    exact hFle n ω
  have hInt : ∀ n : ℕ, ∫ ω, F n ω ∂P = ∑ k ∈ Finset.range n, lambda k := by
    intro n
    have h1 : ∫ ω, ∑ k ∈ Finset.range n, (inner ℝ (X ω - ∫ z, X z ∂P) (phi k)) ^ 2 ∂P
        = ∑ k ∈ Finset.range n,
            ∫ ω, (inner ℝ (X ω - ∫ z, X z ∂P) (phi k)) ^ 2 ∂P :=
      MeasureTheory.integral_finset_sum (Finset.range n)
        (f := fun k ω => (inner ℝ (X ω - ∫ z, X z ∂P) (phi k)) ^ 2) (fun k _ => hint k)
    have hFn : ∫ ω, F n ω ∂P
        = ∫ ω, ∑ k ∈ Finset.range n, (inner ℝ (X ω - ∫ z, X z ∂P) (phi k)) ^ 2 ∂P := by
      simp [hF]
    rw [hFn, h1]
    exact Finset.sum_congr rfl (fun k _ => (hlam k).symm)
  have hlim : Filter.Tendsto (fun n => ∑ k ∈ Finset.range n, lambda k) Filter.atTop
      (nhds (∫ ω, ‖X ω - ∫ z, X z ∂P‖ ^ 2 ∂P)) := by
    simpa [hInt] using hDCT
  have hmain : HasSum (fun k : ℕ => lambda k) (∫ ω, ‖X ω - ∫ z, X z ∂P‖ ^ 2 ∂P) :=
    (hasSum_iff_tendsto_nat_of_nonneg hlambda_nonneg _).2 hlim
  exact ⟨hmain, hmain.tsum_eq⟩
  /- @proof-region region.target-node.session.3356f33ee788c362 end -/
