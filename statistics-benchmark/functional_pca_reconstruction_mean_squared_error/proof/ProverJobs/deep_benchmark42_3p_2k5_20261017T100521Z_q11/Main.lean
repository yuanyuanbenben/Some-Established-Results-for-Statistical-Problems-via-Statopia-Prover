import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q11.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q11.ProvedNodes
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q11.Base

open MeasureTheory

theorem functional_pca_reconstruction_mean_squared_error
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [SecondCountableTopology H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → H)
    (hXmeas : StronglyMeasurable X)
    (hXsq : Integrable (fun ω ↦ ‖X ω‖ ^ 2) P)
    (C : H →L[ℝ] H)
    (phi : ℕ → H) (lambda : ℕ → ℝ)
    (horth : Orthonormal ℝ phi)
    (hcomplete : Dense (Submodule.span ℝ (Set.range phi) : Set H))
    (heigen : ∀ k, C (phi k) = lambda k • phi k)
    (hlambda : Antitone lambda)
    (hlambda_nonneg : ∀ k, 0 ≤ lambda k)
    (hC : ∀ h,
      C h =
        ∫ ω, (inner ℝ (X ω - ∫ z, X z ∂P) h) •
          (X ω - ∫ z, X z ∂P) ∂P) :
    ∀ r : ℕ, 1 ≤ r →
      let mu : H := ∫ ω, X ω ∂P
      let Xr : Ω → H := fun ω ↦
        mu + ∑ k ∈ Finset.range r,
          (inner ℝ (X ω - mu) (phi k)) • phi k
      ∫ ω, ‖X ω - Xr ω‖ ^ 2 ∂P =
        ∑' k : ℕ, if r ≤ k then lambda k else 0
:= by
  /- @proof-region region.root.2edbc11245bf begin -/
  intro r hr
  dsimp only
  have hYmeas : AEStronglyMeasurable (fun ω : Ω => X ω - ∫ z, X z ∂P) P :=
    hXmeas.aestronglyMeasurable.sub aestronglyMeasurable_const
  have hYsq_int : Integrable (fun ω : Ω => ‖X ω - ∫ z, X z ∂P‖ ^ 2) P := by
    have hdom : Integrable (fun ω : Ω => 2 * ‖X ω‖ ^ 2 + 2 * ‖∫ z, X z ∂P‖ ^ 2) P :=
      (hXsq.const_mul 2).add (integrable_const _)
    refine Integrable.mono' hdom (hYmeas.norm.pow 2) ?_
    filter_upwards with ω
    have h2 : ‖X ω - ∫ z, X z ∂P‖ ≤ ‖X ω‖ + ‖∫ z, X z ∂P‖ := norm_sub_le _ _
    have h3 : (0 : ℝ) ≤ ‖X ω‖ + ‖∫ z, X z ∂P‖ := by positivity
    have h4 : (0 : ℝ) ≤ ‖X ω - ∫ z, X z ∂P‖ := norm_nonneg _
    have h5 : (0 : ℝ) ≤ ‖X ω - ∫ z, X z ∂P‖ ^ 2 := sq_nonneg _
    rw [Real.norm_of_nonneg h5]
    have h6 : ‖X ω - ∫ z, X z ∂P‖ ^ 2 ≤ (‖X ω‖ + ‖∫ z, X z ∂P‖) ^ 2 := by
      have h6' : ‖X ω - ∫ z, X z ∂P‖ * ‖X ω - ∫ z, X z ∂P‖
          ≤ (‖X ω‖ + ‖∫ z, X z ∂P‖) * (‖X ω‖ + ‖∫ z, X z ∂P‖) :=
        mul_le_mul h2 h2 h4 h3
      simpa only [sq] using h6'
    nlinarith [h2, h3, h4, h6, sq_nonneg (‖X ω‖ - ‖∫ z, X z ∂P‖)]
  have hinner : ∀ k : ℕ, Integrable
      (fun ω : Ω => (inner ℝ (X ω - ∫ z, X z ∂P) (phi k)) • (X ω - ∫ z, X z ∂P)) P := by
    intro k
    have hdk : Integrable (fun ω : Ω => ‖phi k‖ * ‖X ω - ∫ z, X z ∂P‖ ^ 2) P :=
      hYsq_int.const_mul ‖phi k‖
    refine Integrable.mono' hdk ((hYmeas.inner aestronglyMeasurable_const).smul hYmeas) ?_
    filter_upwards with ω
    rw [norm_smul]
    calc ‖inner ℝ (X ω - ∫ z, X z ∂P) (phi k)‖ * ‖X ω - ∫ z, X z ∂P‖
        ≤ (‖X ω - ∫ z, X z ∂P‖ * ‖phi k‖) * ‖X ω - ∫ z, X z ∂P‖ :=
          mul_le_mul_of_nonneg_right (norm_inner_le_norm _ _) (norm_nonneg _)
      _ = ‖phi k‖ * ‖X ω - ∫ z, X z ∂P‖ ^ 2 := by ring
  have hlambda : ∀ k : ℕ, lambda k = ∫ ω, (inner ℝ (X ω - ∫ z, X z ∂P) (phi k)) ^ 2 ∂P := by
    intro k
    have hself : inner ℝ (phi k) (phi k) = 1 := by
      have h := (orthonormal_iff_ite.1 horth) k k
      simpa using h
    have hcomm := ContinuousLinearMap.integral_comp_comm (innerSL ℝ (phi k)) (hinner k)
    have hpt : ∀ ω : Ω,
        (innerSL ℝ (phi k)) ((inner ℝ (X ω - ∫ z, X z ∂P) (phi k)) •
            (X ω - ∫ z, X z ∂P)) = (inner ℝ (X ω - ∫ z, X z ∂P) (phi k)) ^ 2 := by
      intro ω
      rw [innerSL_apply_apply, inner_smul_right,
        ← real_inner_comm (phi k) (X ω - ∫ z, X z ∂P), sq]
    have h1 : ∫ ω, (innerSL ℝ (phi k)) ((inner ℝ (X ω - ∫ z, X z ∂P) (phi k)) •
            (X ω - ∫ z, X z ∂P)) ∂P
        = ∫ ω, (inner ℝ (X ω - ∫ z, X z ∂P) (phi k)) ^ 2 ∂P := by
      simp only [hpt]
    have h2 : (innerSL ℝ (phi k))
        (∫ ω, (inner ℝ (X ω - ∫ z, X z ∂P) (phi k)) • (X ω - ∫ z, X z ∂P) ∂P) = lambda k := by
      rw [← hC (phi k), heigen k, innerSL_apply_apply, inner_smul_right, hself, mul_one]
    rw [← h1, hcomm]
    exact h2.symm
  obtain ⟨-, hEq⟩ :=
    statopia_math_node_2687649175_9357fdde P X hXmeas hXsq C phi lambda horth heigen hC hlambda r
  have hE : HasSum (fun k : ℕ => lambda k) (∫ ω, ‖X ω - ∫ z, X z ∂P‖ ^ 2 ∂P) :=
    (statopia_math_node_2667375641_f736d674 P X hXmeas hXsq C phi lambda horth hcomplete heigen hC
      hlambda hlambda_nonneg).1
  have htail : ∑' k : ℕ, (if r ≤ k then lambda k else 0)
      = (∫ ω, ‖X ω - ∫ z, X z ∂P‖ ^ 2 ∂P) - ∑ k ∈ Finset.range r, lambda k :=
    (statopia_math_node_1586279299_522770ce lambda hlambda_nonneg
      (∫ ω, ‖X ω - ∫ z, X z ∂P‖ ^ 2 ∂P) hE r).2
  have hpt : ∀ ω : Ω,
      X ω - (∫ z, X z ∂P +
        ∑ k ∈ Finset.range r, (inner ℝ (X ω - ∫ z, X z ∂P) (phi k)) • phi k)
        = (X ω - ∫ z, X z ∂P) -
          ∑ k ∈ Finset.range r, (inner ℝ (X ω - ∫ z, X z ∂P) (phi k)) • phi k := by
    intro ω
    abel
  simp only [hpt]
  rw [hEq, htail]
  /- @proof-region region.root.2edbc11245bf end -/
