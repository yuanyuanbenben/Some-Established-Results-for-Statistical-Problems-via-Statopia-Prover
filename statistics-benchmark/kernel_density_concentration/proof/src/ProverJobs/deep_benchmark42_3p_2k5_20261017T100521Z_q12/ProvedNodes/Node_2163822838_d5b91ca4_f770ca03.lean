import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q12.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q12.Base

open MeasureTheory ProbabilityTheory

open MeasureTheory ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_2163822838_d5b91ca4 : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (hn : 1 ≤ n)
    (X : Fin n → Ω → ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (f : ℝ → ℝ) (hf_meas : Measurable f)
    (K : ℝ → ℝ) (hK_meas : Measurable K)
    (h : ℝ) (hh : 0 < h),
    let e : (Fin n → ℝ) → ℝ → ℝ :=
      fun a x => ((n : ℝ) * h)⁻¹ * ∑ i : Fin n, K ((x - a i) / h)
    let G : (Fin n → ℝ) → ℝ :=
      fun a => ∫ x : ℝ, |e a x - f x| ∂volume
    let Xvec : Ω → (Fin n → ℝ) := fun ω i => X i ω
    let F : Ω → ℝ := fun ω => ∫ x : ℝ, |e (Xvec ω) x - f x| ∂volume
    Measurable (Function.uncurry e) ∧ Measurable G ∧ F = G ∘ Xvec ∧ Measurable F ∧
      @Measurable Ω ℝ
        (⨆ i : Fin n, MeasurableSpace.comap (X i) (inferInstance : MeasurableSpace ℝ))
        (inferInstance : MeasurableSpace ℝ) F := by
  /- @proof-region region.target-node.session.8d4766f530e56da1 begin -/
  intro Ω inst n hn X hX_meas f hf_meas K hK_meas h hh
  dsimp only
  have hcoord : ∀ i : Fin n, Measurable fun p : (Fin n → ℝ) × ℝ => (p.2 - p.1 i) / h := by
    intro i
    have h1 : Measurable fun p : (Fin n → ℝ) × ℝ => p.1 i :=
      (measurable_pi_iff.mp measurable_fst) i
    exact Measurable.div (measurable_snd.sub h1) measurable_const
  have hS : Measurable fun p : (Fin n → ℝ) × ℝ =>
      ∑ i : Fin n, K ((p.2 - p.1 i) / h) :=
    Finset.measurable_sum Finset.univ fun i _ => hK_meas.comp (hcoord i)
  have hE : Measurable fun p : (Fin n → ℝ) × ℝ =>
      ((n : ℝ) * h)⁻¹ * ∑ i : Fin n, K ((p.2 - p.1 i) / h) :=
    Measurable.const_mul hS ((n : ℝ) * h)⁻¹
  have hΦ : Measurable fun p : (Fin n → ℝ) × ℝ =>
      |((n : ℝ) * h)⁻¹ * ∑ i : Fin n, K ((p.2 - p.1 i) / h) - f p.2| :=
    continuous_abs.measurable.comp (hE.sub (hf_meas.comp measurable_snd))
  have hG : Measurable fun a : Fin n → ℝ =>
      ∫ x : ℝ, |((n : ℝ) * h)⁻¹ * ∑ i : Fin n, K ((x - a i) / h) - f x| ∂volume :=
    hΦ.stronglyMeasurable.integral_prod_right'.measurable
  have hXvec : Measurable fun ω : Ω => fun i : Fin n => X i ω := by
    rw [measurable_pi_iff]
    exact hX_meas
  have hF : Measurable fun ω : Ω =>
      ∫ x : ℝ, |((n : ℝ) * h)⁻¹ * ∑ i : Fin n, K ((x - X i ω) / h) - f x| ∂volume :=
    hG.comp hXvec
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Function.uncurry] using hE
  · exact hG
  · rfl
  · exact hF
  · have hXvec' : @Measurable Ω (Fin n → ℝ)
        (⨆ i : Fin n, MeasurableSpace.comap (X i) (inferInstance : MeasurableSpace ℝ))
        (inferInstance : MeasurableSpace (Fin n → ℝ)) (fun ω i => X i ω) :=
      (@measurable_pi_iff Ω (Fin n) (fun _ : Fin n => ℝ)
        (⨆ i : Fin n, MeasurableSpace.comap (X i) (inferInstance : MeasurableSpace ℝ))
        (fun _ : Fin n => (inferInstance : MeasurableSpace ℝ))
        (fun ω i => X i ω)).mpr
        (fun i => measurable_iff_comap_le.mpr
          (le_iSup (f := fun j : Fin n =>
            MeasurableSpace.comap (X j) (inferInstance : MeasurableSpace ℝ)) i))
    exact hG.comp hXvec'
  /- @proof-region region.target-node.session.8d4766f530e56da1 end -/
