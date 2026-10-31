import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q16.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q16.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q16.ProvedNodes.Node_1353280134_668c18e6_a5a2ddf7
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q16.ProvedNodes.Node_2860752011_ddd01222_94825b43
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q16.ProvedNodes.Node_359342246_18c0b9ff_8e3dacd9



open MeasureTheory Matrix ProbabilityTheory

open MeasureTheory Matrix ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_34046222_46bb4793 : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n p : ℕ)
    (X : Matrix (Fin n) (Fin p) ℝ)
    (sigma : ℝ) (hsigma : 0 < sigma)
    (epsilon : Ω → Fin n → ℝ)
    (heps : AEMeasurable epsilon P)
    (hsymm :
      ((1 : Matrix (Fin n) (Fin n) ℝ) - X * (X.transpose * X)⁻¹ * X.transpose).transpose
        = (1 : Matrix (Fin n) (Fin n) ℝ) - X * (X.transpose * X)⁻¹ * X.transpose)
    (horth :
      X.transpose * ((1 : Matrix (Fin n) (Fin n) ℝ) - X * (X.transpose * X)⁻¹ * X.transpose)
        = 0)
    (hgaussian : ∀ a : Fin n → ℝ,
      HasLaw (fun ω => dotProduct a (epsilon ω))
        (gaussianReal 0 (Real.toNNReal (sigma ^ 2 * dotProduct a a))) P),
    let U : Matrix (Fin n) (Fin n) ℝ :=
      (1 : Matrix (Fin n) (Fin n) ℝ) - X * (X.transpose * X)⁻¹ * X.transpose
    let A : Ω → Fin p → ℝ := fun ω => X.transpose *ᵥ epsilon ω
    let B : Ω → Fin n → ℝ := fun ω => U *ᵥ epsilon ω
    IndepFun A B P := by
  /- @proof-region region.target-node.session.81c2c23f1f50c543 begin -/
  intro Ω _ P hP n p X sigma hsigma epsilon heps hsymm horth hgaussian
  haveI : IsProbabilityMeasure P := hP
  dsimp only
  set U : Matrix (Fin n) (Fin n) ℝ := 1 - X * (X.transpose * X)⁻¹ * X.transpose with hU
  have horth' : X.transpose * U = 0 := horth
  set A : Ω → Fin p → ℝ := fun ω => X.transpose *ᵥ epsilon ω with hA
  set B : Ω → Fin n → ℝ := fun ω => U *ᵥ epsilon ω with hB
  have hAmeas : AEMeasurable A P := by
    refine statopia_math_node_359342246_18c0b9ff P p A ?_
    intro i
    exact ⟨Real.toNNReal (sigma ^ 2 * dotProduct (X.transpose i) (X.transpose i)),
      hgaussian (X.transpose i)⟩
  have hBmeas : AEMeasurable B P := by
    refine statopia_math_node_359342246_18c0b9ff P n B ?_
    intro i
    exact ⟨Real.toNNReal (sigma ^ 2 * dotProduct (U i) (U i)), hgaussian (U i)⟩
  let Aw : Ω → EuclideanSpace ℝ (Fin p) := fun ω => WithLp.toLp 2 (X.transpose *ᵥ epsilon ω)
  let Bw : Ω → EuclideanSpace ℝ (Fin n) := fun ω => WithLp.toLp 2 (U *ᵥ epsilon ω)
  have hAw_ofLp : ∀ ω, (Aw ω).ofLp = A ω := fun ω => rfl
  have hBw_ofLp : ∀ ω, (Bw ω).ofLp = B ω := fun ω => rfl
  have hAw : AEMeasurable Aw P :=
    Measurable.comp_aemeasurable (WithLp.measurable_toLp 2 (Fin p → ℝ)) hAmeas
  have hBw : AEMeasurable Bw P :=
    Measurable.comp_aemeasurable (WithLp.measurable_toLp 2 (Fin n → ℝ)) hBmeas
  have hAw_indep : IndepFun Aw Bw P := by
    refine (indepFun_iff_charFun_prod hAw hBw).2 ?_
    intro t
    set s : Fin p → ℝ := t.ofLp.1.ofLp with hs
    set u : Fin n → ℝ := t.ofLp.2.ofLp with hu
    have ht1 : t.ofLp.1 = WithLp.toLp 2 s := by rw [hs, WithLp.toLp_ofLp]
    have ht2 : t.ofLp.2 = WithLp.toLp 2 u := by rw [hu, WithLp.toLp_ofLp]
    have hdep : ∀ (v : Fin p → ℝ) (w : Fin n → ℝ),
        ∫ ω, Complex.exp (Complex.I * ((dotProduct v (A ω) + dotProduct w (B ω) : ℝ) : ℂ)) ∂P
          = Complex.exp ((-(sigma ^ 2 * dotProduct (X *ᵥ v + U *ᵥ w) (X *ᵥ v + U *ᵥ w)) / 2 : ℝ) : ℂ) :=
      fun v w => statopia_math_node_2860752011_ddd01222 P n p X sigma hsigma epsilon heps hsymm hgaussian v w
    have hinner : ∀ (y : EuclideanSpace ℝ (Fin p)) (v : Fin p → ℝ),
        inner ℝ y (WithLp.toLp 2 v) = dotProduct v y.ofLp := by
      intro y v
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp
    have hinner' : ∀ (y : EuclideanSpace ℝ (Fin n)) (v : Fin n → ℝ),
        inner ℝ y (WithLp.toLp 2 v) = dotProduct v y.ofLp := by
      intro y v
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp
    have hpair : ∀ (a : EuclideanSpace ℝ (Fin p)) (b : EuclideanSpace ℝ (Fin n)),
        inner ℝ (WithLp.toLp 2 (a, b)) t = inner ℝ a t.ofLp.1 + inner ℝ b t.ofLp.2 := by
      intro a b
      rw [WithLp.prod_inner_apply]
    have hpairw : AEMeasurable (fun ω => (Aw ω, Bw ω)) P := by
      obtain ⟨φ, hφm, hφae⟩ := hAw
      obtain ⟨ψ, hψm, hψae⟩ := hBw
      exact ⟨fun ω => (φ ω, ψ ω), by fun_prop,
        by
          filter_upwards [hφae, hψae] with ω h1 h2
          rw [h1, h2]⟩
    have hΦw : AEMeasurable (fun ω => WithLp.toLp 2 (Aw ω, Bw ω)) P :=
      Measurable.comp_aemeasurable
        (WithLp.measurable_toLp 2 (EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin n)))
        hpairw
    have hJ : charFun (Measure.map (fun ω => WithLp.toLp 2 (Aw ω, Bw ω)) P) t
        = ∫ ω, Complex.exp (Complex.I * ((dotProduct s (A ω) + dotProduct u (B ω) : ℝ) : ℂ)) ∂P := by
      rw [charFun_eq_integral_innerProbChar]
      rw [integral_map hΦw]
      · simp only [BoundedContinuousFunction.innerProbChar_apply]
        apply integral_congr_ae
        filter_upwards with ω
        rw [hpair (Aw ω) (Bw ω), ht1, ht2, hinner (Aw ω) s, hinner' (Bw ω) u,
          hAw_ofLp ω, hBw_ofLp ω, mul_comm]
      · exact (BoundedContinuousFunction.innerProbChar t).continuous.stronglyMeasurable.aestronglyMeasurable
    have hM1 : charFun (Measure.map Aw P) (WithLp.toLp 2 s)
        = Complex.exp ((-(sigma ^ 2 * dotProduct (X *ᵥ s) (X *ᵥ s)) / 2 : ℝ) : ℂ) := by
      rw [charFun_eq_integral_innerProbChar]
      rw [integral_map hAw]
      · simp only [BoundedContinuousFunction.innerProbChar_apply]
        have e1 : ∀ ω, Complex.exp (↑(inner ℝ (Aw ω) (WithLp.toLp 2 s)) * Complex.I)
            = Complex.exp (Complex.I * ((dotProduct s (A ω) + dotProduct 0 (B ω) : ℝ) : ℂ)) := by
          intro ω
          rw [hinner (Aw ω) s, hAw_ofLp ω]
          have hz : dotProduct 0 (B ω) = 0 := by simp [dotProduct]
          rw [hz, add_zero, mul_comm]
        simp only [e1]
        rw [hdep s 0]
        have hU0 : U *ᵥ (0 : Fin n → ℝ) = 0 := by
          funext i
          simp [Matrix.mulVec, dotProduct]
        rw [hU0]
        simp
      · exact (BoundedContinuousFunction.innerProbChar (WithLp.toLp 2 s)).continuous.stronglyMeasurable.aestronglyMeasurable
    have hM2 : charFun (Measure.map Bw P) (WithLp.toLp 2 u)
        = Complex.exp ((-(sigma ^ 2 * dotProduct (U *ᵥ u) (U *ᵥ u)) / 2 : ℝ) : ℂ) := by
      rw [charFun_eq_integral_innerProbChar]
      rw [integral_map hBw]
      · simp only [BoundedContinuousFunction.innerProbChar_apply]
        have e2 : ∀ ω, Complex.exp (↑(inner ℝ (Bw ω) (WithLp.toLp 2 u)) * Complex.I)
            = Complex.exp (Complex.I * ((dotProduct 0 (A ω) + dotProduct u (B ω) : ℝ) : ℂ)) := by
          intro ω
          rw [hinner' (Bw ω) u, hBw_ofLp ω]
          have hz : dotProduct 0 (A ω) = 0 := by simp [dotProduct]
          rw [hz, zero_add, mul_comm]
        simp only [e2]
        rw [hdep 0 u]
        have hX0 : X *ᵥ (0 : Fin p → ℝ) = 0 := by
          funext i
          simp [Matrix.mulVec, dotProduct]
        rw [hX0]
        simp
      · exact (BoundedContinuousFunction.innerProbChar (WithLp.toLp 2 u)).continuous.stronglyMeasurable.aestronglyMeasurable
    have hadj : ∀ w : Fin n → ℝ, dotProduct (X *ᵥ s) w = dotProduct s (X.transpose *ᵥ w) := by
      intro w
      simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hassoc : X.transpose *ᵥ (U *ᵥ u) = (X.transpose * U) *ᵥ u := by
      funext j
      simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply,
        Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hcross : dotProduct (X *ᵥ s) (U *ᵥ u) = 0 := by
      rw [hadj (U *ᵥ u), hassoc, horth']
      simp [Matrix.mulVec, dotProduct]
    have hcross' : dotProduct (U *ᵥ u) (X *ᵥ s) = 0 := by
      rw [dotProduct_comm (U *ᵥ u) (X *ᵥ s)]
      exact hcross
    have hleft : ∀ a b c : Fin n → ℝ, dotProduct (a + b) c = dotProduct a c + dotProduct b c := by
      intro a b c
      rw [dotProduct_comm (a + b) c, dotProduct_add, dotProduct_comm c a, dotProduct_comm c b]
    have hquad : dotProduct (X *ᵥ s + U *ᵥ u) (X *ᵥ s + U *ᵥ u)
        = dotProduct (X *ᵥ s) (X *ᵥ s) + dotProduct (U *ᵥ u) (U *ᵥ u) := by
      rw [hleft (X *ᵥ s) (U *ᵥ u) (X *ᵥ s + U *ᵥ u), dotProduct_add, dotProduct_add,
        hcross, hcross']
      ring
    have hfac : Complex.exp ((-(sigma ^ 2 * dotProduct (X *ᵥ s + U *ᵥ u) (X *ᵥ s + U *ᵥ u)) / 2 : ℝ) : ℂ)
        = Complex.exp ((-(sigma ^ 2 * dotProduct (X *ᵥ s) (X *ᵥ s)) / 2 : ℝ) : ℂ)
          * Complex.exp ((-(sigma ^ 2 * dotProduct (U *ᵥ u) (U *ᵥ u)) / 2 : ℝ) : ℂ) := by
      rw [← Complex.exp_add]
      congr 1
      have hR : (-(sigma ^ 2 * dotProduct (X *ᵥ s + U *ᵥ u) (X *ᵥ s + U *ᵥ u)) / 2 : ℝ)
          = -(sigma ^ 2 * dotProduct (X *ᵥ s) (X *ᵥ s)) / 2
            + -(sigma ^ 2 * dotProduct (U *ᵥ u) (U *ᵥ u)) / 2 := by
        rw [hquad]
        ring
      rw [hR]
      simp
    rw [hJ, hdep s u, hfac, ht1, ht2, hM1, hM2]
  have hprodw : Measure.map (fun ω => (Aw ω, Bw ω)) P
      = (Measure.map Aw P).prod (Measure.map Bw P) :=
    (indepFun_iff_map_prod_eq_prod_map_map hAw hBw).1 hAw_indep
  have hpairW : AEMeasurable (fun ω => (Aw ω, Bw ω)) P := by
    obtain ⟨φ, hφm, hφae⟩ := hAw
    obtain ⟨ψ, hψm, hψae⟩ := hBw
    exact ⟨fun ω => (φ ω, ψ ω), by fun_prop,
      by
        filter_upwards [hφae, hψae] with ω h1 h2
        rw [h1, h2]⟩
  have hofLp₁ : Measurable (WithLp.ofLp : EuclideanSpace ℝ (Fin p) → (Fin p → ℝ)) :=
    WithLp.measurable_ofLp 2 (Fin p → ℝ)
  have hofLp₂ : Measurable (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)) :=
    WithLp.measurable_ofLp 2 (Fin n → ℝ)
  have hV : Measurable (fun y : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin n) =>
      (y.1.ofLp, y.2.ofLp)) := by
    have h1 : Measurable fun y : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin n) => y.1.ofLp :=
      hofLp₁.comp measurable_fst
    have h2 : Measurable fun y : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin n) => y.2.ofLp :=
      hofLp₂.comp measurable_snd
    fun_prop
  have hVcomp : Measure.map (fun y : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin n) =>
        (y.1.ofLp, y.2.ofLp)) (Measure.map (fun ω => (Aw ω, Bw ω)) P)
      = Measure.map (fun ω => (A ω, B ω)) P := by
    rw [AEMeasurable.map_map_of_aemeasurable
      (show AEMeasurable (fun y : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin n) =>
          (y.1.ofLp, y.2.ofLp)) (Measure.map (fun ω => (Aw ω, Bw ω)) P) from
        ⟨_, hV, Filter.Eventually.of_forall fun _ => rfl⟩) hpairW]
    refine Measure.map_congr ?_
    filter_upwards with ω
    show ((Aw ω).ofLp, (Bw ω).ofLp) = (A ω, B ω)
    rw [hAw_ofLp ω, hBw_ofLp ω]
  have hmapA : Measure.map (WithLp.ofLp : EuclideanSpace ℝ (Fin p) → (Fin p → ℝ))
        (Measure.map Aw P) = Measure.map A P := by
    rw [AEMeasurable.map_map_of_aemeasurable
      (show AEMeasurable (WithLp.ofLp : EuclideanSpace ℝ (Fin p) → (Fin p → ℝ))
          (Measure.map Aw P) from
        ⟨_, hofLp₁, Filter.Eventually.of_forall fun _ => rfl⟩) hAw]
    refine Measure.map_congr ?_
    filter_upwards with ω
    exact hAw_ofLp ω
  have hmapB : Measure.map (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ))
        (Measure.map Bw P) = Measure.map B P := by
    rw [AEMeasurable.map_map_of_aemeasurable
      (show AEMeasurable (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ))
          (Measure.map Bw P) from
        ⟨_, hofLp₂, Filter.Eventually.of_forall fun _ => rfl⟩) hBw]
    refine Measure.map_congr ?_
    filter_upwards with ω
    exact hBw_ofLp ω
  have hR : Measure.map (fun y : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin n) =>
        (y.1.ofLp, y.2.ofLp)) ((Measure.map Aw P).prod (Measure.map Bw P))
      = (Measure.map A P).prod (Measure.map B P) := by
    have hstep : Measure.map (fun y : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin n) =>
          (y.1.ofLp, y.2.ofLp)) ((Measure.map Aw P).prod (Measure.map Bw P))
        = Measure.map (Prod.map (WithLp.ofLp : EuclideanSpace ℝ (Fin p) → (Fin p → ℝ))
            (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)))
            ((Measure.map Aw P).prod (Measure.map Bw P)) := rfl
    rw [hstep, ← Measure.map_prod_map (Measure.map Aw P) (Measure.map Bw P) hofLp₁ hofLp₂,
      hmapA, hmapB]
  have hprod : Measure.map (fun ω => (A ω, B ω)) P
      = (Measure.map A P).prod (Measure.map B P) := by
    have h := congrArg (Measure.map (fun y : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin n) =>
      (y.1.ofLp, y.2.ofLp))) hprodw
    rw [hVcomp, hR] at h
    exact h
  exact (indepFun_iff_map_prod_eq_prod_map_map hAmeas hBmeas).2 hprod
  /- @proof-region region.target-node.session.81c2c23f1f50c543 end -/
