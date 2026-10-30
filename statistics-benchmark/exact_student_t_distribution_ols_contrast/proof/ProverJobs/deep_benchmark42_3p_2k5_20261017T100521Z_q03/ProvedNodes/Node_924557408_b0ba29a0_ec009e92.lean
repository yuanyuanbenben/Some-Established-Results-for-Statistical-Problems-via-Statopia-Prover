import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q03.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q03.Base

open MeasureTheory Matrix ProbabilityTheory

open MeasureTheory Matrix ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_924557408_b0ba29a0 : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (epsilon : Ω → Fin n → ℝ)
    (sigma : ℝ) (hsigma : 0 < sigma)
    (hgaussian : ∀ b : Fin n → ℝ,
      HasLaw (fun ω => dotProduct b (epsilon ω))
        (gaussianReal 0
          (Real.toNNReal (sigma ^ 2 * dotProduct b b))) P)
    (m m2 : ℕ)
    (w : Fin m → Fin n → ℝ) (w2 : Fin m2 → Fin n → ℝ)
    (hw_orth : ∀ i j : Fin m, i ≠ j → dotProduct (w i) (w j) = 0)
    (hw2_orth : ∀ a b : Fin m2, a ≠ b → dotProduct (w2 a) (w2 b) = 0)
    (hw_w2_orth : ∀ (i : Fin m) (a : Fin m2), dotProduct (w i) (w2 a) = 0),
    HasLaw
      (fun ω =>
        ((fun i : Fin m => dotProduct (w i) (epsilon ω)),
         (fun a : Fin m2 => dotProduct (w2 a) (epsilon ω))))
      (Measure.prod
        (Measure.pi (fun i : Fin m =>
          gaussianReal 0 (Real.toNNReal (sigma ^ 2 * dotProduct (w i) (w i)))))
        (Measure.pi (fun a : Fin m2 =>
          gaussianReal 0 (Real.toNNReal (sigma ^ 2 * dotProduct (w2 a) (w2 a))))))
      P := by
  /- @proof-region region.target-node.session.d771c14c1cd21950 begin -/
  intro Ω _ P hP n epsilon sigma hsigma hgaussian m m2 w w2 hw_orth hw2_orth hw_w2_orth
  classical
  have hcoord1 : ∀ i : Fin m, AEMeasurable (fun ω => dotProduct (w i) (epsilon ω)) P :=
    fun i => (hgaussian (w i)).aemeasurable
  have hcoord2 : ∀ a : Fin m2, AEMeasurable (fun ω => dotProduct (w2 a) (epsilon ω)) P :=
    fun a => (hgaussian (w2 a)).aemeasurable
  have hpart1 : AEMeasurable (fun ω => fun i : Fin m => dotProduct (w i) (epsilon ω)) P := by
    rw [aemeasurable_pi_iff]
    exact hcoord1
  have hpart2 : AEMeasurable (fun ω => fun a : Fin m2 => dotProduct (w2 a) (epsilon ω)) P := by
    rw [aemeasurable_pi_iff]
    exact hcoord2
  obtain ⟨f1, hf1m, hf1e⟩ := hpart1
  obtain ⟨f2, hf2m, hf2e⟩ := hpart2
  have hYmeas : Measurable fun ω => (f1 ω, f2 ω) := by
    first
      | exact hf1m.prod_mk hf2m
      | exact hf1m.prod hf2m
      | exact Measurable.prod_mk hf1m hf2m
      | fun_prop
  have hYae : AEMeasurable (fun ω =>
      ((fun i : Fin m => dotProduct (w i) (epsilon ω)),
       (fun a : Fin m2 => dotProduct (w2 a) (epsilon ω)))) P :=
    ⟨fun ω => (f1 ω, f2 ω), hYmeas, by
      filter_upwards [hf1e, hf2e] with ω h1ω h2ω
      rw [h1ω, h2ω]⟩
  have hmain : Measure.map (fun ω =>
      ((fun i : Fin m => dotProduct (w i) (epsilon ω)),
       (fun a : Fin m2 => dotProduct (w2 a) (epsilon ω)))) P
      = (Measure.pi (fun i : Fin m =>
          gaussianReal 0 (Real.toNNReal (sigma ^ 2 * dotProduct (w i) (w i))))).prod
        (Measure.pi (fun a : Fin m2 =>
          gaussianReal 0 (Real.toNNReal (sigma ^ 2 * dotProduct (w2 a) (w2 a))))) := by
    refine (MeasureTheory.charFunDual_eq_prod_iff
      (μ := Measure.pi (fun i : Fin m =>
        gaussianReal 0 (Real.toNNReal (sigma ^ 2 * dotProduct (w i) (w i)))))
      (ν := Measure.pi (fun a : Fin m2 =>
        gaussianReal 0 (Real.toNNReal (sigma ^ 2 * dotProduct (w2 a) (w2 a)))))
      (ξ := P.map (fun ω =>
        ((fun i : Fin m => dotProduct (w i) (epsilon ω)),
         (fun a : Fin m2 => dotProduct (w2 a) (epsilon ω)))))).mp ?_
    intro L
    set T : Fin m → ℝ := fun i => L (ContinuousLinearMap.inl ℝ (Fin m → ℝ) (Fin m2 → ℝ)
      ((ContinuousLinearMap.single ℝ (fun _ : Fin m => ℝ) i) 1)) with hT
    set S : Fin m2 → ℝ := fun a => L (ContinuousLinearMap.inr ℝ (Fin m → ℝ) (Fin m2 → ℝ)
      ((ContinuousLinearMap.single ℝ (fun _ : Fin m2 => ℝ) a) 1)) with hS
    set bb : Fin n → ℝ := (∑ i, T i • w i) + (∑ a, S a • w2 a) with hbb
    have hLsig : ∀ (u : Fin m → ℝ) (v : Fin m2 → ℝ),
        L (u, v) = (∑ i, u i * T i) + (∑ a, v a * S a) := by
      intro u v
      have hul : u = ∑ i, u i • (Pi.single i (1 : ℝ) : Fin m → ℝ) := by
        funext j
        simp [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq']
      have hvl : v = ∑ a, v a • (Pi.single a (1 : ℝ) : Fin m2 → ℝ) := by
        funext j
        simp [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq']
      have hsm : ∀ i : Fin m,
          ((ContinuousLinearMap.single ℝ (fun _ : Fin m => ℝ) i) 1 : Fin m → ℝ) = Pi.single i 1 := by
        intro i
        first
          | rfl
          | simp [ContinuousLinearMap.single]
          | simp [ContinuousLinearMap.single, LinearMap.single]
      have hs2 : ∀ a : Fin m2,
          ((ContinuousLinearMap.single ℝ (fun _ : Fin m2 => ℝ) a) 1 : Fin m2 → ℝ) = Pi.single a 1 := by
        intro a
        first
          | rfl
          | simp [ContinuousLinearMap.single]
          | simp [ContinuousLinearMap.single, LinearMap.single]
      have hpair : (u, v) = ContinuousLinearMap.inl ℝ (Fin m → ℝ) (Fin m2 → ℝ) u
          + ContinuousLinearMap.inr ℝ (Fin m → ℝ) (Fin m2 → ℝ) v := by
        ext <;> simp
      rw [hpair, map_add]
      congr 1
      · conv_lhs => rw [hul]
        simp only [map_sum, ContinuousLinearMap.map_smul, smul_eq_mul, hT]
        exact Finset.sum_congr rfl (fun i _ => by rw [hsm i])
      · conv_lhs => rw [hvl]
        simp only [map_sum, ContinuousLinearMap.map_smul, smul_eq_mul, hS]
        exact Finset.sum_congr rfl (fun a _ => by rw [hs2 a])
    have hdot_add : ∀ (x y z : Fin n → ℝ),
        dotProduct (x + y) z = dotProduct x z + dotProduct y z := by
      intro x y z
      simp only [dotProduct, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    have hdot_comm : ∀ (u v : Fin n → ℝ), dotProduct u v = dotProduct v u := by
      intro u v
      simp only [dotProduct]
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    have hdot_sum_m : ∀ (c : Fin m → ℝ) (y : Fin n → ℝ),
        dotProduct (∑ i, c i • w i) y = ∑ i, c i * dotProduct (w i) y := by
      intro c y
      have hA : (∑ i, c i • w i) = fun j => ∑ i, c i * w i j := by
        funext j
        simp [Finset.sum_apply]
      rw [hA]
      calc dotProduct (fun j => ∑ i, c i * w i j) y
          = ∑ j, (∑ i, c i * w i j) * y j := rfl
        _ = ∑ j, ∑ i, (c i * w i j) * y j := by
              refine Finset.sum_congr rfl (fun j _ => ?_)
              rw [Finset.sum_mul]
        _ = ∑ i, ∑ j, (c i * w i j) * y j := Finset.sum_comm
        _ = ∑ i, c i * ∑ j, w i j * y j := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl (fun j _ => by ring)
        _ = ∑ i, c i * dotProduct (w i) y := rfl
    have hdot_sum_2 : ∀ (c : Fin m2 → ℝ) (y : Fin n → ℝ),
        dotProduct (∑ a, c a • w2 a) y = ∑ a, c a * dotProduct (w2 a) y := by
      intro c y
      have hA : (∑ a, c a • w2 a) = fun j => ∑ a, c a * w2 a j := by
        funext j
        simp [Finset.sum_apply]
      rw [hA]
      calc dotProduct (fun j => ∑ a, c a * w2 a j) y
          = ∑ j, (∑ a, c a * w2 a j) * y j := rfl
        _ = ∑ j, ∑ a, (c a * w2 a j) * y j := by
              refine Finset.sum_congr rfl (fun j _ => ?_)
              rw [Finset.sum_mul]
        _ = ∑ a, ∑ j, (c a * w2 a j) * y j := Finset.sum_comm
        _ = ∑ a, c a * ∑ j, w2 a j * y j := by
              refine Finset.sum_congr rfl (fun a _ => ?_)
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl (fun j _ => by ring)
        _ = ∑ a, c a * dotProduct (w2 a) y := rfl
    have hdot_bb : ∀ y : Fin n → ℝ,
        dotProduct bb y = (∑ i, T i * dotProduct (w i) y)
          + (∑ a, S a * dotProduct (w2 a) y) := by
      intro y
      rw [hbb, hdot_add, hdot_sum_m, hdot_sum_2]
    have hLex : ∀ ω : Ω, L ((fun i : Fin m => dotProduct (w i) (epsilon ω)),
        (fun a : Fin m2 => dotProduct (w2 a) (epsilon ω))) = dotProduct bb (epsilon ω) := by
      intro ω
      rw [hLsig, hdot_bb]
      congr 1
      · exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
      · exact Finset.sum_congr rfl (fun a _ => mul_comm _ _)
    have hLHS : charFunDual (P.map (fun ω =>
        ((fun i : Fin m => dotProduct (w i) (epsilon ω)),
         (fun a : Fin m2 => dotProduct (w2 a) (epsilon ω))))) L
        = Complex.exp (-(sigma ^ 2 * (bb ⬝ᵥ bb)) / 2) := by
      rw [MeasureTheory.charFunDual_eq_charFun_map_one L]
      have haeL : AEMeasurable (⇑L) (P.map (fun ω =>
          ((fun i : Fin m => dotProduct (w i) (epsilon ω)),
           (fun a : Fin m2 => dotProduct (w2 a) (epsilon ω))))) := by
        first
          | exact L.continuous.measurable.aemeasurable
          | exact ⟨⇑L, L.continuous.measurable, by filter_upwards with x; rfl⟩
      have hpush : Measure.map (⇑L) (P.map (fun ω =>
          ((fun i : Fin m => dotProduct (w i) (epsilon ω)),
           (fun a : Fin m2 => dotProduct (w2 a) (epsilon ω)))))
          = Measure.map ((⇑L) ∘ fun ω =>
          ((fun i : Fin m => dotProduct (w i) (epsilon ω)),
           (fun a : Fin m2 => dotProduct (w2 a) (epsilon ω)))) P := by
        have h1 : HasLaw (⇑L) (Measure.map (⇑L) (P.map (fun ω =>
              ((fun i : Fin m => dotProduct (w i) (epsilon ω)),
               (fun a : Fin m2 => dotProduct (w2 a) (epsilon ω))))))
            (P.map (fun ω =>
              ((fun i : Fin m => dotProduct (w i) (epsilon ω)),
               (fun a : Fin m2 => dotProduct (w2 a) (epsilon ω))))) := ⟨haeL, rfl⟩
        have h2 : HasLaw (fun ω =>
              ((fun i : Fin m => dotProduct (w i) (epsilon ω)),
               (fun a : Fin m2 => dotProduct (w2 a) (epsilon ω))))
            (P.map (fun ω =>
              ((fun i : Fin m => dotProduct (w i) (epsilon ω)),
               (fun a : Fin m2 => dotProduct (w2 a) (epsilon ω))))) P := ⟨hYae, rfl⟩
        obtain ⟨-, h3⟩ := h1.comp h2
        exact h3.symm
      have hfun : ((⇑L) ∘ fun ω =>
            ((fun i : Fin m => dotProduct (w i) (epsilon ω)),
             (fun a : Fin m2 => dotProduct (w2 a) (epsilon ω))))
          = fun ω => dotProduct bb (epsilon ω) := by
        funext ω
        exact hLex ω
      obtain ⟨-, hlaw⟩ := hgaussian bb
      rw [hpush, hfun, hlaw, ProbabilityTheory.charFun_gaussianReal]
      have hnn : (0 : ℝ) ≤ sigma ^ 2 * (bb ⬝ᵥ bb) := by
        have h1 : (0 : ℝ) ≤ bb ⬝ᵥ bb := by
          simp only [dotProduct]
          exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (bb i))
        exact mul_nonneg (sq_nonneg sigma) h1
      rw [Real.coe_toNNReal _ hnn]
      congr 1
      push_cast
      ring
    have hRHS : charFunDual (Measure.pi (fun i : Fin m =>
          gaussianReal 0 (Real.toNNReal (sigma ^ 2 * dotProduct (w i) (w i)))))
          (ContinuousLinearMap.comp L (ContinuousLinearMap.inl ℝ (Fin m → ℝ) (Fin m2 → ℝ)))
        * charFunDual (Measure.pi (fun a : Fin m2 =>
          gaussianReal 0 (Real.toNNReal (sigma ^ 2 * dotProduct (w2 a) (w2 a)))))
          (ContinuousLinearMap.comp L (ContinuousLinearMap.inr ℝ (Fin m → ℝ) (Fin m2 → ℝ)))
        = Complex.exp (-(sigma ^ 2 * (bb ⬝ᵥ bb)) / 2) := by
      have hnnm : ∀ i : Fin m, (0 : ℝ) ≤ dotProduct (w i) (w i) := by
        intro i
        simp only [dotProduct]
        exact Finset.sum_nonneg (fun j _ => mul_self_nonneg (w i j))
      have hnn2 : ∀ a : Fin m2, (0 : ℝ) ≤ dotProduct (w2 a) (w2 a) := by
        intro a
        simp only [dotProduct]
        exact Finset.sum_nonneg (fun j _ => mul_self_nonneg (w2 a j))
      have hbridge : ∀ (v : NNReal) (f : ℝ →L[ℝ] ℝ),
          charFunDual (gaussianReal 0 v) f = charFun (gaussianReal 0 v) (f 1) := by
        intro v f
        rw [MeasureTheory.charFunDual_eq_charFun_map_one f]
        have hfun : (⇑f : ℝ → ℝ) = fun x => (f 1) * x := by
          funext x
          have h1 : f x = x • f 1 := by
            simpa using ContinuousLinearMap.map_smul f x (1 : ℝ)
          rw [h1, smul_eq_mul, mul_comm]
        rw [hfun, ProbabilityTheory.gaussianReal_map_const_mul,
          ProbabilityTheory.charFun_gaussianReal, ProbabilityTheory.charFun_gaussianReal]
        congr 1
        first
          | (push_cast; ring)
          | (push_cast; simp only [NNReal.coe_mul, NNReal.coe_mk]; ring)
          | (push_cast; simp; ring)
      have hfac1 : ∀ i : Fin m,
          charFunDual (gaussianReal 0 (Real.toNNReal (sigma ^ 2 * dotProduct (w i) (w i))))
            (ContinuousLinearMap.comp
              (ContinuousLinearMap.comp L (ContinuousLinearMap.inl ℝ (Fin m → ℝ) (Fin m2 → ℝ)))
              (ContinuousLinearMap.single ℝ (fun _ : Fin m => ℝ) i))
          = Complex.exp (-(sigma ^ 2 * dotProduct (w i) (w i) * (T i) ^ 2) / 2) := by
        intro i
        rw [hbridge]
        have hval : (ContinuousLinearMap.comp
              (ContinuousLinearMap.comp L (ContinuousLinearMap.inl ℝ (Fin m → ℝ) (Fin m2 → ℝ)))
              (ContinuousLinearMap.single ℝ (fun _ : Fin m => ℝ) i)) 1 = T i := by
          simp only [ContinuousLinearMap.comp_apply, hT]
        rw [hval, ProbabilityTheory.charFun_gaussianReal,
          Real.coe_toNNReal _ (mul_nonneg (sq_nonneg sigma) (hnnm i))]
        congr 1
        push_cast
        ring
      have hfac2 : ∀ a : Fin m2,
          charFunDual (gaussianReal 0 (Real.toNNReal (sigma ^ 2 * dotProduct (w2 a) (w2 a))))
            (ContinuousLinearMap.comp
              (ContinuousLinearMap.comp L (ContinuousLinearMap.inr ℝ (Fin m → ℝ) (Fin m2 → ℝ)))
              (ContinuousLinearMap.single ℝ (fun _ : Fin m2 => ℝ) a))
          = Complex.exp (-(sigma ^ 2 * dotProduct (w2 a) (w2 a) * (S a) ^ 2) / 2) := by
        intro a
        rw [hbridge]
        have hval : (ContinuousLinearMap.comp
              (ContinuousLinearMap.comp L (ContinuousLinearMap.inr ℝ (Fin m → ℝ) (Fin m2 → ℝ)))
              (ContinuousLinearMap.single ℝ (fun _ : Fin m2 => ℝ) a)) 1 = S a := by
          simp only [ContinuousLinearMap.comp_apply, hS]
        rw [hval, ProbabilityTheory.charFun_gaussianReal,
          Real.coe_toNNReal _ (mul_nonneg (sq_nonneg sigma) (hnn2 a))]
        congr 1
        push_cast
        ring
      have hwi : ∀ i : Fin m, dotProduct (w i) bb = T i * dotProduct (w i) (w i) := by
        intro i
        rw [hdot_comm (w i) bb, hdot_bb]
        have hz1 : (∑ j : Fin m, T j * dotProduct (w j) (w i))
            = T i * dotProduct (w i) (w i) := by
          refine Finset.sum_eq_single i ?_ ?_
          · intro j _ hj
            rw [hw_orth j i hj, mul_zero]
          · intro h
            exact absurd (Finset.mem_univ i) h
        have hz2 : (∑ a : Fin m2, S a * dotProduct (w2 a) (w i)) = 0 := by
          refine Finset.sum_eq_zero ?_
          intro a _
          rw [hdot_comm (w2 a) (w i), hw_w2_orth i a, mul_zero]
        rw [hz1, hz2, add_zero]
      have hw2i : ∀ a : Fin m2, dotProduct (w2 a) bb = S a * dotProduct (w2 a) (w2 a) := by
        intro a
        rw [hdot_comm (w2 a) bb, hdot_bb]
        have hz1 : (∑ i : Fin m, T i * dotProduct (w i) (w2 a)) = 0 := by
          refine Finset.sum_eq_zero ?_
          intro i _
          rw [hw_w2_orth i a, mul_zero]
        have hz2 : (∑ b : Fin m2, S b * dotProduct (w2 b) (w2 a))
            = S a * dotProduct (w2 a) (w2 a) := by
          refine Finset.sum_eq_single a ?_ ?_
          · intro b _ hb
            rw [hw2_orth b a hb, mul_zero]
          · intro h
            exact absurd (Finset.mem_univ a) h
        rw [hz1, hz2, zero_add]
      have hself : dotProduct bb bb
          = (∑ i : Fin m, dotProduct (w i) (w i) * (T i) ^ 2)
            + (∑ a : Fin m2, dotProduct (w2 a) (w2 a) * (S a) ^ 2) := by
        rw [hdot_bb]
        have h1 : (∑ i : Fin m, T i * dotProduct (w i) bb)
            = ∑ i : Fin m, dotProduct (w i) (w i) * (T i) ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [hwi i]
          ring
        have h2 : (∑ a : Fin m2, S a * dotProduct (w2 a) bb)
            = ∑ a : Fin m2, dotProduct (w2 a) (w2 a) * (S a) ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [hw2i a]
          ring
        rw [h1, h2]
      have hE1 : (∏ i : Fin m, Complex.exp (-(sigma ^ 2 * dotProduct (w i) (w i) * (T i) ^ 2) / 2))
          = Complex.exp (∑ i : Fin m, -(sigma ^ 2 * dotProduct (w i) (w i) * (T i) ^ 2) / 2) := by
        rw [Complex.exp_sum]
      have hE2 : (∏ a : Fin m2,
            Complex.exp (-(sigma ^ 2 * dotProduct (w2 a) (w2 a) * (S a) ^ 2) / 2))
          = Complex.exp (∑ a : Fin m2, -(sigma ^ 2 * dotProduct (w2 a) (w2 a) * (S a) ^ 2) / 2) := by
        rw [Complex.exp_sum]
      have hs1r : (∑ i : Fin m, -(sigma ^ 2 * dotProduct (w i) (w i) * (T i) ^ 2) / 2)
          = -(sigma ^ 2 / 2) * (∑ i : Fin m, dotProduct (w i) (w i) * (T i) ^ 2) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      have hs2r : (∑ a : Fin m2, -(sigma ^ 2 * dotProduct (w2 a) (w2 a) * (S a) ^ 2) / 2)
          = -(sigma ^ 2 / 2) * (∑ a : Fin m2, dotProduct (w2 a) (w2 a) * (S a) ^ 2) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun a _ => by ring)
      have hreal : (∑ i : Fin m, -(sigma ^ 2 * dotProduct (w i) (w i) * (T i) ^ 2) / 2)
          + (∑ a : Fin m2, -(sigma ^ 2 * dotProduct (w2 a) (w2 a) * (S a) ^ 2) / 2)
          = -(sigma ^ 2 * ((∑ i : Fin m, dotProduct (w i) (w i) * (T i) ^ 2)
            + (∑ a : Fin m2, dotProduct (w2 a) (w2 a) * (S a) ^ 2))) / 2 := by
        rw [hs1r, hs2r]
        ring
      have hA : (∑ i : Fin m, -((↑sigma : ℂ) ^ 2 * ↑(dotProduct (w i) (w i)) * ↑(T i) ^ 2) / 2)
          = ((∑ i : Fin m, -(sigma ^ 2 * dotProduct (w i) (w i) * (T i) ^ 2) / 2) : ℂ) := by
        norm_cast
      have hB : (∑ a : Fin m2,
            -((↑sigma : ℂ) ^ 2 * ↑(dotProduct (w2 a) (w2 a)) * ↑(S a) ^ 2) / 2)
          = ((∑ a : Fin m2, -(sigma ^ 2 * dotProduct (w2 a) (w2 a) * (S a) ^ 2) / 2) : ℂ) := by
        norm_cast
      have hC : (-((↑sigma : ℂ) ^ 2 * ↑((∑ i : Fin m, dotProduct (w i) (w i) * (T i) ^ 2)
            + (∑ a : Fin m2, dotProduct (w2 a) (w2 a) * (S a) ^ 2))) / 2)
          = ((-(sigma ^ 2 * ((∑ i : Fin m, dotProduct (w i) (w i) * (T i) ^ 2)
            + (∑ a : Fin m2, dotProduct (w2 a) (w2 a) * (S a) ^ 2))) / 2 : ℝ) : ℂ) := by
        norm_cast
      rw [MeasureTheory.charFunDual_pi, MeasureTheory.charFunDual_pi]
      simp only [hfac1, hfac2]
      rw [hE1, hE2, ← Complex.exp_add]
      congr 1
      rw [hself, hA, hB, hC]
      first
        | norm_cast
        | (norm_cast
           rw [hs1r, hs2r]
           ring)
    rw [hLHS, hRHS]
  exact ⟨hYae, hmain⟩
  /- @proof-region region.target-node.session.d771c14c1cd21950 end -/
