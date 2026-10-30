import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q02.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q02.ProvedNodes
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q02.Base

open MeasureTheory ProbabilityTheory

theorem bootstrap_sample_variance_conditional_mean
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 2 ≤ n)
    (X : Fin n → Ω → ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X P)
    (hX_ident : ∀ i,
      IdentDistrib (X i) (X ⟨0, Nat.zero_lt_of_lt hn⟩) P P)
    (hX_sq : Integrable
      (fun ω ↦ (X ⟨0, Nat.zero_lt_of_lt hn⟩ ω) ^ 2) P)
    (I : Fin n → Ω → Fin n)
    (hI_meas : ∀ j, Measurable (I j))
    (hI_indep : iIndepFun I P)
    (hI_uniform : ∀ i j, P {ω | I j ω = i} = (n : ENNReal)⁻¹)
    (hIX_indep :
      IndepFun (fun ω j ↦ I j ω) (fun ω i ↦ X i ω) P) :
    let Xstar : Fin n → Ω → ℝ := fun j ω ↦ X (I j ω) ω
    let mean : Ω → ℝ := fun ω ↦ (n : ℝ)⁻¹ * ∑ i, X i ω
    let meanStar : Ω → ℝ := fun ω ↦ (n : ℝ)⁻¹ * ∑ j, Xstar j ω
    let V : Ω → ℝ := fun ω ↦
      (n : ℝ)⁻¹ * ∑ i, (X i ω - mean ω) ^ 2
    let Vstar : Ω → ℝ := fun ω ↦
      (n : ℝ)⁻¹ * ∑ j, (Xstar j ω - meanStar ω) ^ 2
    let G : MeasurableSpace Ω :=
      MeasurableSpace.comap (fun ω i ↦ X i ω)
        (inferInstance : MeasurableSpace (Fin n → ℝ))
    condExp G P Vstar =ᵐ[P]
      fun ω ↦ (((n - 1 : ℕ) : ℝ) / (n : ℝ)) * V ω
:= by
  /- @proof-region region.root.6548cb48c6bc begin -/
  classical
  dsimp only
  let Xstar : Fin n → Ω → ℝ := fun j ω => X (I j ω) ω
  let mean : Ω → ℝ := fun ω => (n : ℝ)⁻¹ * ∑ i, X i ω
  let meanStar : Ω → ℝ := fun ω => (n : ℝ)⁻¹ * ∑ j, Xstar j ω
  let V : Ω → ℝ := fun ω => (n : ℝ)⁻¹ * ∑ i, (X i ω - mean ω) ^ 2
  let Vstar : Ω → ℝ := fun ω => (n : ℝ)⁻¹ * ∑ j, (Xstar j ω - meanStar ω) ^ 2
  change condExp (MeasurableSpace.comap (fun ω i => X i ω)
      (inferInstance : MeasurableSpace (Fin n → ℝ))) P Vstar =ᵐ[P]
    (fun ω => (((n - 1 : ℕ) : ℝ) / (n : ℝ)) * V ω)
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hnposnat : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn1
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnposnat
  have hnr : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hXsq : ∀ i : Fin n, Integrable (fun ω => (X i ω) ^ 2) P := by
    intro i
    exact (ProbabilityTheory.IdentDistrib.integrable_iff ((hX_ident i).sq)).mpr hX_sq
  have hdiff : ∀ i k : Fin n, Integrable (fun ω => (X i ω - X k ω) ^ 2) P := by
    intro i k
    have hik : Measurable (fun ω => (X i ω - X k ω) ^ 2) := by
      have h := (hX_meas i).sub (hX_meas k)
      simpa [pow_two] using h.mul h
    have hdom : Integrable (fun ω => 2 * (X i ω) ^ 2 + 2 * (X k ω) ^ 2) P :=
      (((hXsq i).const_mul 2).add ((hXsq k).const_mul 2))
    refine hdom.mono' hik.aestronglyMeasurable ?_
    filter_upwards with ω
    have h1 : (0 : ℝ) ≤ (X i ω - X k ω) ^ 2 := sq_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg h1]
    nlinarith [sq_nonneg (X i ω + X k ω)]
  have key : ∀ y : Fin n → ℝ,
      (∑ i : Fin n, ∑ k : Fin n, (y i - y k) ^ 2)
        = 2 * (n : ℝ) ^ 2
            * ((n : ℝ)⁻¹ * ∑ i : Fin n, (y i - (n : ℝ)⁻¹ * ∑ k : Fin n, y k) ^ 2) := by
    intro y
    set S : ℝ := ∑ k : Fin n, y k with hS
    set Q : ℝ := ∑ k : Fin n, (y k) ^ 2 with hQ
    have hinner : ∀ i : Fin n,
        (∑ k : Fin n, (y i - y k) ^ 2) = (n : ℝ) * (y i) ^ 2 + (-2 * y i) * S + Q := by
      intro i
      have hexp : ∀ k : Fin n, (y i - y k) ^ 2 = (y i) ^ 2 + (-2 * y i) * y k + (y k) ^ 2 := by
        intro k
        ring
      rw [Finset.sum_congr rfl (fun k _ => hexp k)]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← Finset.mul_sum]
    have hdouble : (∑ i : Fin n, ∑ k : Fin n, (y i - y k) ^ 2)
        = 2 * (n : ℝ) * Q - 2 * S ^ 2 := by
      rw [Finset.sum_congr rfl (fun i _ => hinner i)]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      have e1 : (∑ i : Fin n, (n : ℝ) * (y i) ^ 2) = (n : ℝ) * Q := by
        rw [← Finset.mul_sum]
      have e2 : (∑ i : Fin n, (-2 * y i) * S) = (-2 * S) * S := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
      have e3 : (∑ _i : Fin n, Q) = (n : ℝ) * Q := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [e1, e2, e3]
      ring
    have hcentered : (∑ i : Fin n, (y i - (n : ℝ)⁻¹ * S) ^ 2) = Q - (n : ℝ)⁻¹ * S ^ 2 := by
      rw [show (∑ i : Fin n, (y i - (n : ℝ)⁻¹ * S) ^ 2)
          = ∑ i : Fin n, ((y i) ^ 2 - (2 * ((n : ℝ)⁻¹ * S)) * y i + ((n : ℝ)⁻¹ * S) ^ 2) from
        Finset.sum_congr rfl (fun i _ => by ring)]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
      ring
    rw [hdouble, hcentered]
    field_simp
  have hsumint : Integrable (fun ω => ∑ i : Fin n, ∑ k : Fin n, (X i ω - X k ω) ^ 2) P :=
    integrable_finset_sum Finset.univ
      (fun i _ => integrable_finset_sum Finset.univ (fun k _ => hdiff i k))
  have hVeq : V = fun ω => (2 * (n : ℝ) ^ 2)⁻¹
      * ∑ i : Fin n, ∑ k : Fin n, (X i ω - X k ω) ^ 2 := by
    funext ω
    have hk := key (fun i => X i ω)
    have hVω : V ω
        = (n : ℝ)⁻¹ * ∑ i : Fin n, (X i ω - (n : ℝ)⁻¹ * ∑ k : Fin n, X k ω) ^ 2 := rfl
    rw [hVω, hk, ← mul_assoc, inv_mul_cancel₀ (mul_ne_zero two_ne_zero (pow_ne_zero 2 hnr)),
      one_mul]
  have hVint : Integrable V P := by
    rw [hVeq]
    exact hsumint.const_mul _
  have meas_sum : ∀ (s : Finset (Fin n)) (f : Fin n → Ω → ℝ),
      (∀ i ∈ s, Measurable (f i)) → Measurable fun ω => ∑ i ∈ s, f i ω := by
    intro s
    induction s using Finset.induction with
    | empty =>
      intro f _
      simpa using (measurable_const : Measurable fun _ : Ω => (0 : ℝ))
    | insert a s ha ih =>
      intro f hf
      have h1 : Measurable (f a) := hf a (Finset.mem_insert_self a s)
      have h2 : Measurable fun ω => ∑ i ∈ s, f i ω :=
        ih f (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      simpa [Finset.sum_insert ha] using h1.add h2
  have hXstar_meas : ∀ j : Fin n, Measurable fun ω => X (I j ω) ω := by
    intro j
    have hrepr : (fun ω => X (I j ω) ω)
        = fun ω => ∑ i : Fin n, ({ω' : Ω | I j ω' = i}.indicator (X i)) ω := by
      funext ω
      have hterm : ∀ i : Fin n,
          ({ω' : Ω | I j ω' = i}.indicator (X i)) ω = if I j ω = i then X i ω else 0 := by
        intro i
        simp [Set.indicator_apply]
      rw [Finset.sum_congr rfl (fun i _ => hterm i)]
      have hsingle_i := Finset.sum_eq_single (s := Finset.univ)
        (f := fun i : Fin n => if I j ω = i then X i ω else (0 : ℝ)) (I j ω)
        (fun b _ hb => by
          have h : ¬ (I j ω = b) := fun hh => hb hh.symm
          simp [h])
        (fun h => absurd (Finset.mem_univ _) h)
      rw [hsingle_i]
      simp
    rw [hrepr]
    exact meas_sum Finset.univ (fun i => {ω' : Ω | I j ω' = i}.indicator (X i))
      (fun i _ => (hX_meas i).indicator ((hI_meas j) (measurableSet_singleton i)))
  have hmean_meas : Measurable mean :=
    Measurable.const_mul (meas_sum Finset.univ X (fun i _ => hX_meas i)) _
  have hVmeas : Measurable V := by
    have hterm : ∀ i : Fin n, Measurable fun ω => (X i ω - mean ω) ^ 2 := by
      intro i
      have h := (hX_meas i).sub hmean_meas
      simpa [pow_two] using h.mul h
    have hsum := meas_sum Finset.univ (fun i ω => (X i ω - mean ω) ^ 2) (fun i _ => hterm i)
    exact Measurable.const_mul hsum _
  have hsingle : ∀ (s : Finset (Fin n)) (g : Fin n → ℝ) (a : Fin n), a ∈ s →
      (∀ i ∈ s, 0 ≤ g i) → g a ≤ ∑ i ∈ s, g i := by
    intro s
    induction s using Finset.induction with
    | empty =>
      intro g a ha
      simp at ha
    | insert b s hb ih =>
      intro g a ha hnn
      rw [Finset.sum_insert hb]
      rcases Finset.mem_insert.mp ha with rfl | ha'
      · have h0 : 0 ≤ ∑ i ∈ s, g i :=
          Finset.sum_nonneg (fun i hi => hnn i (Finset.mem_insert_of_mem hi))
        linarith
      · have h1 : g a ≤ ∑ i ∈ s, g i := ih g a ha' (fun i hi => hnn i (Finset.mem_insert_of_mem hi))
        have h2 : 0 ≤ g b := hnn b (Finset.mem_insert_self b s)
        linarith
  have hpairint : ∀ j l : Fin n,
      Integrable (fun ω => (Xstar j ω - Xstar l ω) ^ 2) P := by
    intro j l
    have hmeas : Measurable fun ω => (Xstar j ω - Xstar l ω) ^ 2 := by
      have h := (hXstar_meas j).sub (hXstar_meas l)
      simpa [pow_two] using h.mul h
    refine hsumint.mono' hmeas.aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 : (Xstar j ω - Xstar l ω) ^ 2 ≤ ∑ k : Fin n, (Xstar j ω - X k ω) ^ 2 :=
      hsingle Finset.univ (fun k => (Xstar j ω - X k ω) ^ 2) (I l ω) (Finset.mem_univ _)
        (fun k _ => sq_nonneg _)
    have h2 : (∑ k : Fin n, (Xstar j ω - X k ω) ^ 2)
        ≤ ∑ i : Fin n, ∑ k : Fin n, (X i ω - X k ω) ^ 2 :=
      hsingle Finset.univ (fun i => ∑ k : Fin n, (X i ω - X k ω) ^ 2) (I j ω)
        (Finset.mem_univ _) (fun i _ => Finset.sum_nonneg (fun k _ => sq_nonneg _))
    linarith
  have hVstar_eq : Vstar = fun ω => (2 * (n : ℝ) ^ 2)⁻¹
      * ∑ j : Fin n, ∑ l : Fin n, (Xstar j ω - Xstar l ω) ^ 2 := by
    funext ω
    have hk := key (fun j => Xstar j ω)
    have hVω : Vstar ω
        = (n : ℝ)⁻¹ * ∑ j : Fin n, (Xstar j ω - (n : ℝ)⁻¹ * ∑ l : Fin n, Xstar l ω) ^ 2 := rfl
    rw [hVω, hk, ← mul_assoc, inv_mul_cancel₀ (mul_ne_zero two_ne_zero (pow_ne_zero 2 hnr)),
      one_mul]
  have meas_sumF : ∀ (s : Finset (Fin n)) (f : Fin n → (Fin n → ℝ) → ℝ),
      (∀ i ∈ s, Measurable (f i)) → Measurable fun v => ∑ i ∈ s, f i v := by
    intro s
    induction s using Finset.induction with
    | empty =>
      intro f _
      simpa using (measurable_const : Measurable fun _ : (Fin n → ℝ) => (0 : ℝ))
    | insert a s ha ih =>
      intro f hf
      have h1 : Measurable (f a) := hf a (Finset.mem_insert_self a s)
      have h2 : Measurable fun v => ∑ i ∈ s, f i v :=
        ih f (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      simpa [Finset.sum_insert ha] using h1.add h2
  have hfeat : Measurable
      (fun v : Fin n → ℝ => (n : ℝ)⁻¹ * ∑ i, (v i - (n : ℝ)⁻¹ * ∑ j, v j) ^ 2) := by
    have hmeanF : Measurable (fun v : Fin n → ℝ => (n : ℝ)⁻¹ * ∑ j, v j) :=
      (meas_sumF Finset.univ (fun j v => v j) (fun j _ => measurable_pi_apply j)).const_mul _
    have hterm : ∀ i : Fin n,
        Measurable (fun v : Fin n → ℝ => (v i - (n : ℝ)⁻¹ * ∑ j, v j) ^ 2) := by
      intro i
      have h := (measurable_pi_apply i).sub hmeanF
      simpa [pow_two] using h.mul h
    exact (meas_sumF Finset.univ _ (fun i _ => hterm i)).const_mul _
  have hVFmeas : ∀ (g : (Fin n → ℝ) → ℝ), Measurable g →
      @Measurable Ω ℝ
        (MeasurableSpace.comap (fun ω i => X i ω)
          (inferInstance : MeasurableSpace (Fin n → ℝ)))
        Real.measurableSpace (fun ω => g (fun i => X i ω)) := by
    intro g hg
    rw [measurable_iff_comap_le]
    refine le_trans (le_of_eq ?_) (MeasurableSpace.comap_mono (measurable_iff_comap_le.mp hg))
    exact (MeasurableSpace.comap_comp (f := g) (g := fun ω i => X i ω)
      (m := Real.measurableSpace)).symm
  have hVmeasG : @Measurable Ω ℝ
      (MeasurableSpace.comap (fun ω i => X i ω) (inferInstance : MeasurableSpace (Fin n → ℝ)))
      Real.measurableSpace V := by
    have hVform : V = fun ω =>
        (fun v : Fin n → ℝ => (n : ℝ)⁻¹ * ∑ i, (v i - (n : ℝ)⁻¹ * ∑ j, v j) ^ 2)
          (fun i => X i ω) := by
      funext ω
      rfl
    rw [hVform]
    exact hVFmeas _ hfeat
  have hpair_moment : ∀ j l : Fin n, j ≠ l →
      condExp (MeasurableSpace.comap (fun ω i => X i ω)
        (inferInstance : MeasurableSpace (Fin n → ℝ))) P
        (fun ω => (Xstar j ω - Xstar l ω) ^ 2) =ᵐ[P] (fun ω => 2 * V ω) := by
    intro j l hjl
    exact statopia_math_node_48977322_51aaa398 P n hn1 X hX_meas I hI_meas hI_indep hI_uniform
      hIX_indep hdiff hVmeasG hVint j l hjl
  have sum_ae : ∀ (ι : Type) (s : Finset ι) (u v : ι → Ω → ℝ), (∀ i ∈ s, u i =ᵐ[P] v i) →
      (∑ i ∈ s, u i) =ᵐ[P] (∑ i ∈ s, v i) := by
    intro ι s
    induction s using Finset.induction with
    | empty =>
      intro u v _
      exact Filter.Eventually.of_forall (fun ω => by simp)
    | insert a s ha ih =>
      intro u v h
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      filter_upwards [h a (Finset.mem_insert_self a s),
        ih u v (fun i hi => h i (Finset.mem_insert_of_mem hi))] with ω h1 h2
      rw [Pi.add_apply, Pi.add_apply, h1, h2]
  have hsumform : (∑ j : Fin n, ∑ l : Fin n, (fun ω => (Xstar j ω - Xstar l ω) ^ 2))
      = fun ω => ∑ j : Fin n, ∑ l : Fin n, (Xstar j ω - Xstar l ω) ^ 2 := by
    funext ω
    simp
  have hinner_eval : ∀ (j : Fin n) (ω : Ω),
      (∑ l : Fin n, (if j = l then (0 : ℝ) else 2 * V ω))
        = (((n - 1 : ℕ) : ℝ)) * (2 * V ω) := by
    intro j ω
    set c : ℝ := 2 * V ω with hc
    have hsplit : (∑ l : Fin n, (if j = l then (0 : ℝ) else c))
        = (∑ l : Fin n, c) - (∑ l : Fin n, (if j = l then c else (0 : ℝ))) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun l _ => by
        by_cases h : j = l <;> simp [h])
    have hone : (∑ l : Fin n, (if j = l then c else (0 : ℝ))) = c := by
      have h := Finset.sum_eq_single (s := Finset.univ)
        (f := fun l : Fin n => if j = l then c else (0 : ℝ)) j
        (fun b _ hb => by
          have hbj : ¬ (j = b) := fun hh => hb hh.symm
          simp [hbj])
        (fun h => absurd (Finset.mem_univ _) h)
      rw [h]
      simp
    rw [hsplit, hone, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub hn1]
      norm_num
    rw [hcast]
    ring
  have hval : ∀ j l : Fin n,
      condExp (MeasurableSpace.comap (fun ω i => X i ω)
        (inferInstance : MeasurableSpace (Fin n → ℝ))) P
        (fun ω => (Xstar j ω - Xstar l ω) ^ 2) =ᵐ[P]
        (fun ω => if j = l then (0 : ℝ) else 2 * V ω) := by
    intro j l
    by_cases hjl : j = l
    · subst hjl
      have hzero : (fun ω => (Xstar j ω - Xstar j ω) ^ 2) = (0 : Ω → ℝ) := by
        funext ω
        simp
      rw [hzero]
      filter_upwards with ω
      simp [MeasureTheory.condExp_zero]
    · have hfun : (fun ω => if j = l then (0 : ℝ) else 2 * V ω) = fun ω => 2 * V ω := by
        funext ω
        simp [hjl]
      rw [hfun]
      exact hpair_moment j l hjl
  have hSvalue : condExp (MeasurableSpace.comap (fun ω i => X i ω)
        (inferInstance : MeasurableSpace (Fin n → ℝ))) P
        (∑ j : Fin n, ∑ l : Fin n, (fun ω => (Xstar j ω - Xstar l ω) ^ 2))
      =ᵐ[P] (fun ω => (n : ℝ) * (((n - 1 : ℕ) : ℝ)) * (2 * V ω)) := by
    have h1 : condExp (MeasurableSpace.comap (fun ω i => X i ω)
          (inferInstance : MeasurableSpace (Fin n → ℝ))) P
          (∑ j : Fin n, ∑ l : Fin n, (fun ω => (Xstar j ω - Xstar l ω) ^ 2))
        =ᵐ[P] (∑ j : Fin n,
          condExp (MeasurableSpace.comap (fun ω i => X i ω)
            (inferInstance : MeasurableSpace (Fin n → ℝ))) P
            (∑ l : Fin n, (fun ω => (Xstar j ω - Xstar l ω) ^ 2))) :=
      condExp_finset_sum (s := Finset.univ)
        (f := fun j : Fin n => (∑ l : Fin n, (fun ω => (Xstar j ω - Xstar l ω) ^ 2)))
        (fun j _ => integrable_finset_sum' Finset.univ (fun l _ => hpairint j l)) _
    have h2 : (∑ j : Fin n,
          condExp (MeasurableSpace.comap (fun ω i => X i ω)
            (inferInstance : MeasurableSpace (Fin n → ℝ))) P
            (∑ l : Fin n, (fun ω => (Xstar j ω - Xstar l ω) ^ 2)))
        =ᵐ[P] (∑ j : Fin n, (fun ω => (((n - 1 : ℕ) : ℝ)) * (2 * V ω))) :=
      sum_ae (Fin n) Finset.univ _ _ (fun j _ => by
        have hinner := condExp_finset_sum (s := Finset.univ)
          (f := fun l : Fin n => (fun ω => (Xstar j ω - Xstar l ω) ^ 2))
          (fun l _ => hpairint j l) (MeasurableSpace.comap (fun ω i => X i ω)
            (inferInstance : MeasurableSpace (Fin n → ℝ)))
        have hstep : (∑ l : Fin n,
            condExp (MeasurableSpace.comap (fun ω i => X i ω)
              (inferInstance : MeasurableSpace (Fin n → ℝ))) P
              (fun ω => (Xstar j ω - Xstar l ω) ^ 2))
            =ᵐ[P] (∑ l : Fin n, (fun ω => if j = l then (0 : ℝ) else 2 * V ω)) :=
          sum_ae (Fin n) Finset.univ _ _ (fun l _ => hval j l)
        have heval : (∑ l : Fin n, (fun ω => if j = l then (0 : ℝ) else 2 * V ω))
            =ᵐ[P] (fun ω => (((n - 1 : ℕ) : ℝ)) * (2 * V ω)) := by
          filter_upwards with ω
          simp only [Finset.sum_apply]
          exact hinner_eval j ω
        exact hinner.trans (hstep.trans heval))
    have h3 : (∑ j : Fin n, (fun ω => (((n - 1 : ℕ) : ℝ)) * (2 * V ω)))
        =ᵐ[P] (fun ω => (n : ℝ) * (((n - 1 : ℕ) : ℝ)) * (2 * V ω)) := by
      filter_upwards with ω
      simp only [Finset.sum_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      ring
    exact h1.trans (h2.trans h3)
  have hbridge : (fun ω => (2 * (n : ℝ) ^ 2)⁻¹
        * ∑ j : Fin n, ∑ l : Fin n, (Xstar j ω - Xstar l ω) ^ 2)
      =ᵐ[P] ((2 * (n : ℝ) ^ 2)⁻¹ •
        (∑ j : Fin n, ∑ l : Fin n, (fun ω => (Xstar j ω - Xstar l ω) ^ 2))) := by
    filter_upwards with ω
    simp only [Pi.smul_apply, smul_eq_mul, hsumform]
  rw [hVstar_eq]
  refine (condExp_congr_ae hbridge).trans ?_
  refine (condExp_smul ((2 * (n : ℝ) ^ 2)⁻¹)
    (∑ j : Fin n, ∑ l : Fin n, (fun ω => (Xstar j ω - Xstar l ω) ^ 2))
    (MeasurableSpace.comap (fun ω i => X i ω)
      (inferInstance : MeasurableSpace (Fin n → ℝ)))).trans ?_
  filter_upwards [hSvalue] with ω hω
  rw [Pi.smul_apply, hω, smul_eq_mul]
  show (2 * (n : ℝ) ^ 2)⁻¹ * ((n : ℝ) * (((n - 1 : ℕ) : ℝ)) * (2 * V ω))
    = (((n - 1 : ℕ) : ℝ) / (n : ℝ)) * V ω
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn1]
    norm_num
  rw [hcast]
  field_simp
  try ring
  /- @proof-region region.root.6548cb48c6bc end -/
