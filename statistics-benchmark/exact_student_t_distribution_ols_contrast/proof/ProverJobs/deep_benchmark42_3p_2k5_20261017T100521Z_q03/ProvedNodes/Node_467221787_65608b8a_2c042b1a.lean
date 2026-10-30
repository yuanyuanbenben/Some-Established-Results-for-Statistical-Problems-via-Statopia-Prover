import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q03.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q03.Base

open MeasureTheory Matrix ProbabilityTheory

open MeasureTheory Matrix ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_467221787_65608b8a : (Measure.pi (fun _ : Fin 1 => gaussianReal 0 1)).map
        (fun y : Fin 1 → ℝ => ∑ k : Fin 1, (y k) ^ 2)
      = volume.withDensity
          (fun s : ℝ => ENNReal.ofReal (gammaConvDensity (((1 : ℕ) : ℝ) / 2) s)) := by
  /- @proof-region region.target-node.session.a32a33d8263b6097 begin -/
  have hmap : Measure.map (fun f : Fin 1 → ℝ => f 0)
      (Measure.pi fun _ : Fin 1 => gaussianReal 0 1) = gaussianReal 0 1 := by
    simpa using
      (measurePreserving_piUnique (fun _ : Fin 1 => (gaussianReal 0 1 : Measure ℝ))).map_eq
  have hfun : (fun y : Fin 1 → ℝ => ∑ k : Fin 1, (y k) ^ 2)
      = (fun z : ℝ => z ^ 2) ∘ (fun f : Fin 1 → ℝ => f 0) := by
    funext y
    simp
  have hred : (Measure.pi (fun _ : Fin 1 => gaussianReal 0 1)).map
        (fun y : Fin 1 → ℝ => ∑ k : Fin 1, (y k) ^ 2)
      = (gaussianReal 0 1).map (fun z : ℝ => z ^ 2) := by
    rw [hfun]
    conv_rhs => rw [← hmap]
    rw [Measure.map_map] <;> measurability
  rw [hred]
  have hsq_meas : Measurable fun z : ℝ => z ^ 2 := by measurability
  have hgauss : gaussianReal (0 : ℝ) 1
      = volume.withDensity (fun z : ℝ => ENNReal.ofReal (gaussianPDFReal 0 1 z)) := by
    unfold gaussianReal
    rw [if_neg (by norm_num)]
    rfl
  have hembTest (e : ℝ ≃ᵐ ℝ) : MeasurableEmbedding (⇑e) := e.measurableEmbedding
  have hcomapTest {f : ℝ → ℝ} (hf : MeasurableEmbedding f) (μ : Measure ℝ) (s : Set ℝ) :
      Measure.comap f μ s = μ (f '' s) := hf.comap_apply μ s
  have hPsi : ∀ t : ℝ, gammaConvDensity (((1 : ℕ) : ℝ) / 2) t
      = 2 * ((2 * Real.sqrt t)⁻¹ * gaussianPDFReal 0 1 (Real.sqrt t)) := by
    intro t
    have hcast : (((1 : ℕ) : ℝ) / 2) = (1 / 2 : ℝ) := by norm_num
    have hc1 : ((1 : NNReal) : ℝ) = 1 := by norm_num
    rw [gammaConvDensity, gaussianPDFReal_def]
    simp only [hcast, hc1]
    by_cases ht : 0 < t
    · rw [if_pos ht]
      have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
      have hp2 : Real.rpow 2 (1 / 2) = Real.sqrt 2 := (Real.sqrt_eq_rpow 2).symm
      have h1 : Real.sqrt (2 * Real.pi) = Real.rpow 2 (1 / 2) * Real.Gamma (1 / 2) := by
        rw [Real.Gamma_one_half_eq, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), ← hp2]
      have h2 : Real.rpow t (1 / 2 - 1) = (Real.sqrt t)⁻¹ := by
        have hsub : (1 / 2 - 1 : ℝ) = -(1 / 2) := by norm_num
        rw [hsub]
        have hneg : Real.rpow t (-(1 / 2)) = (Real.rpow t (1 / 2))⁻¹ :=
          Real.rpow_neg ht.le (1 / 2)
        rw [hneg, show Real.rpow t (1 / 2) = Real.sqrt t from (Real.sqrt_eq_rpow t).symm]
      simp only [sub_zero, mul_one, hsq]
      rw [h1, h2]
      have hc : Real.rpow 2 (1 / 2) * Real.Gamma (1 / 2) ≠ 0 := by
        have hg : Real.Gamma (1 / 2) = Real.sqrt Real.pi := Real.Gamma_one_half_eq
        rw [hp2, hg]
        have hp2' : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
        have hpp : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
        exact (mul_pos hp2' hpp).ne'
      field_simp
    · rw [if_neg ht, Real.sqrt_eq_zero'.2 (le_of_not_gt ht)]
      simp
  let e : ℝ ≃ᵐ ℝ :=
    { toFun := fun y : ℝ => if 0 ≤ y then Real.sqrt y else -Real.sqrt (-y)
      invFun := fun x : ℝ => if 0 ≤ x then x ^ 2 else -(x ^ 2)
      left_inv := by
        intro y
        dsimp only
        by_cases hy : 0 ≤ y
        · rw [if_pos hy, if_pos (Real.sqrt_nonneg y), Real.sq_sqrt hy]
        · have hpos : ¬ (0 ≤ -Real.sqrt (-y)) := by
            have hsp : 0 < Real.sqrt (-y) := Real.sqrt_pos.2 (by linarith)
            linarith
          rw [if_neg hy, if_neg hpos,
            show (-Real.sqrt (-y)) ^ 2 = (Real.sqrt (-y)) ^ 2 by ring,
            Real.sq_sqrt (by linarith : (0 : ℝ) ≤ -y)]
          ring
      right_inv := by
        intro x
        dsimp only
        by_cases hx : 0 ≤ x
        · rw [if_pos hx, if_pos (sq_nonneg x), Real.sqrt_sq hx]
        · have hx' : x < 0 := not_le.1 hx
          have hpos : ¬ (0 ≤ -(x ^ 2)) := by nlinarith
          rw [if_neg hx, if_neg hpos, neg_neg, Real.sqrt_sq_eq_abs, abs_of_neg hx']
          ring
      measurable_toFun := by
        have h1 : Measurable fun y : ℝ => Real.sqrt y := Real.continuous_sqrt.measurable
        have h2 : Measurable fun y : ℝ => -Real.sqrt (-y) :=
          (Real.continuous_sqrt.measurable.comp measurable_neg).neg
        exact Measurable.ite measurableSet_Ici h1 h2
      measurable_invFun := by
        have h1 : Measurable fun x : ℝ => x ^ 2 := by
          simpa [pow_two] using (measurable_id.mul measurable_id)
        exact Measurable.ite measurableSet_Ici h1 h1.neg }
  have hes : ⇑e.symm = fun x : ℝ => if 0 ≤ x then x ^ 2 else -(x ^ 2) := rfl
  have hφnn : ∀ x : ℝ, 0 ≤ gaussianPDFReal 0 1 x := fun x =>
    ProbabilityTheory.gaussianPDFReal_nonneg 0 1 x
  have hIntφ : ∀ s : Set ℝ, IntegrableOn (gaussianPDFReal 0 1) s ℙ := fun s =>
    (ProbabilityTheory.integrable_gaussianPDFReal 0 1).integrableOn
  have he_pos : ∀ x : ℝ, 0 < x → ⇑e x = Real.sqrt x := by
    intro x hx
    show (if 0 ≤ x then Real.sqrt x else -Real.sqrt (-x)) = Real.sqrt x
    rw [if_pos hx.le]
  have he_neg : ∀ x : ℝ, x < 0 → ⇑e x = -Real.sqrt (-x) := by
    intro x hx
    show (if 0 ≤ x then Real.sqrt x else -Real.sqrt (-x)) = -Real.sqrt (-x)
    rw [if_neg (not_le.2 hx)]
  have hψ_nonpos : ∀ s : ℝ, ¬ 0 < s → gammaConvDensity (((1 : ℕ) : ℝ) / 2) s = 0 := by
    intro s hs
    rw [gammaConvDensity, if_neg hs]
  have hμsing : gaussianReal 0 1 ({0} : Set ℝ) = 0 := by
    rw [hgauss, withDensity_apply _ (measurableSet_singleton (0 : ℝ))]
    simp
  let ne : ℝ ≃ᵐ ℝ :=
    { toFun := fun x : ℝ => -x
      invFun := fun x : ℝ => -x
      left_inv := by intro x; simp
      right_inv := by intro x; simp
      measurable_toFun := measurable_neg
      measurable_invFun := measurable_neg }
  let e₂ : ℝ ≃ᵐ ℝ := ne.trans e
  have he₂ : ⇑e₂ = fun x : ℝ => ⇑e (-x) := rfl
  have hder_pos : ∀ x : ℝ, 0 < x → HasDerivWithinAt (⇑e) ((2 * Real.sqrt x)⁻¹) (Set.Ioi 0) x := by
    intro x hx
    have h1 : HasDerivWithinAt Real.sqrt ((2 * Real.sqrt x)⁻¹) (Set.Ioi 0) x :=
      (Real.hasDerivAt_sqrt (ne_of_gt hx)).hasDerivWithinAt.congr_deriv (by rw [one_div])
    exact h1.congr (fun y hy => he_pos y hy) (he_pos x hx)
  have hder_neg : ∀ x : ℝ, 0 < x → HasDerivWithinAt (⇑e₂) (-((2 * Real.sqrt x)⁻¹)) (Set.Ioi 0) x := by
    intro x hx
    have h1 : HasDerivWithinAt (fun y : ℝ => -Real.sqrt y) (-((2 * Real.sqrt x)⁻¹))
        (Set.Ioi 0) x := by
      have h0 := (Real.hasDerivAt_sqrt (ne_of_gt hx)).neg
      exact h0.hasDerivWithinAt.congr_deriv (by rw [one_div])
    exact h1.congr (fun y hy => by
      show ⇑e (-y) = -Real.sqrt y
      have hy' : (0 : ℝ) < y := hy
      rw [he_neg (-y) (by linarith : -y < 0), neg_neg]) (by
      show ⇑e (-x) = -Real.sqrt x
      rw [he_neg (-x) (by linarith : -x < 0), neg_neg])
  have himg_eq : ∀ B : Set ℝ, ⇑e '' B = ⇑e.symm ⁻¹' B := by
    intro B
    ext z
    constructor
    · rintro ⟨b, hb, rfl⟩
      simpa using hb
    · intro hz
      exact ⟨⇑e.symm z, hz, by simp⟩
  have himg_meas : ∀ B : Set ℝ, MeasurableSet B → MeasurableSet (⇑e '' B) := by
    intro B hB
    rw [himg_eq B]
    exact (hembTest e.symm).measurable hB
  have hneg_meas : ∀ B : Set ℝ, MeasurableSet B → MeasurableSet (-B) := by
    intro B hB
    have h := measurable_neg hB
    simpa using h
  have himg₂ : ∀ B : Set ℝ, ⇑e₂ '' B = ⇑e '' (-B) := by
    intro B
    ext z
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨-b, by simpa using hb, by rw [he₂]⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨-b, by simpa using hb, by rw [he₂]; simp⟩
  have himg₂_meas : ∀ B : Set ℝ, MeasurableSet B → MeasurableSet (⇑e₂ '' B) := by
    intro B hB
    rw [himg₂ B]
    exact himg_meas (-B) (hneg_meas B hB)
  have hsqid : ∀ B : Set ℝ, B ⊆ Set.Ioi 0 →
      (fun z : ℝ => z ^ 2) ⁻¹' B = ⇑e '' B ∪ ⇑e₂ '' B := by
    intro B hB
    ext z
    constructor
    · intro hz
      have hzp : (0 : ℝ) < z ^ 2 := hB hz
      rcases lt_trichotomy z 0 with hlt | heq | hgt
      · right
        refine ⟨z ^ 2, hz, ?_⟩
        show ⇑e (-(z ^ 2)) = z
        rw [he_neg (-(z ^ 2)) (by nlinarith), neg_neg, Real.sqrt_sq_eq_abs, abs_of_neg hlt]
        ring
      · subst heq
        exact absurd hzp (by norm_num : ¬ (0 : ℝ) < 0 ^ 2)
      · left
        refine ⟨z ^ 2, hz, ?_⟩
        show ⇑e (z ^ 2) = z
        rw [he_pos (z ^ 2) hzp, Real.sqrt_sq (le_of_lt hgt)]
    · intro hz
      rcases hz with hz | hz
      · obtain ⟨b, hb, rfl⟩ := hz
        have hbpos : (0 : ℝ) < b := hB hb
        show (⇑e b) ^ 2 ∈ B
        rw [he_pos b hbpos, Real.sq_sqrt hbpos.le]
        exact hb
      · obtain ⟨b, hb, rfl⟩ := hz
        have hbpos : (0 : ℝ) < b := hB hb
        show (⇑e₂ b) ^ 2 ∈ B
        have hval : ⇑e₂ b = -Real.sqrt b := by
          show ⇑e (-b) = -Real.sqrt b
          rw [he_neg (-b) (by linarith : -b < 0), neg_neg]
        rw [hval, show (-Real.sqrt b) ^ 2 = (Real.sqrt b) ^ 2 by ring,
          Real.sq_sqrt hbpos.le]
        exact hb
  have hφeven : ∀ y : ℝ, gaussianPDFReal 0 1 (-y) = gaussianPDFReal 0 1 y := by
    intro y
    rw [gaussianPDFReal_def]
    have hc1 : ((1 : NNReal) : ℝ) = 1 := by norm_num
    simp only [hc1, mul_one, sub_zero]
    rw [show (-y) ^ 2 = y ^ 2 by ring]
  have hcomap_e : ∀ B : Set ℝ, MeasurableSet B → B ⊆ Set.Ioi 0 →
      (Measure.comap ⇑e
          (volume.withDensity (fun x => ENNReal.ofReal (gaussianPDFReal 0 1 x)))) B
        = ENNReal.ofReal
            (∫ x in B, |((2 * Real.sqrt x)⁻¹ : ℝ)| * gaussianPDFReal 0 1 (⇑e x)) := by
    intro B hB hBsub
    exact MeasurableEmbedding.withDensity_ofReal_comap_apply_eq_integral_abs_deriv_mul
      (hembTest e) hB (Filter.Eventually.of_forall fun x _ => hφnn x) (hIntφ (⇑e '' B))
      (fun x hx => (hder_pos x (hBsub hx)).mono hBsub)
  have hcomap_e₂ : ∀ B : Set ℝ, MeasurableSet B → B ⊆ Set.Ioi 0 →
      (Measure.comap ⇑e₂
          (volume.withDensity (fun x => ENNReal.ofReal (gaussianPDFReal 0 1 x)))) B
        = ENNReal.ofReal
            (∫ x in B, |(-((2 * Real.sqrt x)⁻¹) : ℝ)| * gaussianPDFReal 0 1 (⇑e₂ x)) := by
    intro B hB hBsub
    exact MeasurableEmbedding.withDensity_ofReal_comap_apply_eq_integral_abs_deriv_mul
      (hembTest e₂) hB (Filter.Eventually.of_forall fun x _ => hφnn x) (hIntφ (⇑e₂ '' B))
      (fun x hx => (hder_neg x (hBsub hx)).mono hBsub)
  have hψclosed : ∀ x : ℝ, 0 < x → gammaConvDensity (((1 : ℕ) : ℝ) / 2) x
      = (Real.sqrt (2 * Real.pi))⁻¹ *
          (Real.rpow x (-(1 / 2)) * Real.exp (-(1 / 2) * x)) := by
    intro x hx
    rw [hPsi x, gaussianPDFReal_def]
    have hc1 : ((1 : NNReal) : ℝ) = 1 := by norm_num
    simp only [hc1, mul_one, sub_zero]
    have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
    rw [hsq]
    have hspos : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx
    have hpow : Real.rpow x (-(1 / 2)) = (Real.sqrt x)⁻¹ := by
      have h1 : Real.rpow x (-(1 / 2)) = (Real.rpow x (1 / 2))⁻¹ := Real.rpow_neg hx.le (1 / 2)
      rw [h1, show Real.rpow x (1 / 2) = Real.sqrt x from (Real.sqrt_eq_rpow x).symm]
    rw [hpow]
    rw [show -(1 / 2) * x = -(x / 2) by ring]
    have hsx : (2 * Real.sqrt x) ≠ 0 := by positivity
    field_simp
  have hInt0 : IntegrableOn (fun x : ℝ => Real.rpow x (-(1 / 2)) * Real.exp (-(1 / 2) * x))
      (Set.Ioi 0) ℙ := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := -(1 / 2)) (b := (1 / 2))
      (by norm_num) (by norm_num) (by norm_num)
    simpa [Real.rpow_one] using h
  have hIntψ : IntegrableOn (fun s : ℝ => gammaConvDensity (((1 : ℕ) : ℝ) / 2) s) (Set.Ioi 0) ℙ := by
    have hbase : IntegrableOn
        (fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ *
          (Real.rpow x (-(1 / 2)) * Real.exp (-(1 / 2) * x))) (Set.Ioi 0) ℙ :=
      hInt0.const_mul _
    exact hbase.congr_fun (fun x hx => (hψclosed x hx).symm) measurableSet_Ioi
  have hInt2H : ∀ B : Set ℝ, MeasurableSet B → B ⊆ Set.Ioi 0 →
      IntegrableOn
        (fun x : ℝ => 2 * ((2 * Real.sqrt x)⁻¹ * gaussianPDFReal 0 1 (Real.sqrt x))) B ℙ := by
    intro B hB hBsub
    have h1 : IntegrableOn (fun s : ℝ => gammaConvDensity (((1 : ℕ) : ℝ) / 2) s) B ℙ :=
      hIntψ.mono hBsub le_rfl
    exact h1.congr_fun (fun x _ => hPsi x) hB
  have hLHS : ∀ B : Set ℝ, MeasurableSet B → B ⊆ Set.Ioi 0 →
      (Measure.map (fun z : ℝ => z ^ 2) (gaussianReal 0 1)) B
        = ENNReal.ofReal
            (∫ x in B, |((2 * Real.sqrt x)⁻¹ : ℝ)| * gaussianPDFReal 0 1 (⇑e x))
          + ENNReal.ofReal
            (∫ x in B, |(-((2 * Real.sqrt x)⁻¹) : ℝ)| * gaussianPDFReal 0 1 (⇑e₂ x)) := by
    intro B hB hBsub
    have hdisj : Disjoint (⇑e '' B) (⇑e₂ '' B) := by
      rw [Set.disjoint_left]
      intro z hz1 hz2
      obtain ⟨b1, hb1, rfl⟩ := hz1
      obtain ⟨b2, hb2, h2⟩ := hz2
      have hb1pos : (0 : ℝ) < b1 := hBsub hb1
      have hb2pos : (0 : ℝ) < b2 := hBsub hb2
      have hleft : ⇑e₂ b2 = -Real.sqrt b2 := by
        show ⇑e (-b2) = -Real.sqrt b2
        rw [he_neg (-b2) (by linarith : -b2 < 0), neg_neg]
      have hright : ⇑e b1 = Real.sqrt b1 := he_pos b1 hb1pos
      have h2' : -Real.sqrt b2 = Real.sqrt b1 := by
        rw [← hleft, ← hright]
        exact h2
      have hp : (0 : ℝ) < Real.sqrt b2 := Real.sqrt_pos.2 hb2pos
      have hn : (0 : ℝ) ≤ Real.sqrt b1 := Real.sqrt_nonneg b1
      linarith
    calc (Measure.map (fun z : ℝ => z ^ 2) (gaussianReal 0 1)) B
        = gaussianReal 0 1 ((fun z : ℝ => z ^ 2) ⁻¹' B) :=
          Measure.map_apply (by measurability : Measurable fun z : ℝ => z ^ 2) hB
      _ = gaussianReal 0 1 (⇑e '' B ∪ ⇑e₂ '' B) := by rw [hsqid B hBsub]
      _ = gaussianReal 0 1 (⇑e '' B) + gaussianReal 0 1 (⇑e₂ '' B) :=
          measure_union (μ := gaussianReal 0 1) hdisj (himg₂_meas B hB)
      _ = Measure.comap ⇑e (gaussianReal 0 1) B + Measure.comap ⇑e₂ (gaussianReal 0 1) B := by
          rw [← hcomapTest (hembTest e) (gaussianReal 0 1) B,
            ← hcomapTest (hembTest e₂) (gaussianReal 0 1) B]
      _ = ENNReal.ofReal
            (∫ x in B, |((2 * Real.sqrt x)⁻¹ : ℝ)| * gaussianPDFReal 0 1 (⇑e x))
          + ENNReal.ofReal
            (∫ x in B, |(-((2 * Real.sqrt x)⁻¹) : ℝ)| * gaussianPDFReal 0 1 (⇑e₂ x)) := by
          rw [hgauss, hcomap_e B hB hBsub, hcomap_e₂ B hB hBsub]
  have hψnn : ∀ x : ℝ, 0 ≤ gammaConvDensity (((1 : ℕ) : ℝ) / 2) x := by
    intro x
    rw [hPsi x]
    have hsp : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
    have h1 : (0 : ℝ) ≤ (2 * Real.sqrt x)⁻¹ := inv_nonneg.2 (by positivity)
    have h2 : (0 : ℝ) ≤ gaussianPDFReal 0 1 (Real.sqrt x) := hφnn _
    nlinarith
  have hmain : ∀ B : Set ℝ, MeasurableSet B → B ⊆ Set.Ioi 0 →
      (Measure.map (fun z : ℝ => z ^ 2) (gaussianReal 0 1)) B
        = (volume.withDensity
            (fun s : ℝ => ENNReal.ofReal (gammaConvDensity (((1 : ℕ) : ℝ) / 2) s))) B := by
    intro B hB hBsub
    have hνB : (volume.withDensity
          (fun s : ℝ => ENNReal.ofReal (gammaConvDensity (((1 : ℕ) : ℝ) / 2) s))) B
        = ENNReal.ofReal (∫ x in B, gammaConvDensity (((1 : ℕ) : ℝ) / 2) x) := by
      rw [withDensity_apply _ hB]
      exact (ofReal_integral_eq_lintegral_ofReal (hIntψ.mono hBsub le_rfl)
        (Filter.Eventually.of_forall hψnn)).symm
    rw [hLHS B hB hBsub, hνB]
    have hG1 : (∫ x in B, |((2 * Real.sqrt x)⁻¹ : ℝ)| * gaussianPDFReal 0 1 (⇑e x))
        = ∫ x in B, (2 * Real.sqrt x)⁻¹ * gaussianPDFReal 0 1 (Real.sqrt x) := by
      refine setIntegral_congr_fun hB (fun x hx => ?_)
      have hx0 : (0 : ℝ) < x := hBsub hx
      rw [abs_of_pos (by positivity : (0 : ℝ) < (2 * Real.sqrt x)⁻¹), he_pos x hx0]
    have hG2 : (∫ x in B, |(-((2 * Real.sqrt x)⁻¹) : ℝ)| * gaussianPDFReal 0 1 (⇑e₂ x))
        = ∫ x in B, (2 * Real.sqrt x)⁻¹ * gaussianPDFReal 0 1 (Real.sqrt x) := by
      refine setIntegral_congr_fun hB (fun x hx => ?_)
      have hx0 : (0 : ℝ) < x := hBsub hx
      have hphi : ⇑e₂ x = -Real.sqrt x := by
        show ⇑e (-x) = -Real.sqrt x
        rw [he_neg (-x) (by linarith : -x < 0), neg_neg]
      rw [hphi, hφeven (Real.sqrt x), abs_neg,
        abs_of_pos (by positivity : (0 : ℝ) < (2 * Real.sqrt x)⁻¹)]
    have hψ2 : (∫ x in B, gammaConvDensity (((1 : ℕ) : ℝ) / 2) x)
        = ∫ x in B, 2 * ((2 * Real.sqrt x)⁻¹ * gaussianPDFReal 0 1 (Real.sqrt x)) := by
      refine setIntegral_congr_fun hB (fun x _ => hPsi x)
    have htwo : (∫ x in B, 2 * ((2 * Real.sqrt x)⁻¹ * gaussianPDFReal 0 1 (Real.sqrt x)))
        = 2 * ∫ x in B, (2 * Real.sqrt x)⁻¹ * gaussianPDFReal 0 1 (Real.sqrt x) :=
      integral_const_mul 2 _
    have hsum : (∫ x in B, |((2 * Real.sqrt x)⁻¹ : ℝ)| * gaussianPDFReal 0 1 (⇑e x))
        + (∫ x in B, |(-((2 * Real.sqrt x)⁻¹) : ℝ)| * gaussianPDFReal 0 1 (⇑e₂ x))
        = ∫ x in B, gammaConvDensity (((1 : ℕ) : ℝ) / 2) x := by
      rw [hG1, hG2, hψ2, htwo]
      ring
    have hn1 : (0 : ℝ) ≤ ∫ x in B, |((2 * Real.sqrt x)⁻¹ : ℝ)| * gaussianPDFReal 0 1 (⇑e x) := by
      refine integral_nonneg (fun x => ?_)
      have h := hφnn (⇑e x)
      positivity
    have hn2 : (0 : ℝ) ≤ ∫ x in B, |(-((2 * Real.sqrt x)⁻¹) : ℝ)| * gaussianPDFReal 0 1 (⇑e₂ x) := by
      refine integral_nonneg (fun x => ?_)
      have h := hφnn (⇑e₂ x)
      positivity
    rw [← ENNReal.ofReal_add hn1 hn2, hsum]
  refine Measure.ext ?_
  intro A hA
  let μs : Measure ℝ := Measure.map (fun z : ℝ => z ^ 2) (gaussianReal 0 1)
  let ν : Measure ℝ := volume.withDensity
    (fun s : ℝ => ENNReal.ofReal (gammaConvDensity (((1 : ℕ) : ℝ) / 2) s))
  change μs A = ν A
  have hIiom : MeasurableSet (A ∩ Set.Ioi 0) := hA.inter measurableSet_Ioi
  have hdif : MeasurableSet (A \ Set.Ioi 0) := hA.diff measurableSet_Ioi
  have hd : Disjoint (A ∩ Set.Ioi 0) (A \ Set.Ioi 0) := by
    rw [Set.disjoint_left]
    intro z hz hz'
    exact hz'.2 hz.2
  have hunion : A ∩ Set.Ioi 0 ∪ (A \ Set.Ioi 0) = A := by
    ext z
    constructor
    · intro hz
      rcases hz with hz | hz
      · exact hz.1
      · exact hz.1
    · intro hz
      by_cases h : z ∈ Set.Ioi 0
      · exact Or.inl ⟨hz, h⟩
      · exact Or.inr ⟨hz, h⟩
  have hz1 : μs (A \ Set.Ioi 0) = 0 := by
    rw [Measure.map_apply hsq_meas hdif]
    refine measure_mono_null ?_ hμsing
    intro z hz
    have hle : z ^ 2 ≤ 0 := not_lt.1 hz.2
    have hzero : z ^ 2 = 0 := le_antisymm hle (sq_nonneg z)
    have h2 : z * z = 0 := by rw [← pow_two]; exact hzero
    have hz0 : z = 0 := by rcases mul_eq_zero.1 h2 with h | h <;> exact h
    simp [hz0]
  have hz2 : ν (A \ Set.Ioi 0) = 0 := by
    rw [withDensity_apply _ hdif]
    have hind : (A \ Set.Ioi 0).indicator
        (fun x => ENNReal.ofReal (gammaConvDensity (((1 : ℕ) : ℝ) / 2) x)) = 0 := by
      funext x
      by_cases hx : x ∈ A \ Set.Ioi 0
      · rw [Set.indicator_of_mem hx, hψ_nonpos x hx.2]
        exact ENNReal.ofReal_zero
      · simp [hx]
    rw [← lintegral_indicator hdif, hind]
    exact lintegral_zero
  have hsplitμ : μs A = μs (A ∩ Set.Ioi 0) := by
    have h := measure_union (μ := μs) hd hdif
    rw [hunion, hz1, add_zero] at h
    exact h
  have hsplitν : ν A = ν (A ∩ Set.Ioi 0) := by
    have h := measure_union (μ := ν) hd hdif
    rw [hunion, hz2, add_zero] at h
    exact h
  rw [hsplitμ, hsplitν]
  exact hmain (A ∩ Set.Ioi 0) hIiom (Set.inter_subset_right)
  /- @proof-region region.target-node.session.a32a33d8263b6097 end -/
