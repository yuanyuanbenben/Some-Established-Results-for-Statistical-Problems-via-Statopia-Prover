import Mathlib

/- Offline Bayes squeeze. No assumptions about the Dirichlet process are hidden
here: the testing and evidence estimates must be supplied by their own proofs. -/
open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section
namespace OfflineDPContraction

/-- Changing both numerator and denominator to truth-density likelihood ratios
does not change Bayes' quotient on the true distribution's positive-density set. -/
theorem normalized_bayes_quotient (a b r : ℝ≥0∞) (hr : r ≠ 0) (hrt : r ≠ ∞) :
    (a / r) / (b / r) = a / b := by
  simp only [div_eq_mul_inv]
  rw [ENNReal.mul_inv (Or.inr (ENNReal.inv_ne_top.mpr hr))
    (Or.inr (ENNReal.inv_ne_zero.mpr hrt)), inv_inv]
  calc (a * r⁻¹) * (b⁻¹ * r) = (a * b⁻¹) * (r⁻¹ * r) := by ac_rfl
       _ = a * b⁻¹ := by rw [ENNReal.inv_mul_cancel hr hrt, mul_one]

/-- Tonelli transfers a uniform type-II testing bound to the integrated latent
numerator. The likelihood ratio loses mass only where the true density is zero,
so an inequality is sufficient and no global positive-density assumption occurs. -/
theorem tested_numerator_bound {Z H : Type*} [MeasurableSpace Z]
    [MeasurableSpace H] (μ : Measure Z) [SigmaFinite μ]
    (π : Measure H) [IsProbabilityMeasure π]
    (p0 : Z → ℝ≥0∞) (hp0 : Measurable p0)
    (L : H → Z → ℝ≥0∞) (hL : Measurable (Function.uncurry L))
    (B : Set H) (hB : MeasurableSet B) (T : Set Z) (hT : MeasurableSet T)
    (e : ℝ≥0∞) (htest : ∀ θ ∈ B, ∫⁻ x in Tᶜ, L θ x ∂μ ≤ e) :
    ∫⁻ x in Tᶜ, (∫⁻ θ in B, L θ x / p0 x ∂π) ∂μ.withDensity p0 ≤ e := by
  have hNm : Measurable (fun x => ∫⁻ θ in B, L θ x / p0 x ∂π) :=
    (hL.div (hp0.comp measurable_snd)).lintegral_prod_left
  rw [setLIntegral_withDensity_eq_setLIntegral_mul μ hp0 hNm hT.compl]
  calc
    ∫⁻ x in Tᶜ, (p0 * fun x => ∫⁻ θ in B, L θ x / p0 x ∂π) x ∂μ
        ≤ ∫⁻ x in Tᶜ, ∫⁻ θ in B, L θ x ∂π ∂μ := by
      apply lintegral_mono
      intro x
      change p0 x * (∫⁻ θ in B, L θ x / p0 x ∂π) ≤ _
      have hLm : Measurable (fun θ : H => L θ x / p0 x) :=
        (hL.comp (measurable_id.prodMk (measurable_const (a := x)))).div_const _
      rw [← lintegral_const_mul (p0 x) hLm]
      apply lintegral_mono
      intro θ
      calc p0 x * (L θ x / p0 x) = (p0 x * (p0 x)⁻¹) * L θ x := by
            simp only [div_eq_mul_inv]; ac_rfl
           _ ≤ L θ x := by
            simpa using mul_le_mul_right' (ENNReal.mul_inv_le_one (p0 x)) (L θ x)
    _ = ∫⁻ θ in B, ∫⁻ x in Tᶜ, L θ x ∂μ ∂π :=
      lintegral_lintegral_swap (hL.comp (measurable_snd.prodMk measurable_fst)).aemeasurable
    _ ≤ ∫⁻ θ in B, e ∂π := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hB] with θ hθ
      exact htest θ hθ
    _ ≤ e := by
      simp only [lintegral_const, Measure.restrict_apply_univ]
      calc e * π B ≤ e * 1 := mul_le_mul_left' (prob_le_one) e
           _ = e := mul_one e

/-- A finite-sample posterior bound. `N` and `D` are likelihood ratios relative
to the true sampling density, and `T` is the rejecting event of a test. -/
theorem posterior_probability_bound {Z : Type*} [MeasurableSpace Z]
    (ν : Measure Z) (u N D : Z → ℝ≥0∞) (T : Set Z)
    (hT : MeasurableSet T) (hN : AEMeasurable N ν)
    (hBayes : ∀ᵐ x ∂ν, u x = N x / D x)
    (ε a e : ℝ≥0∞) (hε : ε ≠ 0) (hεtop : ε ≠ ∞)
    (ha : a ≠ 0) (hatop : a ≠ ∞)
    (hsmall : ∫⁻ x in Tᶜ, N x ∂ν ≤ e) :
    ν {x | ε < u x} ≤ ν T + ν {x | D x < a} + e / (ε * a) := by
  classical
  let R : Z → ℝ≥0∞ := Tᶜ.indicator N
  have hR : AEMeasurable R ν := hN.indicator hT.compl
  have hinc : ∀ᵐ x ∂ν, ε < u x →
      x ∈ T ∪ {x | D x < a} ∪ {x | ε * a ≤ R x} := by
    filter_upwards [hBayes] with x hx hxu
    by_cases hxT : x ∈ T
    · exact Or.inl (Or.inl hxT)
    by_cases hxD : D x < a
    · exact Or.inl (Or.inr hxD)
    · apply Or.inr
      have hNgt : ε * D x < N x := ENNReal.mul_lt_of_lt_div (hx ▸ hxu)
      simpa [R, Set.indicator_of_mem (Set.mem_compl hxT)] using
        (le_trans (mul_le_mul_left' (not_lt.mp hxD) ε) hNgt.le)
  have hmeasure : ν {x | ε < u x} ≤
      ν T + ν {x | D x < a} + ν {x | ε * a ≤ R x} := by
    exact (measure_mono_ae hinc).trans
      ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl))
  have hmarkov : ν {x | ε * a ≤ R x} ≤ e / (ε * a) := by
    refine (meas_ge_le_lintegral_div hR (mul_ne_zero hε ha)
      (ENNReal.mul_ne_top hεtop hatop)).trans ?_
    apply ENNReal.div_le_div_right
    simpa [R, lintegral_indicator hT.compl] using hsmall
  exact hmeasure.trans (add_le_add le_rfl hmarkov)

/-- Exponentially consistent tests and a subexponential evidence lower bound
imply posterior convergence in probability. Different sample spaces are allowed
for each sample size; in particular `Z n = Fin n → X`. -/
theorem posterior_tendsto_zero {Z : ℕ → Type*} [∀ n, MeasurableSpace (Z n)]
    (ν : ∀ n, Measure (Z n))
    (u N D : ∀ n, Z n → ℝ≥0∞) (T : ∀ n, Set (Z n))
    (hT : ∀ n, MeasurableSet (T n))
    (hN : ∀ n, AEMeasurable (N n) (ν n))
    (hBayes : ∀ n, ∀ᵐ x ∂ν n, u n x = N n x / D n x)
    (c : ℝ) (hc : 0 < c)
    (htest : Tendsto (fun n => ν n (T n)) atTop (𝓝 0))
    (hevidence : Tendsto (fun n => ν n {x | D n x <
      ENNReal.ofReal (Real.exp (-(n : ℝ) * (c / 2)))}) atTop (𝓝 0))
    (hsmall : ∀ᶠ n in atTop, ∫⁻ x in (T n)ᶜ, N n x ∂ν n ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ) * c))) :
    ∀ ε : ℝ≥0∞, 0 < ε →
      Tendsto (fun n => ν n {x | ε < u n x}) atTop (𝓝 0) := by
  intro ε hε
  by_cases hεtop : ε = ∞
  · subst ε
    simpa only [not_top_lt, Set.setOf_false, measure_empty] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
  have hreal : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ) * (c / 2)))
      atTop (𝓝 0) := by
    have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one
      (le_of_lt (Real.exp_pos (-(c / 2))))
      (Real.exp_lt_one_iff.mpr (by linarith : -(c / 2) < 0))
    convert hpow using 1
    funext n
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hratioEq : ∀ n : ℕ,
      ENNReal.ofReal (Real.exp (-(n : ℝ) * c)) /
        (ε * ENNReal.ofReal (Real.exp (-(n : ℝ) * (c / 2)))) =
      ENNReal.ofReal (Real.exp (-(n : ℝ) * (c / 2))) / ε := by
    intro n
    let b : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(n : ℝ) * (c / 2)))
    have hb : b ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
    have hbt : b ≠ ∞ := ENNReal.ofReal_ne_top
    have hsplit : ENNReal.ofReal (Real.exp (-(n : ℝ) * c)) = b * b := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2
      ring
    change ENNReal.ofReal (Real.exp (-(n : ℝ) * c)) / (ε * b) = b / ε
    rw [hsplit, ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl hε.ne') (Or.inl hεtop)]
    calc (ε⁻¹ * b⁻¹) * (b * b) = ε⁻¹ * (b⁻¹ * b) * b := by ac_rfl
         _ = b / ε := by rw [ENNReal.inv_mul_cancel hb hbt]; simp [div_eq_mul_inv, mul_comm]
  have hratio : Tendsto (fun n : ℕ =>
      ENNReal.ofReal (Real.exp (-(n : ℝ) * c)) /
        (ε * ENNReal.ofReal (Real.exp (-(n : ℝ) * (c / 2))))) atTop (𝓝 0) := by
    simp_rw [hratioEq]
    simpa using ENNReal.Tendsto.div_const ((ENNReal.continuous_ofReal.tendsto 0).comp hreal) (Or.inr hε.ne')
  have hsum := (htest.add hevidence).add hratio
  simp only [zero_add] at hsum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Filter.Eventually.of_forall (fun n => zero_le _))
  filter_upwards [hsmall] with n hn
  exact posterior_probability_bound (ν n) (u n) (N n) (D n) (T n)
    (hT n) (hN n) (hBayes n) ε _ _ hε.ne' hεtop
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne' ENNReal.ofReal_ne_top hn

end OfflineDPContraction
