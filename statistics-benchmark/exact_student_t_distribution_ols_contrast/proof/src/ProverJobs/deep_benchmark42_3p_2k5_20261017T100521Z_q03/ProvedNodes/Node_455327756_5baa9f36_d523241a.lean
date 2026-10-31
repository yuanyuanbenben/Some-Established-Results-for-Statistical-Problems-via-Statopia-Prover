import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q03.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q03.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q03.ProvedNodes.Node_3678446978_c1498b57_7ef4111b
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q03.ProvedNodes.Node_924557408_b0ba29a0_ec009e92


open MeasureTheory Matrix ProbabilityTheory

open MeasureTheory Matrix ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_455327756_5baa9f36 : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n p : ℕ) (hnp : p < n)
    (X : Matrix (Fin n) (Fin p) ℝ) (hX : Function.Injective X.mulVec)
    (a : Fin p → ℝ) (ha : a ≠ 0)
    (sigma : ℝ) (hsigma : 0 < sigma)
    (epsilon : Ω → Fin n → ℝ)
    (hgaussian : ∀ b : Fin n → ℝ,
      HasLaw (fun ω => dotProduct b (epsilon ω))
        (gaussianReal 0 (Real.toNNReal (sigma ^ 2 * dotProduct b b))) P)
    (v : Fin (n - p) → (Fin n → ℝ))
    (hv1 : ∀ k : Fin (n - p), dotProduct (v k) (v k) = 1)
    (hv2 : ∀ k l : Fin (n - p), k ≠ l → dotProduct (v k) (v l) = 0)
    (hvu : ∀ k : Fin (n - p),
      dotProduct (X *ᵥ ((X.transpose * X)⁻¹ *ᵥ a)) (v k) = 0)
    (huu : dotProduct (X *ᵥ ((X.transpose * X)⁻¹ *ᵥ a))
        (X *ᵥ ((X.transpose * X)⁻¹ *ᵥ a))
      = dotProduct a ((X.transpose * X)⁻¹ *ᵥ a))
    (hqpos : 0 < dotProduct a ((X.transpose * X)⁻¹ *ᵥ a)),
    HasLaw
      (fun ω =>
        (dotProduct (X *ᵥ ((X.transpose * X)⁻¹ *ᵥ a)) (epsilon ω) /
            (sigma * Real.sqrt (dotProduct a ((X.transpose * X)⁻¹ *ᵥ a))),
          ∑ k : Fin (n - p), (dotProduct (v k) (epsilon ω) / sigma) ^ 2))
      ((gaussianReal 0 1).prod
        (volume.withDensity
          (fun s => ENNReal.ofReal (gammaConvDensity (((n - p : ℕ) : ℝ) / 2) s)))) P := by
  /- @proof-region region.target-node.session.20cfb3ecbee095ba begin -/
  intro Ω _ P _ n p hnp X hX a ha sigma hsigma epsilon hgaussian v hv1 hv2 hvu huu hqpos
  set M : Matrix (Fin p) (Fin p) ℝ := (X.transpose * X)⁻¹
  set u : Fin n → ℝ := X *ᵥ (M *ᵥ a)
  set q : ℝ := dotProduct a (M *ᵥ a)
  have hq : 0 < q := hqpos
  have hsig_ne : sigma ≠ 0 := ne_of_gt hsigma
  have hs_pos : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  have hsq : Real.sqrt q ^ 2 = q := Real.sq_sqrt (le_of_lt hq)
  have hsmul_dot : ∀ (c : ℝ) (x y : Fin n → ℝ), dotProduct (c • x) y = c * dotProduct x y := by
    intro c x y
    rw [dotProduct_comm (c • x) y, dotProduct_smul, smul_eq_mul, dotProduct_comm x y]
  let w : Fin 1 → Fin n → ℝ := fun _ => (sigma * Real.sqrt q)⁻¹ • u
  let w2 : Fin (n - p) → Fin n → ℝ := fun k => sigma⁻¹ • v k
  have hone : ∀ i j : Fin 1, i = j := fun i j => Fin.ext (by omega)
  have hw_orth : ∀ i j : Fin 1, i ≠ j → dotProduct (w i) (w j) = 0 := by
    intro i j hij
    exact absurd (hone i j) hij
  have hw2_orth : ∀ a b : Fin (n - p), a ≠ b → dotProduct (w2 a) (w2 b) = 0 := by
    intro a b hab
    show dotProduct (sigma⁻¹ • v a) (sigma⁻¹ • v b) = 0
    rw [hsmul_dot, dotProduct_smul, smul_eq_mul, hv2 a b hab, mul_zero, mul_zero]
  have hw_w2_orth : ∀ (i : Fin 1) (a : Fin (n - p)), dotProduct (w i) (w2 a) = 0 := by
    intro i a
    show dotProduct ((sigma * Real.sqrt q)⁻¹ • u) (sigma⁻¹ • v a) = 0
    rw [hsmul_dot, dotProduct_smul, smul_eq_mul, hvu a, mul_zero, mul_zero]
  have hvar_w : ∀ i : Fin 1, sigma ^ 2 * dotProduct (w i) (w i) = 1 := by
    intro i
    have h1 : dotProduct (w i) (w i) = ((sigma * Real.sqrt q)⁻¹) ^ 2 * q := by
      show dotProduct ((sigma * Real.sqrt q)⁻¹ • u) ((sigma * Real.sqrt q)⁻¹ • u)
          = ((sigma * Real.sqrt q)⁻¹) ^ 2 * q
      rw [hsmul_dot, dotProduct_smul, smul_eq_mul, huu]
      ring
    rw [h1, inv_pow]
    have ha2 : (sigma * Real.sqrt q) ^ 2 = sigma ^ 2 * q := by rw [mul_pow, hsq]
    rw [ha2]
    have hne : sigma ^ 2 * q ≠ 0 := by
      have hpos : 0 < sigma ^ 2 * q := by positivity
      exact ne_of_gt hpos
    calc sigma ^ 2 * ((sigma ^ 2 * q)⁻¹ * q) = (sigma ^ 2 * q) * (sigma ^ 2 * q)⁻¹ := by ring
      _ = 1 := mul_inv_cancel₀ hne
  have hvar_w2 : ∀ k : Fin (n - p), sigma ^ 2 * dotProduct (w2 k) (w2 k) = 1 := by
    intro k
    have h1 : dotProduct (w2 k) (w2 k) = (sigma ^ 2)⁻¹ := by
      show dotProduct (sigma⁻¹ • v k) (sigma⁻¹ • v k) = (sigma ^ 2)⁻¹
      rw [hsmul_dot, dotProduct_smul, smul_eq_mul, hv1 k, ← inv_pow]
      ring
    rw [h1]
    exact mul_inv_cancel₀ (pow_ne_zero 2 hsig_ne)
  have hblock := statopia_math_node_924557408_b0ba29a0 P n epsilon sigma hsigma hgaussian 1 (n - p)
    w w2 hw_orth hw2_orth hw_w2_orth
  have hμ1 : Measure.pi (fun i : Fin 1 =>
      gaussianReal 0 (Real.toNNReal (sigma ^ 2 * dotProduct (w i) (w i))))
      = Measure.pi (fun _ : Fin 1 => gaussianReal 0 1) := by
    have hfun : (fun i : Fin 1 =>
        gaussianReal 0 (Real.toNNReal (sigma ^ 2 * dotProduct (w i) (w i))))
        = (fun _ : Fin 1 => gaussianReal 0 1) := by
      funext i
      rw [hvar_w i]
      simp
    rw [hfun]
  have hμ2 : Measure.pi (fun a : Fin (n - p) =>
      gaussianReal 0 (Real.toNNReal (sigma ^ 2 * dotProduct (w2 a) (w2 a))))
      = Measure.pi (fun _ : Fin (n - p) => gaussianReal 0 1) := by
    have hfun : (fun a : Fin (n - p) =>
        gaussianReal 0 (Real.toNNReal (sigma ^ 2 * dotProduct (w2 a) (w2 a))))
        = (fun _ : Fin (n - p) => gaussianReal 0 1) := by
      funext k
      rw [hvar_w2 k]
      simp
    rw [hfun]
  have hpair : HasLaw
      (fun ω => ((fun i : Fin 1 => dotProduct (w i) (epsilon ω)),
        (fun a : Fin (n - p) => dotProduct (w2 a) (epsilon ω))))
      ((Measure.pi (fun _ : Fin 1 => gaussianReal 0 1)).prod
        (Measure.pi (fun _ : Fin (n - p) => gaussianReal 0 1))) P := by
    rw [← hμ1, ← hμ2]
    exact hblock
  have hE_map : Measure.map (fun y : Fin 1 → ℝ => y (default : Fin 1))
      (Measure.pi (fun _ : Fin 1 => gaussianReal 0 1)) = gaussianReal 0 1 := by
    simpa using (measurePreserving_piUnique (fun _ : Fin 1 => gaussianReal 0 1)).map_eq
  have hchi : Measure.map (fun y : Fin (n - p) → ℝ => ∑ k : Fin (n - p), (y k) ^ 2)
      (Measure.pi (fun _ : Fin (n - p) => gaussianReal 0 1))
      = volume.withDensity
          (fun s => ENNReal.ofReal (gammaConvDensity (((n - p : ℕ) : ℝ) / 2) s)) :=
    statopia_math_node_3678446978_c1498b57 (n - p) (by omega)
  have hE_meas : Measurable (fun y : Fin 1 → ℝ => y (default : Fin 1)) := by fun_prop
  have hS_meas : Measurable (fun y : Fin (n - p) → ℝ => ∑ k : Fin (n - p), (y k) ^ 2) := by
    fun_prop
  have hY : HasLaw
      (fun z : (Fin 1 → ℝ) × (Fin (n - p) → ℝ) =>
        (z.1 (default : Fin 1), ∑ k : Fin (n - p), (z.2 k) ^ 2))
      ((gaussianReal 0 1).prod
        (volume.withDensity
          (fun s => ENNReal.ofReal (gammaConvDensity (((n - p : ℕ) : ℝ) / 2) s))))
      ((Measure.pi (fun _ : Fin 1 => gaussianReal 0 1)).prod
        (Measure.pi (fun _ : Fin (n - p) => gaussianReal 0 1))) := by
    have hm := MeasureTheory.Measure.map_prod_map
      (f := fun y : Fin 1 → ℝ => y (default : Fin 1))
      (g := fun y : Fin (n - p) → ℝ => ∑ k : Fin (n - p), (y k) ^ 2)
      (Measure.pi (fun _ : Fin 1 => gaussianReal 0 1))
      (Measure.pi (fun _ : Fin (n - p) => gaussianReal 0 1)) hE_meas hS_meas
    rw [hE_map, hchi] at hm
    have hfun : (fun z : (Fin 1 → ℝ) × (Fin (n - p) → ℝ) =>
        (z.1 (default : Fin 1), ∑ k : Fin (n - p), (z.2 k) ^ 2))
        = Prod.map (fun y : Fin 1 → ℝ => y (default : Fin 1))
            (fun y : Fin (n - p) → ℝ => ∑ k : Fin (n - p), (y k) ^ 2) := by
      funext z
      obtain ⟨a, b⟩ := z
      rfl
    rw [← hfun] at hm
    refine MeasureTheory.MeasurePreserving.hasLaw ⟨?_, ?_⟩
    · fun_prop
    · exact hm.symm
  have hcomp := ProbabilityTheory.HasLaw.comp hY hpair
  refine ProbabilityTheory.HasLaw.congr hcomp ?_
  filter_upwards with ω
  have h1 : dotProduct u (epsilon ω) / (sigma * Real.sqrt q)
      = dotProduct (w (default : Fin 1)) (epsilon ω) := by
    show dotProduct u (epsilon ω) / (sigma * Real.sqrt q)
        = dotProduct ((sigma * Real.sqrt q)⁻¹ • u) (epsilon ω)
    rw [hsmul_dot, inv_mul_eq_div]
  have h2 : (∑ k : Fin (n - p), (dotProduct (v k) (epsilon ω) / sigma) ^ 2)
      = ∑ k : Fin (n - p), (dotProduct (w2 k) (epsilon ω)) ^ 2 := by
    refine Finset.sum_congr rfl ?_
    intro k _
    show (dotProduct (v k) (epsilon ω) / sigma) ^ 2
        = (dotProduct (sigma⁻¹ • v k) (epsilon ω)) ^ 2
    rw [hsmul_dot, inv_mul_eq_div]
  exact Prod.ext h1 h2
  /- @proof-region region.target-node.session.20cfb3ecbee095ba end -/
