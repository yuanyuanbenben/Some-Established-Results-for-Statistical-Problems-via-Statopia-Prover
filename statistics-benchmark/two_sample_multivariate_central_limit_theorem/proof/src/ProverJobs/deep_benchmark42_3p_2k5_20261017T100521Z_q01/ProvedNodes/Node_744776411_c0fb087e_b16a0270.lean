import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q01.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q01.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q01.ProvedNodes.Node_2158809186_10a872fc_de5de311
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q01.ProvedNodes.Node_2755252338_b98666b0_79251434
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q01.ProvedNodes.Node_3456905758_2fd530dc_a1c83014



open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

set_option autoImplicit false in
theorem statopia_math_node_744776411_c0fb087e : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (d : ℕ)
    (X Y : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (cov : Matrix (Fin d) (Fin d) ℝ)
    (m n : ℕ → ℕ)
    (hX_meas : ∀ i, Measurable (X i))
    (hY_meas : ∀ i, Measurable (Y i))
    (hX_indep : iIndepFun X P)
    (hY_indep : iIndepFun Y P)
    (hXY_indep : IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) P)
    (hX_ident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hY_ident : ∀ i, IdentDistrib (Y i) (Y 0) P P)
    (hXY_ident : IdentDistrib (X 0) (Y 0) P P)
    (hX_second : Integrable (fun ω => ‖X 0 ω‖ ^ 2) P)
    (hX_cov : ∀ j k : Fin d,
      ∫ ω,
          (X 0 ω j - (∫ ω, X 0 ω ∂P) j) *
            (X 0 ω k - (∫ ω, X 0 ω ∂P) k) ∂P =
        cov j k)
    (hm_pos : ∀ r, 0 < m r)
    (hn_pos : ∀ r, 0 < n r)
    (hm_lim : Tendsto m atTop atTop)
    (hn_lim : Tendsto n atTop atTop),
    ∀ t : EuclideanSpace ℝ (Fin d),
      Tendsto
        (fun r : ℕ =>
          charFun
            (P.map (fun ω =>
              Real.sqrt
                  (((m r : ℝ) * (n r : ℝ)) / ((m r : ℝ) + (n r : ℝ))) •
                (((m r : ℝ)⁻¹ • ∑ i ∈ Finset.range (m r), X i ω) -
                  ((n r : ℝ)⁻¹ • ∑ j ∈ Finset.range (n r), Y j ω))))
            t)
        atTop
        (𝓝 (Complex.exp
          (-(1 / 2 : ℂ) *
            (((∑ j : Fin d, ∑ k : Fin d, t j * t k * cov j k) : ℝ) : ℂ)))) := by
  /- @proof-region region.target-node.session.b9930c478e1e19db begin -/
  intro Ω instΩ P instP d X Y cov m n hX_meas hY_meas hX_indep hY_indep hXY_indep hX_ident
    hY_ident hXY_ident hX_second hX_cov hm_pos hn_pos hm_lim hn_lim t
  classical
  have hX0_meas : Measurable (X 0) := hX_meas 0
  haveI hprob : IsProbabilityMeasure (P.map (X 0)) :=
    MeasureTheory.Measure.isProbabilityMeasure_map hX0_meas.aemeasurable
  have hmeanX : ∫ x : EuclideanSpace ℝ (Fin d), x ∂(P.map (X 0)) = ∫ ω, X 0 ω ∂P :=
    MeasureTheory.integral_map hX0_meas.aemeasurable continuous_id.aestronglyMeasurable
  have hcovX : ∀ j k : Fin d,
      ∫ x : EuclideanSpace ℝ (Fin d),
          (x j - (∫ ω, X 0 ω ∂P) j) * (x k - (∫ ω, X 0 ω ∂P) k) ∂(P.map (X 0)) =
        cov j k := by
    intro j k
    rw [MeasureTheory.integral_map hX0_meas.aemeasurable
      (f := fun x : EuclideanSpace ℝ (Fin d) =>
        (x j - (∫ ω, X 0 ω ∂P) j) * (x k - (∫ ω, X 0 ω ∂P) k))
      ((by fun_prop : Continuous (fun x : EuclideanSpace ℝ (Fin d) =>
        (x j - (∫ ω, X 0 ω ∂P) j) * (x k - (∫ ω, X 0 ω ∂P) k))).aestronglyMeasurable)]
    exact hX_cov j k
  have hsecondX : Integrable (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖ ^ 2) (P.map (X 0)) := by
    refine (MeasureTheory.integrable_map_measure
      (f := X 0) (g := fun x : EuclideanSpace ℝ (Fin d) => ‖x‖ ^ 2) ?_ hX0_meas.aemeasurable).2 ?_
    · exact (continuous_norm.pow 2).aestronglyMeasurable
    · exact hX_second
  obtain ⟨δ, hδpos, ε, hε0, hεbound, hεformula⟩ :=
    statopia_math_node_3456905758_2fd530dc d (P.map (X 0)) hsecondX
  have hchar : ∀ s : EuclideanSpace ℝ (Fin d), ‖s‖ < δ →
      charFun (P.map (X 0)) s =
        Complex.exp
          (Complex.I * (↑(inner ℝ s (∫ ω, X 0 ω ∂P)) : ℂ) -
              (1 / 2 : ℂ) *
                (∑ j : Fin d, ∑ k : Fin d, (↑(s j) : ℂ) * ↑(s k) * ↑(cov j k)) + ε s) := by
    intro s hs
    rw [hεformula s hs]
    congr 1
    simp only [hmeanX, hcovX]
  let c : ℕ → ℝ := fun r => Real.sqrt (((m r : ℝ) * (n r : ℝ)) / ((m r : ℝ) + (n r : ℝ)))
  let s1 : ℕ → EuclideanSpace ℝ (Fin d) := fun r => (c r / (m r : ℝ)) • t
  let s2 : ℕ → EuclideanSpace ℝ (Fin d) := fun r => (-(c r / (n r : ℝ))) • t
  have hc_apply : ∀ r : ℕ, c r = Real.sqrt (((m r : ℝ) * (n r : ℝ)) / ((m r : ℝ) + (n r : ℝ))) :=
    fun r => rfl
  have hs1_apply : ∀ r : ℕ, s1 r = (c r / (m r : ℝ)) • t := fun r => rfl
  have hs2_apply : ∀ r : ℕ, s2 r = (-(c r / (n r : ℝ))) • t := fun r => rfl
  have hmR_pos : ∀ r : ℕ, (0 : ℝ) < (m r : ℝ) := fun r => by exact_mod_cast hm_pos r
  have hnR_pos : ∀ r : ℕ, (0 : ℝ) < (n r : ℝ) := fun r => by exact_mod_cast hn_pos r
  have hc_nonneg : ∀ r : ℕ, 0 ≤ c r := fun r => Real.sqrt_nonneg _
  have hc_sq : ∀ r : ℕ, c r ^ 2 = ((m r : ℝ) * (n r : ℝ)) / ((m r : ℝ) + (n r : ℝ)) := by
    intro r
    rw [hc_apply r, Real.sq_sqrt]
    exact div_nonneg (mul_nonneg (hmR_pos r).le (hnR_pos r).le)
      (by linarith [hmR_pos r, hnR_pos r])
  have hnorm_s1 : ∀ r : ℕ, ‖s1 r‖ = (c r / (m r : ℝ)) * ‖t‖ := by
    intro r
    rw [hs1_apply r, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (hc_nonneg r) (le_of_lt (hmR_pos r)))]
  have hnorm_s2 : ∀ r : ℕ, ‖s2 r‖ = (c r / (n r : ℝ)) * ‖t‖ := by
    intro r
    rw [hs2_apply r, norm_smul, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg (div_nonneg (hc_nonneg r) (le_of_lt (hnR_pos r)))]
  have hmR_tendsto : Tendsto (fun r : ℕ => (m r : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hm_lim
  have hnR_tendsto : Tendsto (fun r : ℕ => (n r : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn_lim
  have hsqrt_inv_m : Tendsto (fun r : ℕ => Real.sqrt ((m r : ℝ)⁻¹)) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp
      (Filter.Tendsto.inv_tendsto_atTop hmR_tendsto)
    rw [Real.sqrt_zero] at h
    exact h
  have hsqrt_inv_n : Tendsto (fun r : ℕ => Real.sqrt ((n r : ℝ)⁻¹)) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp
      (Filter.Tendsto.inv_tendsto_atTop hnR_tendsto)
    rw [Real.sqrt_zero] at h
    exact h
  have hsq_le1 : ∀ r : ℕ, (c r / (m r : ℝ)) ^ 2 ≤ (m r : ℝ)⁻¹ := by
    intro r
    have hm := hmR_pos r
    have hn := hnR_pos r
    have hkey : c r ^ 2 ≤ (m r : ℝ) := by
      rw [hc_sq r, div_le_iff₀ (by linarith : (0 : ℝ) < (m r : ℝ) + (n r : ℝ))]
      nlinarith [hm, hn]
    rw [div_pow, div_le_iff₀ (pow_pos hm 2)]
    have h3 : (m r : ℝ)⁻¹ * (m r : ℝ) ^ 2 = (m r : ℝ) := by
      rw [pow_two, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hm), one_mul]
    rw [h3]
    exact hkey
  have hsq_le2 : ∀ r : ℕ, (c r / (n r : ℝ)) ^ 2 ≤ (n r : ℝ)⁻¹ := by
    intro r
    have hm := hmR_pos r
    have hn := hnR_pos r
    have hkey : c r ^ 2 ≤ (n r : ℝ) := by
      rw [hc_sq r, div_le_iff₀ (by linarith : (0 : ℝ) < (m r : ℝ) + (n r : ℝ))]
      nlinarith [hm, hn]
    rw [div_pow, div_le_iff₀ (pow_pos hn 2)]
    have h3 : (n r : ℝ)⁻¹ * (n r : ℝ) ^ 2 = (n r : ℝ) := by
      rw [pow_two, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hn), one_mul]
    rw [h3]
    exact hkey
  have hratio1 : Tendsto (fun r : ℕ => c r / (m r : ℝ)) atTop (𝓝 0) :=
    squeeze_zero (fun r => div_nonneg (hc_nonneg r) (le_of_lt (hmR_pos r)))
      (fun r => by
        have hnn : 0 ≤ c r / (m r : ℝ) := div_nonneg (hc_nonneg r) (le_of_lt (hmR_pos r))
        calc c r / (m r : ℝ) = Real.sqrt ((c r / (m r : ℝ)) ^ 2) := (Real.sqrt_sq hnn).symm
          _ ≤ Real.sqrt ((m r : ℝ)⁻¹) := Real.sqrt_le_sqrt (hsq_le1 r))
      hsqrt_inv_m
  have hratio2 : Tendsto (fun r : ℕ => c r / (n r : ℝ)) atTop (𝓝 0) :=
    squeeze_zero (fun r => div_nonneg (hc_nonneg r) (le_of_lt (hnR_pos r)))
      (fun r => by
        have hnn : 0 ≤ c r / (n r : ℝ) := div_nonneg (hc_nonneg r) (le_of_lt (hnR_pos r))
        calc c r / (n r : ℝ) = Real.sqrt ((c r / (n r : ℝ)) ^ 2) := (Real.sqrt_sq hnn).symm
          _ ≤ Real.sqrt ((n r : ℝ)⁻¹) := Real.sqrt_le_sqrt (hsq_le2 r))
      hsqrt_inv_n
  have hnorm_s1_tendsto : Tendsto (fun r : ℕ => ‖s1 r‖) atTop (𝓝 0) := by
    have h : Tendsto (fun r : ℕ => (c r / (m r : ℝ)) * ‖t‖) atTop (𝓝 0) := by
      simpa using hratio1.mul_const ‖t‖
    simpa only [hnorm_s1] using h
  have hnorm_s2_tendsto : Tendsto (fun r : ℕ => ‖s2 r‖) atTop (𝓝 0) := by
    have h : Tendsto (fun r : ℕ => (c r / (n r : ℝ)) * ‖t‖) atTop (𝓝 0) := by
      simpa using hratio2.mul_const ‖t‖
    simpa only [hnorm_s2] using h
  have hmR_ne : ∀ r : ℕ, (m r : ℝ) ≠ 0 := fun r => ne_of_gt (hmR_pos r)
  have hnR_ne : ∀ r : ℕ, (n r : ℝ) ≠ 0 := fun r => ne_of_gt (hnR_pos r)
  have hmn_ne : ∀ r : ℕ, (m r : ℝ) + (n r : ℝ) ≠ 0 :=
    fun r => ne_of_gt (by linarith [hmR_pos r, hnR_pos r])
  have hc2_div_m : ∀ r : ℕ, c r ^ 2 / (m r : ℝ) = (n r : ℝ) / ((m r : ℝ) + (n r : ℝ)) := by
    intro r
    have hm' : (m r : ℝ) ≠ 0 := hmR_ne r
    have hmn' : (m r : ℝ) + (n r : ℝ) ≠ 0 := hmn_ne r
    rw [hc_sq r]
    field_simp
  have hc2_div_n : ∀ r : ℕ, c r ^ 2 / (n r : ℝ) = (m r : ℝ) / ((m r : ℝ) + (n r : ℝ)) := by
    intro r
    have hn' : (n r : ℝ) ≠ 0 := hnR_ne r
    have hmn' : (m r : ℝ) + (n r : ℝ) ≠ 0 := hmn_ne r
    rw [hc_sq r]
    field_simp
  have hweight1 : ∀ r : ℕ,
      (m r : ℝ) * ‖s1 r‖ ^ 2 = ((n r : ℝ) / ((m r : ℝ) + (n r : ℝ))) * ‖t‖ ^ 2 := by
    intro r
    have hm' : (m r : ℝ) ≠ 0 := hmR_ne r
    have hm2 : (m r : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hm'
    have hkey : (m r : ℝ) * ‖s1 r‖ ^ 2 = (c r ^ 2 / (m r : ℝ)) * ‖t‖ ^ 2 := by
      rw [hnorm_s1 r, mul_pow, div_pow]
      field_simp
    rw [hkey, hc2_div_m r]
  have hweight2 : ∀ r : ℕ,
      (n r : ℝ) * ‖s2 r‖ ^ 2 = ((m r : ℝ) / ((m r : ℝ) + (n r : ℝ))) * ‖t‖ ^ 2 := by
    intro r
    have hn' : (n r : ℝ) ≠ 0 := hnR_ne r
    have hn2 : (n r : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hn'
    have hkey : (n r : ℝ) * ‖s2 r‖ ^ 2 = (c r ^ 2 / (n r : ℝ)) * ‖t‖ ^ 2 := by
      rw [hnorm_s2 r, mul_pow, div_pow]
      field_simp
    rw [hkey, hc2_div_n r]
  have hweight1_le : ∀ r : ℕ, (m r : ℝ) * ‖s1 r‖ ^ 2 ≤ ‖t‖ ^ 2 := by
    intro r
    rw [hweight1 r]
    have hle : (n r : ℝ) / ((m r : ℝ) + (n r : ℝ)) ≤ 1 := by
      rw [div_le_iff₀ (by linarith [hmR_pos r, hnR_pos r] : (0 : ℝ) < (m r : ℝ) + (n r : ℝ))]
      linarith [hmR_pos r]
    simpa using mul_le_mul_of_nonneg_right hle (by positivity : (0 : ℝ) ≤ ‖t‖ ^ 2)
  have hweight2_le : ∀ r : ℕ, (n r : ℝ) * ‖s2 r‖ ^ 2 ≤ ‖t‖ ^ 2 := by
    intro r
    rw [hweight2 r]
    have hle : (m r : ℝ) / ((m r : ℝ) + (n r : ℝ)) ≤ 1 := by
      rw [div_le_iff₀ (by linarith [hmR_pos r, hnR_pos r] : (0 : ℝ) < (m r : ℝ) + (n r : ℝ))]
      linarith [hnR_pos r]
    simpa using mul_le_mul_of_nonneg_right hle (by positivity : (0 : ℝ) ≤ ‖t‖ ^ 2)
  have hweight_sum : ∀ r : ℕ,
      (n r : ℝ) / ((m r : ℝ) + (n r : ℝ)) + (m r : ℝ) / ((m r : ℝ) + (n r : ℝ)) = 1 := by
    intro r
    have hmn' : (m r : ℝ) + (n r : ℝ) ≠ 0 := hmn_ne r
    field_simp
    ring
  have hmapX : ∀ i : ℕ, P.map (X i) = P.map (X 0) := by
    intro i
    first
      | exact (hX_ident i).map_eq
      | exact IdentDistrib.map_eq (hX_ident i)
      | exact ProbabilityTheory.IdentDistrib.map_eq (hX_ident i)
  have hmapY : ∀ i : ℕ, P.map (Y i) = P.map (Y 0) := by
    intro i
    first
      | exact (hY_ident i).map_eq
      | exact IdentDistrib.map_eq (hY_ident i)
      | exact ProbabilityTheory.IdentDistrib.map_eq (hY_ident i)
  have hmapXY : P.map (Y 0) = P.map (X 0) := by
    first
      | exact hXY_ident.map_eq
      | exact (IdentDistrib.map_eq hXY_ident).symm
      | exact (ProbabilityTheory.IdentDistrib.map_eq hXY_ident).symm
  have hfactor : ∀ r : ℕ,
      charFun (P.map (fun ω =>
        Real.sqrt (((m r : ℝ) * (n r : ℝ)) / ((m r : ℝ) + (n r : ℝ))) •
          (((m r : ℝ)⁻¹ • ∑ i ∈ Finset.range (m r), X i ω) -
            ((n r : ℝ)⁻¹ • ∑ j ∈ Finset.range (n r), Y j ω)))) t =
        (charFun (P.map (X 0)) (s1 r)) ^ (m r) * (charFun (P.map (X 0)) (s2 r)) ^ (n r) :=
    fun r => statopia_math_node_2755252338_b98666b0 P d X Y m n hX_meas hY_meas hX_indep
      hY_indep hXY_indep hmapX hmapY hmapXY hm_pos hn_pos r t
  let Qfun : EuclideanSpace ℝ (Fin d) → ℝ :=
    fun s => ∑ j : Fin d, ∑ k : Fin d, s j * s k * cov j k
  let A : ℝ := inner ℝ t (∫ ω, X 0 ω ∂P)
  let Psi : EuclideanSpace ℝ (Fin d) → ℂ := fun s =>
    Complex.I * (↑(inner ℝ s (∫ ω, X 0 ω ∂P)) : ℂ) - (1 / 2 : ℂ) * (↑(Qfun s) : ℂ)
  have hQfun_apply : ∀ s : EuclideanSpace ℝ (Fin d),
      Qfun s = ∑ j : Fin d, ∑ k : Fin d, s j * s k * cov j k := fun s => rfl
  have hPsi_apply : ∀ s : EuclideanSpace ℝ (Fin d), Psi s =
      Complex.I * (↑(inner ℝ s (∫ ω, X 0 ω ∂P)) : ℂ) - (1 / 2 : ℂ) * (↑(Qfun s) : ℂ) :=
    fun s => rfl
  have hQcast : ∀ s : EuclideanSpace ℝ (Fin d),
      (∑ j : Fin d, ∑ k : Fin d, (↑(s j) : ℂ) * ↑(s k) * ↑(cov j k)) = (↑(Qfun s) : ℂ) := by
    intro s
    rw [hQfun_apply s]
    push_cast
    ring
  have hQreal_scale : ∀ (a : ℝ) (u : EuclideanSpace ℝ (Fin d)), Qfun (a • u) = a ^ 2 * Qfun u := by
    intro a u
    rw [hQfun_apply, hQfun_apply]
    have hpt : ∀ j : Fin d, ((a • u) j : ℝ) = a * u j := fun j => by simp
    simp only [hpt]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  have hchar' : ∀ s : EuclideanSpace ℝ (Fin d), ‖s‖ < δ →
      charFun (P.map (X 0)) s = Complex.exp (Psi s + ε s) := by
    intro s hs
    rw [hchar s hs, hPsi_apply s]
    congr 1
    rw [hQcast s]
  have hPsi1 : ∀ r : ℕ, Psi (s1 r) =
      Complex.I * (↑(c r / (m r : ℝ) * A) : ℂ) -
        (1 / 2 : ℂ) * (↑((c r / (m r : ℝ)) ^ 2 * Qfun t) : ℂ) := by
    intro r
    rw [hPsi_apply, hs1_apply r, real_inner_smul_left, hQreal_scale]
  have hPsi2 : ∀ r : ℕ, Psi (s2 r) =
      Complex.I * (↑(-(c r / (n r : ℝ)) * A) : ℂ) -
        (1 / 2 : ℂ) * (↑((-(c r / (n r : ℝ))) ^ 2 * Qfun t) : ℂ) := by
    intro r
    rw [hPsi_apply, hs2_apply r, real_inner_smul_left, hQreal_scale]
  have hreal1 : ∀ r : ℕ,
      (m r : ℝ) * (c r / (m r : ℝ) * A) + (n r : ℝ) * (-(c r / (n r : ℝ)) * A) = 0 := by
    intro r
    have hm' : (m r : ℝ) ≠ 0 := hmR_ne r
    have hn' : (n r : ℝ) ≠ 0 := hnR_ne r
    field_simp
    ring
  have hreal2a : ∀ r : ℕ,
      (m r : ℝ) * ((c r / (m r : ℝ)) ^ 2) + (n r : ℝ) * ((-(c r / (n r : ℝ))) ^ 2) = 1 := by
    intro r
    have hm' : (m r : ℝ) ≠ 0 := hmR_ne r
    have hn' : (n r : ℝ) ≠ 0 := hnR_ne r
    have h1 : (m r : ℝ) * ((c r / (m r : ℝ)) ^ 2) = c r ^ 2 / (m r : ℝ) := by
      field_simp
    have h2 : (n r : ℝ) * ((-(c r / (n r : ℝ))) ^ 2) = c r ^ 2 / (n r : ℝ) := by
      field_simp
    rw [h1, h2, hc2_div_m r, hc2_div_n r]
    exact hweight_sum r
  have hreal2 : ∀ r : ℕ,
      (m r : ℝ) * ((c r / (m r : ℝ)) ^ 2 * Qfun t) +
        (n r : ℝ) * ((-(c r / (n r : ℝ))) ^ 2 * Qfun t) = Qfun t := by
    intro r
    calc (m r : ℝ) * ((c r / (m r : ℝ)) ^ 2 * Qfun t) +
          (n r : ℝ) * ((-(c r / (n r : ℝ))) ^ 2 * Qfun t)
        = ((m r : ℝ) * ((c r / (m r : ℝ)) ^ 2) +
            (n r : ℝ) * ((-(c r / (n r : ℝ))) ^ 2)) * Qfun t := by ring
      _ = 1 * Qfun t := by rw [hreal2a r]
      _ = Qfun t := one_mul _
  have hmcast : ∀ r : ℕ, (↑(m r) : ℂ) = ((m r : ℝ) : ℂ) := fun r => by push_cast; ring
  have hncast : ∀ r : ℕ, (↑(n r) : ℂ) = ((n r : ℝ) : ℂ) := fun r => by push_cast; ring
  have hpull : ∀ (k z w : ℝ), (↑k : ℂ) * (Complex.I * (↑z : ℂ) - (1 / 2 : ℂ) * (↑w : ℂ))
      = Complex.I * (↑(k * z) : ℂ) - (1 / 2 : ℂ) * (↑(k * w) : ℂ) := by
    intro k z w
    push_cast
    ring
  have hcomb : ∀ (x1 y1 x2 y2 : ℝ),
      (Complex.I * (↑x1 : ℂ) - (1 / 2 : ℂ) * (↑y1 : ℂ)) +
        (Complex.I * (↑x2 : ℂ) - (1 / 2 : ℂ) * (↑y2 : ℂ))
      = Complex.I * (↑(x1 + x2) : ℂ) - (1 / 2 : ℂ) * (↑(y1 + y2) : ℂ) := by
    intro x1 y1 x2 y2
    push_cast
    ring
  have hPsi_add : ∀ r : ℕ, (↑(m r) : ℂ) * Psi (s1 r) + (↑(n r) : ℂ) * Psi (s2 r)
      = -(1 / 2 : ℂ) * (↑(Qfun t) : ℂ) := by
    intro r
    rw [hmcast r, hncast r, hPsi1 r, hPsi2 r, hpull, hpull]
    rw [hcomb, hreal1 r, hreal2 r]
    simp
  have hεrem1 : Tendsto (fun r : ℕ => (↑(m r) : ℂ) * ε (s1 r)) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro e he
    have heta : 0 < e / (2 * (‖t‖ ^ 2 + 1)) := by positivity
    obtain ⟨rho, hrho_pos, hrho_delta, hrho_bound⟩ := hεbound (e / (2 * (‖t‖ ^ 2 + 1))) heta
    have hev : ∀ᶠ r : ℕ in atTop, ‖s1 r‖ < rho :=
      hnorm_s1_tendsto.eventually (Iio_mem_nhds hrho_pos)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
    refine ⟨N, fun r hr => ?_⟩
    have hsr : ‖s1 r‖ < rho := hN r hr
    have heps : ‖ε (s1 r)‖ ≤ e / (2 * (‖t‖ ^ 2 + 1)) * ‖s1 r‖ ^ 2 := hrho_bound (s1 r) hsr
    have hw : (m r : ℝ) * ‖s1 r‖ ^ 2 ≤ ‖t‖ ^ 2 := hweight1_le r
    have hmnn : (0 : ℝ) ≤ (m r : ℝ) := le_of_lt (hmR_pos r)
    have hstep1 : (m r : ℝ) * ‖ε (s1 r)‖ ≤
        (m r : ℝ) * (e / (2 * (‖t‖ ^ 2 + 1)) * ‖s1 r‖ ^ 2) :=
      mul_le_mul_of_nonneg_left heps hmnn
    have hstep3 : e / (2 * (‖t‖ ^ 2 + 1)) * ((m r : ℝ) * ‖s1 r‖ ^ 2) ≤
        e / (2 * (‖t‖ ^ 2 + 1)) * ‖t‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    have hstep4 : e / (2 * (‖t‖ ^ 2 + 1)) * ‖t‖ ^ 2 < e := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (‖t‖ ^ 2 + 1))]
      nlinarith [sq_nonneg ‖t‖, he]
    have hkey : (m r : ℝ) * ‖ε (s1 r)‖ < e := by
      have h5 : e / (2 * (‖t‖ ^ 2 + 1)) * ((m r : ℝ) * ‖s1 r‖ ^ 2) =
          (m r : ℝ) * (e / (2 * (‖t‖ ^ 2 + 1)) * ‖s1 r‖ ^ 2) := by ring
      linarith
    have hcn : ‖((m r : ℝ) : ℂ)‖ = (m r : ℝ) := by simp
    have hnormeq : ‖(↑(m r) : ℂ) * ε (s1 r)‖ = (m r : ℝ) * ‖ε (s1 r)‖ := by
      rw [norm_mul, hmcast r, hcn]
    have hfin : ‖(↑(m r) : ℂ) * ε (s1 r)‖ < e := by rw [hnormeq]; exact hkey
    simpa [dist_eq_norm] using hfin
  have hεrem2 : Tendsto (fun r : ℕ => (↑(n r) : ℂ) * ε (s2 r)) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro e he
    have heta : 0 < e / (2 * (‖t‖ ^ 2 + 1)) := by positivity
    obtain ⟨rho, hrho_pos, hrho_delta, hrho_bound⟩ := hεbound (e / (2 * (‖t‖ ^ 2 + 1))) heta
    have hev : ∀ᶠ r : ℕ in atTop, ‖s2 r‖ < rho :=
      hnorm_s2_tendsto.eventually (Iio_mem_nhds hrho_pos)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
    refine ⟨N, fun r hr => ?_⟩
    have hsr : ‖s2 r‖ < rho := hN r hr
    have heps : ‖ε (s2 r)‖ ≤ e / (2 * (‖t‖ ^ 2 + 1)) * ‖s2 r‖ ^ 2 := hrho_bound (s2 r) hsr
    have hw : (n r : ℝ) * ‖s2 r‖ ^ 2 ≤ ‖t‖ ^ 2 := hweight2_le r
    have hn : (0 : ℝ) ≤ (n r : ℝ) := le_of_lt (hnR_pos r)
    have hstep1 : (n r : ℝ) * ‖ε (s2 r)‖ ≤
        (n r : ℝ) * (e / (2 * (‖t‖ ^ 2 + 1)) * ‖s2 r‖ ^ 2) :=
      mul_le_mul_of_nonneg_left heps hn
    have hstep3 : e / (2 * (‖t‖ ^ 2 + 1)) * ((n r : ℝ) * ‖s2 r‖ ^ 2) ≤
        e / (2 * (‖t‖ ^ 2 + 1)) * ‖t‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    have hkey : (n r : ℝ) * ‖ε (s2 r)‖ < e := by
      have h5 : e / (2 * (‖t‖ ^ 2 + 1)) * ((n r : ℝ) * ‖s2 r‖ ^ 2) =
          (n r : ℝ) * (e / (2 * (‖t‖ ^ 2 + 1)) * ‖s2 r‖ ^ 2) := by ring
      have h4 : e / (2 * (‖t‖ ^ 2 + 1)) * ‖t‖ ^ 2 < e := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (‖t‖ ^ 2 + 1))]
        nlinarith [sq_nonneg ‖t‖, he]
      linarith
    have hcn : ‖((n r : ℝ) : ℂ)‖ = (n r : ℝ) := by simp
    have hnormeq : ‖(↑(n r) : ℂ) * ε (s2 r)‖ = (n r : ℝ) * ‖ε (s2 r)‖ := by
      rw [norm_mul, hncast r, hcn]
    have hfin : ‖(↑(n r) : ℂ) * ε (s2 r)‖ < e := by rw [hnormeq]; exact hkey
    simpa [dist_eq_norm] using hfin
  have hrem : Tendsto
      (fun r : ℕ => (↑(m r) : ℂ) * ε (s1 r) + (↑(n r) : ℂ) * ε (s2 r)) atTop (𝓝 0) := by
    simpa using hεrem1.add hεrem2
  have hfuneq : (fun r : ℕ => (↑(m r) : ℂ) * (Psi (s1 r) + ε (s1 r)) +
        (↑(n r) : ℂ) * (Psi (s2 r) + ε (s2 r)))
      = fun r : ℕ => ((↑(m r) : ℂ) * Psi (s1 r) + (↑(n r) : ℂ) * Psi (s2 r)) +
          ((↑(m r) : ℂ) * ε (s1 r) + (↑(n r) : ℂ) * ε (s2 r)) := by
    funext r
    ring
  have hexp_limit : Tendsto
      (fun r : ℕ => (↑(m r) : ℂ) * (Psi (s1 r) + ε (s1 r)) +
        (↑(n r) : ℂ) * (Psi (s2 r) + ε (s2 r)))
      atTop (𝓝 (-(1 / 2 : ℂ) * (↑(Qfun t) : ℂ))) := by
    rw [hfuneq]
    have hc : Tendsto
        (fun r : ℕ => (↑(m r) : ℂ) * Psi (s1 r) + (↑(n r) : ℂ) * Psi (s2 r))
        atTop (𝓝 (-(1 / 2 : ℂ) * (↑(Qfun t) : ℂ))) := by
      have hthis : (fun r : ℕ => (↑(m r) : ℂ) * Psi (s1 r) + (↑(n r) : ℂ) * Psi (s2 r))
          = (fun _ : ℕ => -(1 / 2 : ℂ) * (↑(Qfun t) : ℂ)) := funext hPsi_add
      rw [hthis]
      exact tendsto_const_nhds
    simpa using hc.add hrem
  have hexp_tendsto : Tendsto
      (fun r : ℕ => Complex.exp ((↑(m r) : ℂ) * (Psi (s1 r) + ε (s1 r)) +
        (↑(n r) : ℂ) * (Psi (s2 r) + ε (s2 r))))
      atTop (𝓝 (Complex.exp (-(1 / 2 : ℂ) * (↑(Qfun t) : ℂ)))) :=
    (Complex.continuous_exp.tendsto (-(1 / 2 : ℂ) * (↑(Qfun t) : ℂ))).comp hexp_limit
  have hevent : ∀ᶠ r : ℕ in atTop,
      charFun (P.map (fun ω =>
        Real.sqrt (((m r : ℝ) * (n r : ℝ)) / ((m r : ℝ) + (n r : ℝ))) •
          (((m r : ℝ)⁻¹ • ∑ i ∈ Finset.range (m r), X i ω) -
            ((n r : ℝ)⁻¹ • ∑ j ∈ Finset.range (n r), Y j ω)))) t =
      Complex.exp ((↑(m r) : ℂ) * (Psi (s1 r) + ε (s1 r)) +
        (↑(n r) : ℂ) * (Psi (s2 r) + ε (s2 r))) := by
    have h1 : ∀ᶠ r : ℕ in atTop, ‖s1 r‖ < δ :=
      hnorm_s1_tendsto.eventually (Iio_mem_nhds hδpos)
    have h2 : ∀ᶠ r : ℕ in atTop, ‖s2 r‖ < δ :=
      hnorm_s2_tendsto.eventually (Iio_mem_nhds hδpos)
    filter_upwards [h1, h2] with r hr1 hr2
    rw [hfactor r, hchar' (s1 r) hr1, hchar' (s2 r) hr2, ← Complex.exp_nat_mul,
      ← Complex.exp_nat_mul, ← Complex.exp_add]
  refine Tendsto.congr' ?_ hexp_tendsto
  filter_upwards [hevent] with r hr
  exact hr.symm
  /- @proof-region region.target-node.session.b9930c478e1e19db end -/
