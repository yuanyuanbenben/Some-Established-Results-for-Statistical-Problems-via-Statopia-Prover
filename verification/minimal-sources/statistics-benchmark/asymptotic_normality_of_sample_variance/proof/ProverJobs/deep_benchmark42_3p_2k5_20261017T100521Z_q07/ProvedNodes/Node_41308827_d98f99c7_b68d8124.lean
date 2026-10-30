import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q07.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q07.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q07.ProvedNodes.Node_1944206525_019ec9f6_8f2f63a4
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

set_option autoImplicit false in
theorem statopia_math_node_41308827_d98f99c7 : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (m sigma2 : ℝ)
    (hY_meas : ∀ i : ℕ, Measurable (Y i))
    (hY_indep : iIndepFun Y P)
    (hY_ident : ∀ i : ℕ, IdentDistrib (Y i) (Y 0) P P)
    (hY_memLp : MemLp (Y 0) 2 P)
    (hY_mean : ∀ i : ℕ, ∫ ω, Y i ω ∂P = m)
    (hsigma2_pos : 0 < sigma2)
    (hY_var : ∫ ω, (Y 0 ω) ^ 2 ∂P - m ^ 2 = sigma2),
    Statlib.StatFoundation.Convergence.WeakConvergence
      (fun n : ℕ =>
        ⟨Measure.map
          (fun ω => (Real.sqrt (n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, (Y i ω - m)) P,
          Measure.isProbabilityMeasure_map (by measurability)⟩)
      ⟨gaussianReal 0 ⟨sigma2, hsigma2_pos.le⟩, by infer_instance⟩ := by
  /- @proof-region region.target-node.session.4fbad5c10f1386aa begin -/
  intro Ω _ P _ Y m sigma2 hY_meas hY_indep hY_ident hY_memLp hY_mean hsigma2_pos hY_var
  classical
  have hmaps : ∀ n : ℕ,
      AEMeasurable (fun ω => (Real.sqrt (n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, (Y i ω - m)) P := by
    intro n
    measurability
  have hchar : ∀ t : ℝ,
      Tendsto (fun n : ℕ => charFun (Measure.map
        (fun ω => (Real.sqrt (n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, (Y i ω - m)) P) t) atTop
        (nhds (charFun (gaussianReal 0 ⟨sigma2, hsigma2_pos.le⟩) t)) := by
    intro t
    have hσpos : 0 < Real.sqrt sigma2 := Real.sqrt_pos.mpr hsigma2_pos
    have hσne : Real.sqrt sigma2 ≠ 0 := ne_of_gt hσpos
    have hσsq : Real.sqrt sigma2 ^ 2 = sigma2 := Real.sq_sqrt hsigma2_pos.le
    have hlim : Complex.exp (-(↑((Real.sqrt sigma2 * t) ^ 2) / 2))
        = charFun (gaussianReal 0 ⟨sigma2, hsigma2_pos.le⟩) t := by
      have hsq : (Real.sqrt sigma2 * t) ^ 2 = sigma2 * t ^ 2 := by
        rw [mul_pow, hσsq]
      rw [hsq, ProbabilityTheory.charFun_gaussianReal]
      congr 1
      push_cast
      ring
    have hkey : Tendsto (fun n : ℕ => charFun (Measure.map
        (fun ω => (∑ j : Fin (n + 1), (Y (j : ℕ) ω - m) / Real.sqrt sigma2) /
          Real.sqrt ((n : ℝ) + 1)) P) (Real.sqrt sigma2 * t)) atTop
        (nhds (Complex.exp (-(↑((Real.sqrt sigma2 * t) ^ 2) / 2)))) :=
      Statlib.StatFoundation.Convergence.LindebergFeller.charfun_lindeberg_pointwise
        (μ := P) (k := fun n => n + 1) (by intro n; exact Nat.succ_pos n)
        (X := fun n j => fun ω => (Y (j : ℕ) ω - m) / Real.sqrt sigma2)
        (s := fun n => Real.sqrt ((n : ℝ) + 1))
        (by intro n; positivity)
        (by intro n j; measurability)
        (by
          intro n
          have h1 : iIndepFun (fun i : ℕ => fun ω => (Y i ω - m) / Real.sqrt sigma2) P := by
            simpa using hY_indep.comp (fun i (y : ℝ) => (y - m) / Real.sqrt sigma2)
              (fun i => by measurability)
          exact ProbabilityTheory.iIndepFun.precomp (g := fun j : Fin (n + 1) => (j : ℕ))
            (fun a b hab => Fin.ext hab) h1)
        (by
          intro n j
          have hj_memLp : MemLp (Y (j : ℕ)) 2 P := (hY_ident (j : ℕ)).memLp_iff.mpr hY_memLp
          have hj_int : Integrable (Y (j : ℕ)) P := hj_memLp.integrable (by norm_num)
          have h1 : ∫ ω, (Y (j : ℕ) ω - m) ∂P = 0 := by
            rw [MeasureTheory.integral_sub hj_int (integrable_const m)]
            simp [hY_mean (j : ℕ)]
          have hdiv : (fun ω => (Y (j : ℕ) ω - m) / Real.sqrt sigma2)
              = fun ω => (Real.sqrt sigma2)⁻¹ • (Y (j : ℕ) ω - m) := by
            funext ω
            rw [div_eq_inv_mul, smul_eq_mul]
          rw [hdiv, MeasureTheory.integral_smul, h1, smul_zero])
        (by
          intro n j
          have hj_memLp : MemLp (Y (j : ℕ)) 2 P := (hY_ident (j : ℕ)).memLp_iff.mpr hY_memLp
          have hsub : MemLp (fun ω => Y (j : ℕ) ω - m) 2 P := hj_memLp.sub (memLp_const m)
          simpa only [div_eq_inv_mul] using hsub.const_mul (Real.sqrt sigma2)⁻¹)
        (by
          intro n
          have hY0_int : Integrable (Y 0) P := hY_memLp.integrable (by norm_num)
          have hY0sq_int : Integrable (fun ω => (Y 0 ω) ^ 2) P := hY_memLp.integrable_sq
          have hZm : Integrable (fun ω => Y 0 ω - m) P := hY0_int.sub (integrable_const m)
          have hZ0 : ∫ ω, (Y 0 ω - m) ∂P = 0 := by
            rw [MeasureTheory.integral_sub hY0_int (integrable_const m)]
            simp [hY_mean 0]
          have h0 : ∫ ω, (Y 0 ω - m) ^ 2 ∂P = sigma2 := by
            have hcongr : ∫ ω, (Y 0 ω - m) ^ 2 ∂P
                = ∫ ω, ((Y 0 ω) ^ 2 - m ^ 2 - 2*m*(Y 0 ω - m)) ∂P := by
              congr 1
              funext ω
              ring
            rw [hcongr]
            have hA : Integrable (fun ω => (Y 0 ω) ^ 2 - m ^ 2) P :=
              hY0sq_int.sub (integrable_const (m ^ 2))
            have hB : Integrable (fun ω => 2*m*(Y 0 ω - m)) P := hZm.const_mul (2*m)
            rw [MeasureTheory.integral_sub hA hB]
            have hAsplit : ∫ ω, ((Y 0 ω) ^ 2 - m ^ 2) ∂P
                = ∫ ω, (Y 0 ω) ^ 2 ∂P - m ^ 2 := by
              rw [MeasureTheory.integral_sub hY0sq_int (integrable_const (m ^ 2))]
              simp
            have hBzero : ∫ ω, 2*m*(Y 0 ω - m) ∂P = 0 := by
              have hsm : (fun ω => 2*m*(Y 0 ω - m)) = fun ω => (2*m) • (Y 0 ω - m) := by
                funext ω
                rw [smul_eq_mul]
              rw [hsm, MeasureTheory.integral_smul, hZ0, smul_zero]
            rw [hAsplit, hBzero]
            simpa using hY_var
          have hvarj : ∀ j : ℕ, ∫ ω, (Y j ω - m) ^ 2 ∂P = sigma2 := by
            intro j
            have h1 : ∫ ω, (Y j ω - m) ^ 2 ∂P = Var[Y j; P] := by
              rw [ProbabilityTheory.variance_eq_integral (hY_meas j).aemeasurable, hY_mean j]
            have h2 : ∫ ω, (Y 0 ω - m) ^ 2 ∂P = Var[Y 0; P] := by
              rw [ProbabilityTheory.variance_eq_integral (hY_meas 0).aemeasurable, hY_mean 0]
            rw [h1, (hY_ident j).variance_eq, ← h2]
            exact h0
          have hterm : ∀ j : Fin (n + 1),
              ∫ ω, ((Y (j : ℕ) ω - m) / Real.sqrt sigma2) ^ 2 ∂P = 1 := by
            intro j
            have hσ' : Real.sqrt sigma2 ≠ 0 := hσne
            have hsqfun : (fun ω => ((Y (j : ℕ) ω - m) / Real.sqrt sigma2) ^ 2)
                = fun ω => (Real.sqrt sigma2 ^ 2)⁻¹ • ((Y (j : ℕ) ω - m) ^ 2) := by
              funext ω
              rw [smul_eq_mul]
              field_simp
            rw [hsqfun, MeasureTheory.integral_smul, hvarj (j : ℕ), hσsq, smul_eq_mul]
            exact inv_mul_cancel₀ (ne_of_gt hsigma2_pos)
          have hc' : ∑ j : Fin (n + 1),
              ∫ ω, ((Y (j : ℕ) ω - m) / Real.sqrt sigma2) ^ 2 ∂P = ((n + 1 : ℕ) : ℝ) := by
            rw [Finset.sum_congr rfl (fun j _ => hterm j)]
            simp
          show ∑ j : Fin (n + 1),
              ∫ ω, ((Y (j : ℕ) ω - m) / Real.sqrt sigma2) ^ 2 ∂P
              = (Real.sqrt ((n : ℝ) + 1)) ^ 2
          rw [hc']
          push_cast
          rw [Real.sq_sqrt (by positivity : (0:ℝ) ≤ (n : ℝ) + 1)])
        (statopia_math_node_1944206525_019ec9f6 (P := P) (Y := Y) (m := m) (sigma2 := sigma2)
          hY_meas hY_ident hY_memLp hY_mean hsigma2_pos hY_var)
        (Real.sqrt sigma2 * t)
    have hstep : ∀ n : ℕ, charFun (Measure.map
        (fun ω => (∑ j : Fin (n + 1), (Y (j : ℕ) ω - m) / Real.sqrt sigma2) /
          Real.sqrt ((n : ℝ) + 1)) P) (Real.sqrt sigma2 * t)
        = charFun (Measure.map
          (fun ω => (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ *
            ∑ i ∈ Finset.range (n + 1), (Y i ω - m)) P) t := by
      intro n
      have hmcast : ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) := by
        push_cast
        ring
      have hF : (fun ω => Real.sqrt sigma2 *
            ((∑ j : Fin (n + 1), (Y (j : ℕ) ω - m) / Real.sqrt sigma2) /
              Real.sqrt ((n : ℝ) + 1)))
          = fun ω => (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ *
              ∑ i ∈ Finset.range (n + 1), (Y i ω - m) := by
        funext ω
        have hmpos : (0 : ℝ) < Real.sqrt ((n + 1 : ℕ) : ℝ) := by
          apply Real.sqrt_pos.mpr
          positivity
        have hm' : Real.sqrt ((n + 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hmpos
        have hσ' : Real.sqrt sigma2 ≠ 0 := hσne
        rw [hmcast]
        rw [Fin.sum_univ_eq_sum_range (fun i => (Y i ω - m) / Real.sqrt sigma2) (n + 1),
          Finset.sum_div]
        field_simp
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        field_simp
      have hcomp : ((fun x : ℝ => Real.sqrt sigma2 * x) ∘
            (fun ω => (∑ j : Fin (n + 1), (Y (j : ℕ) ω - m) / Real.sqrt sigma2) /
              Real.sqrt ((n : ℝ) + 1)))
          = fun ω => Real.sqrt sigma2 *
            ((∑ j : Fin (n + 1), (Y (j : ℕ) ω - m) / Real.sqrt sigma2) /
              Real.sqrt ((n : ℝ) + 1)) := rfl
      have hmap : Measure.map (fun x : ℝ => Real.sqrt sigma2 * x)
            (Measure.map (fun ω => (∑ j : Fin (n + 1), (Y (j : ℕ) ω - m) / Real.sqrt sigma2) /
              Real.sqrt ((n : ℝ) + 1)) P)
          = Measure.map ((fun x : ℝ => Real.sqrt sigma2 * x) ∘
              (fun ω => (∑ j : Fin (n + 1), (Y (j : ℕ) ω - m) / Real.sqrt sigma2) /
                Real.sqrt ((n : ℝ) + 1))) P :=
        Measure.map_map (by fun_prop) (by measurability)
      rw [← MeasureTheory.charFun_map_mul]
      rw [hmap]
      rw [hcomp, hF]
    have hshift : Tendsto (fun n : ℕ => charFun (Measure.map
        (fun ω => (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ *
          ∑ i ∈ Finset.range (n + 1), (Y i ω - m)) P) t)
        atTop (nhds (charFun (gaussianReal 0 ⟨sigma2, hsigma2_pos.le⟩) t)) := by
      rw [← hlim]
      exact hkey.congr' (Filter.Eventually.of_forall (fun n => hstep n))
    refine (Filter.tendsto_add_atTop_iff_nat (f := fun n : ℕ => charFun (Measure.map
        (fun ω => (Real.sqrt (n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, (Y i ω - m)) P) t) 1).mp ?_
    simpa using hshift
  have hf0 : (fun t : ℝ => charFun (gaussianReal 0 ⟨sigma2, hsigma2_pos.le⟩) t) 0 = 1 := by
    simp [ProbabilityTheory.charFun_gaussianReal]
  have hfc : ContinuousAt (fun t : ℝ => charFun (gaussianReal 0 ⟨sigma2, hsigma2_pos.le⟩) t) 0 := by
    have hfun : (fun t : ℝ => charFun (gaussianReal 0 ⟨sigma2, hsigma2_pos.le⟩) t)
        = fun t : ℝ => Complex.exp (-(↑t ^ 2 * (↑sigma2 : ℂ) / 2)) := by
      funext t
      rw [ProbabilityTheory.charFun_gaussianReal]
      congr 1
      push_cast
      ring
    rw [hfun]
    fun_prop
  obtain ⟨μ₀, hμ₀char, hμ₀tend⟩ :=
    Statlib.StatFoundation.Convergence.levy_continuity
      (μs := fun n : ℕ => ⟨Measure.map
        (fun ω => (Real.sqrt (n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, (Y i ω - m)) P,
          Measure.isProbabilityMeasure_map (hmaps n)⟩)
      (f := fun t : ℝ => charFun (gaussianReal 0 ⟨sigma2, hsigma2_pos.le⟩) t)
      hchar hf0 hfc
  have hμ₀eq : μ₀ = ⟨gaussianReal 0 ⟨sigma2, hsigma2_pos.le⟩, by infer_instance⟩ := by
    apply Statlib.StatFoundation.Convergence.probMeasure_eq_of_charFun_eq
    intro t
    simpa using hμ₀char t
  rw [hμ₀eq] at hμ₀tend
  simpa using hμ₀tend
  /- @proof-region region.target-node.session.4fbad5c10f1386aa end -/
