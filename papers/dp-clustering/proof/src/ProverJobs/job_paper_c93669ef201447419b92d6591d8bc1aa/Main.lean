import ProverJobs.job_paper_c93669ef201447419b92d6591d8bc1aa.Vocabulary
import ProverJobs.job_paper_c93669ef201447419b92d6591d8bc1aa.ProvedNodes
import ProverJobs.job_paper_c93669ef201447419b92d6591d8bc1aa.Base

namespace Statlib.Imported
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators

theorem paper_c93669ef201447419b92d6591d8bc1aa
    (t : ℕ) (ht : 1 ≤ t)
    (c : ℝ) (hc : 0 < c)
    (θstar : Fin t → ℝ)
    (hsep : ∀ j k : Fin t, j ≠ k → 2 * c < |θstar j - θstar k|)
    (g q0 : ℝ → ℝ)
      (hg_meas : Measurable g)
      (hg_nonneg : ∀ x, 0 ≤ g x)
      (hg_integral : ∫ x, g x ∂volume = 1)
      (hg_int : Integrable g volume)
      (hg_pos : ∀ x ∈ Set.Icc (-c) c, 0 < g x)
      (hg_zero : ∀ x, x ∉ Set.Icc (-c) c → g x = 0)
      (hq0_meas : Measurable q0)
      (hq0_nonneg : ∀ θ, 0 ≤ q0 θ)
      (hq0_integral : ∫ θ, q0 θ ∂volume = 1)
      (hq0_int : Integrable q0 volume)
      (hθstar_supp : ∀ j : Fin t, θstar j ∈ interior (Measure.support (Q0 q0)))
      (m M : ℝ) (hm : 0 < m) (hM : 0 < M)
      (hT1 : ∀ x ∈ Set.Icc (-c) c, m ≤ g x ∧ g x ≤ M)
      (hT2diff : DifferentiableOn ℝ g (Set.Ioo (-c) c))
      (Rg : ℝ) (hRg : 0 ≤ Rg) (hT2 : ∀ x ∈ Set.Ioo (-c) c, |deriv g x / g x| ≤ Rg)
      (U : ℝ) (hU : 0 < U)
      (hT3 : ∀ y ∈ Set.Icc (0 : ℝ) (2 * c), q0 y + q0 (-y) ≤ U)
      (L : ℝ) (hL : 0 < L) (δ : Fin t → ℝ) (hδ : ∀ j, 0 < δ j)
      (hT4 : ∀ (j : Fin t) (θ : ℝ), |θ - θstar j| ≤ δ j → L ≤ q0 θ)
      (p : Fin t → ℝ) (hp_pos : ∀ j, 0 < p j) (hp_lt : ∀ j, p j < 1)
      (hp_sum : ∑ j, p j = 1)
      (Rcomp : Fin t → Measure ℝ)
      (hRcomp_prob : ∀ j, IsProbabilityMeasure (Rcomp j))
      (hRcomp_ne : ∀ j k : Fin t, j ≠ k → Rcomp j ≠ Rcomp k)
      (hRcomp_dens : ∀ j : Fin t,
        Rcomp j = volume.withDensity (fun x => ENNReal.ofReal (g (x - θstar j))))
      {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : ℕ → Ω → ℝ) (hX_meas : ∀ i, Measurable (X i))
      (hX_indep : iIndepFun X μ)
      (hX_law : ∀ i, Measure.map (X i) μ = mixLaw p Rcomp)
      (hX_joint : Measure.map (fun ω (i : ℕ) => X i ω) μ = Pinf p Rcomp) :
      ∃ K : ℝ, 0 < K ∧ ∀ j : Fin t, ∃ Nj : ℕ, 3 ≤ Nj ∧ (1 : ℝ) / (Nj : ℝ) ≤ δ j ∧
        ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂μ, Nj ≤ windowCount X θstar c n j ω →
          ENNReal.ofReal (Real.rpow K (1 / (t : ℝ)) * Ystat X θstar c n j ω /
              ((windowCount X θstar c n j ω : ℝ) *
                Real.rpow (Real.log (n : ℝ)) (1 / (2 * (t : ℝ)))))
            ≤ ∫⁻ θ, ENNReal.ofReal (((windowIdx X θstar c n j ω).prod
                  (fun i => g (X i ω - θ) / g (X i ω - θstar j))) * q0 θ) ∂volume
:= by
  /- @proof-region region.root.e75fb4c990cb begin -/
  classical
  have htR : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have htRpos : (0 : ℝ) < (t : ℝ) := by linarith
  have ht_ne : (t : ℝ) ≠ 0 := ne_of_gt htRpos
  have hae_int := statopia_math_node_4114883645_8b1ad159 t ht c hc θstar g M hM hg_nonneg
    (fun x hx => (hT1 x hx).2) hg_zero p hp_pos hp_sum Rcomp hRcomp_dens μ X hX_meas hX_law
  set cst : ℝ := Real.exp (-Rg) * L with hcst
  have hcst_pos : 0 < cst := mul_pos (Real.exp_pos _) hL
  have hcst_nonneg : 0 ≤ cst := hcst_pos.le
  have hK : Real.rpow (cst ^ t) (1 / (t : ℝ)) = cst := by
    show (cst ^ t : ℝ) ^ (1 / (t : ℝ)) = cst
    rw [← Real.rpow_natCast cst t]
    rw [← Real.rpow_mul hcst_nonneg]
    rw [show (t : ℝ) * (1 / (t : ℝ)) = 1 by field_simp]
    rw [Real.rpow_one]
  refine ⟨cst ^ t, pow_pos hcst_pos t, ?_⟩
  intro j
  have hδpos : 0 < δ j := hδ j
  obtain ⟨Nj0, hNj0⟩ := exists_nat_gt (1 / δ j)
  have hNj0pos : (0 : ℝ) < (Nj0 : ℝ) := by
    have h : (0 : ℝ) < 1 / δ j := by positivity
    linarith
  have hprod : (1 : ℝ) < (Nj0 : ℝ) * δ j := by
    have hne : δ j ≠ 0 := ne_of_gt hδpos
    have hk : (1 : ℝ) / δ j * δ j = 1 := by field_simp
    have h2 := mul_lt_mul_of_pos_right hNj0 hδpos
    rwa [hk] at h2
  have hlt : (1 : ℝ) / (Nj0 : ℝ) < δ j := by
    have hne : (Nj0 : ℝ) ≠ 0 := ne_of_gt hNj0pos
    have hk : (1 : ℝ) / (Nj0 : ℝ) * (Nj0 : ℝ) = 1 := by field_simp
    have h2 : (1 : ℝ) / (Nj0 : ℝ) * (Nj0 : ℝ) < δ j * (Nj0 : ℝ) := by
      rw [hk]
      simpa [mul_comm] using hprod
    exact lt_of_mul_lt_mul_right h2 hNj0pos.le
  
  have hNjpos : (0 : ℝ) < ((max 3 Nj0 : ℕ) : ℝ) := by
    have h : 0 < max 3 Nj0 := lt_of_lt_of_le (by norm_num) (le_max_left 3 Nj0)
    exact_mod_cast h
  have hinv : (1 : ℝ) / ((max 3 Nj0 : ℕ) : ℝ) ≤ δ j := by
    refine le_trans (one_div_le_one_div_of_le hNj0pos ?_) hlt.le
    exact_mod_cast (le_max_right 3 Nj0)
  have h3Nj : 3 ≤ max 3 Nj0 := le_max_left 3 Nj0
  refine ⟨max 3 Nj0, h3Nj, hinv, ?_⟩
  intro n hn
  filter_upwards [hae_int] with ω hω
  intro hnω
  have h1nj : 1 ≤ windowCount X θstar c n j ω := by omega
  obtain ⟨hsub, hwin, hcnt, hord, hgap⟩ :=
    statopia_math_node_834363190_4b893991 t ht c hc θstar X n j ω h1nj
  obtain ⟨hUj, hLj⟩ := hord
  obtain ⟨hA0, hs0, hsA, hsnj, hnjs⟩ := hgap
  have hn3 : 3 ≤ n := by omega
  have hNjle : (1 : ℝ) / ((windowCount X θstar c n j ω : ℕ) : ℝ) ≤ δ j := by
    have hle : ((max 3 Nj0 : ℕ) : ℝ) ≤ ((windowCount X θstar c n j ω : ℕ) : ℝ) := by
      exact_mod_cast hnω
    exact le_trans (one_div_le_one_div_of_le hNjpos hle) hinv
  have hlog : (1 : ℝ) ≤ Real.log (n : ℝ) := by
    have hn3R : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
    have hexp : Real.exp (1 : ℝ) ≤ (3 : ℝ) := Real.exp_one_lt_three.le
    have h := Real.log_le_log (Real.exp_pos 1) (le_trans hexp hn3R)
    rwa [Real.log_exp] at h
  have hLn1 : 1 ≤ Real.rpow (Real.log (n : ℝ)) (1 / (2 * (t : ℝ))) := by
    refine Real.one_le_rpow hlog ?_
    exact div_nonneg zero_le_one (by linarith : (0 : ℝ) ≤ 2 * (t : ℝ))
  have hnjpos : (0 : ℝ) < ((windowCount X θstar c n j ω : ℕ) : ℝ) := by
    have h : 0 < windowCount X θstar c n j ω := by omega
    exact_mod_cast h
  have hintoo : ∀ i ∈ windowIdx X θstar c n j ω, X i ω - θstar j ∈ Set.Ioo (-c) c :=
    fun i hi => hω.2.1 i j (hwin i hi).2.2
  have hP : ∀ θ ∈ Set.Ioo (θstar j - min (c + θstar j - upperOrderStat X θstar c n j ω)
        (1 / ((windowCount X θstar c n j ω : ℕ) : ℝ))) (θstar j) ∪ {θstar j},
      Real.exp (-Rg) ≤ ∏ i ∈ windowIdx X θstar c n j ω,
        g (X i ω - θ) / g (X i ω - θstar j) :=
    (statopia_math_node_537990944_6d0e223c t ht c hc θstar g Rg hRg X n j ω h1nj hUj hintoo
      m M hm hM hT1 hT2diff hT2).2
  have hlin := statopia_math_node_2396382263_35e06d48 t ht c hc θstar g q0 Rg hRg L hL δ X n hn j ω
    h1nj hNjle hUj (fun i hi => (hwin i hi).2.2) hg_nonneg hg_pos hq0_nonneg
    (fun θ hθ => hT4 j θ hθ) hP
  set N : ℝ := ((windowCount X θstar c n j ω : ℕ) : ℝ) with hN
  set Ln : ℝ := Real.rpow (Real.log (n : ℝ)) (1 / (2 * (t : ℝ))) with hLn
  set A : ℝ := c + θstar j - upperOrderStat X θstar c n j ω with hA
  set s : ℝ := min A (1 / N) with hs
  have hNpos : 0 < N := hnjpos
  have hA0' : 0 ≤ A := hA0
  have hLn1' : 1 ≤ Ln := hLn1
  have hmin : min 1 (N * Ln * A) / (N * Ln) ≤ min A (1 / N) :=
    statopia_math_node_226752033_d30a6425 N Ln A hNpos hLn1' hA0'
  have hY : Ystat X θstar c n j ω = min 1 (N * Ln * A) := by
    simp only [Ystat, hN, hLn, hA]
  have hreal : Real.rpow (cst ^ t) (1 / (t : ℝ)) * Ystat X θstar c n j ω / (N * Ln) ≤
      cst * s := by
    rw [hK]
    have hstep : cst * (min 1 (N * Ln * A) / (N * Ln)) ≤ cst * min A (1 / N) :=
      mul_le_mul_of_nonneg_left hmin hcst_nonneg
    calc cst * Ystat X θstar c n j ω / (N * Ln)
        = cst * (min 1 (N * Ln * A) / (N * Ln)) := by rw [hY]; ring
      _ ≤ cst * min A (1 / N) := hstep
      _ = cst * s := by rw [hs]
  exact le_trans (ENNReal.ofReal_le_ofReal hreal) hlin
  /- @proof-region region.root.e75fb4c990cb end -/

end Statlib.Imported
