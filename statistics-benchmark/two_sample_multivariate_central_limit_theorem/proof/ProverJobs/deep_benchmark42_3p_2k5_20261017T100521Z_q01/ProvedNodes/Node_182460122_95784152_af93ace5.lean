import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q01.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q01.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q01.ProvedNodes.Node_1864527449_b0cc0f87_22231466
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q01.ProvedNodes.Node_3980798612_87c1b9de_8c55c5f3
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

set_option autoImplicit false in
theorem statopia_math_node_182460122_95784152 : ∀ (d : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure ν]
    (hsecond : Integrable (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖ ^ 2) ν),
    ∀ (eta : ℝ), 0 < eta →
      ∀ᶠ s : EuclideanSpace ℝ (Fin d) in 𝓝 (0 : EuclideanSpace ℝ (Fin d)),
        ‖∫ x : EuclideanSpace ℝ (Fin d),
            (Complex.exp
                (((inner ℝ (x - (∫ z : EuclideanSpace ℝ (Fin d), z ∂ν)) s : ℝ) : ℂ) *
                    Complex.I +
                  (1 / 2 : ℂ) *
                    (((∑ j : Fin d, ∑ k : Fin d, s j * s k *
                          (∫ y : EuclideanSpace ℝ (Fin d),
                            (y j - (∫ z : EuclideanSpace ℝ (Fin d), z ∂ν) j) *
                              (y k - (∫ z : EuclideanSpace ℝ (Fin d), z ∂ν) k) ∂ν)) :
                        ℝ) : ℂ))
              - 1) ∂ν‖
          ≤ eta * ‖s‖ ^ 2 := by
  /- @proof-region region.target-node.session.9ab3de3792b561de begin -/
  intro d ν hprob hsecond eta heta
  haveI := hprob
  set m : EuclideanSpace ℝ (Fin d) := ∫ z, z ∂ν with hm
  have hId_int : Integrable (fun x : EuclideanSpace ℝ (Fin d) => x) ν := by
    have hb : Integrable (fun x : EuclideanSpace ℝ (Fin d) => 1 + ‖x‖ ^ 2) ν :=
      (integrable_const 1).add hsecond
    refine hb.mono' ?_ ?_
    · exact (by fun_prop : Continuous fun x : EuclideanSpace ℝ (Fin d) => x).aestronglyMeasurable
    · filter_upwards with x
      have hx : (0:ℝ) ≤ ‖x‖ := norm_nonneg x
      have h1 : ‖x‖ ≤ 1 + ‖x‖ ^ 2 := by nlinarith
      simpa using h1
  have hsub_int : Integrable (fun x : EuclideanSpace ℝ (Fin d) => x - m) ν :=
    hId_int.sub (integrable_const m)
  have hcent_int : ∫ x : EuclideanSpace ℝ (Fin d), (x - m) ∂ν = 0 := by
    rw [integral_sub hId_int (integrable_const m)]
    simp [hm]
  have hsq_int : Integrable (fun x : EuclideanSpace ℝ (Fin d) => ‖x - m‖ ^ 2) ν := by
    have hb : Integrable (fun x : EuclideanSpace ℝ (Fin d) => 4 * ‖x‖ ^ 2 + 4 * ‖m‖ ^ 2) ν :=
      (hsecond.const_mul 4).add (integrable_const _)
    refine hb.mono' ?_ ?_
    · exact (by fun_prop : Continuous fun x : EuclideanSpace ℝ (Fin d) => ‖x - m‖ ^ 2).aestronglyMeasurable
    · filter_upwards with x
      have h2 : (0:ℝ) ≤ ‖x - m‖ := norm_nonneg _
      have h4 : ‖x - m‖ ^ 2 ≤ (‖x‖ + ‖m‖) ^ 2 := by
        have h1 : ‖x - m‖ ≤ ‖x‖ + ‖m‖ := norm_sub_le x m
        nlinarith
      have h5 : ‖‖x - m‖ ^ 2‖ = ‖x - m‖ ^ 2 := Real.norm_of_nonneg (by positivity)
      rw [h5]
      nlinarith [sq_nonneg (‖x‖ - ‖m‖), norm_nonneg x, norm_nonneg m]
  have hK_nonneg : 0 ≤ ∫ x : EuclideanSpace ℝ (Fin d), ‖x - m‖ ^ 2 ∂ν :=
    integral_nonneg (fun x => by positivity)
  set M : ℝ := (∫ x : EuclideanSpace ℝ (Fin d), ‖x - m‖ ^ 2 ∂ν) + 1 with hMdef
  have hM1 : (1:ℝ) ≤ M := by rw [hMdef]; linarith
  have hMpos : (0:ℝ) < M := lt_of_lt_of_le one_pos hM1
  have hKle : (∫ x : EuclideanSpace ℝ (Fin d), ‖x - m‖ ^ 2 ∂ν) ≤ M := by rw [hMdef]; linarith
  have hquad_form : ∀ s : EuclideanSpace ℝ (Fin d),
      ∫ x : EuclideanSpace ℝ (Fin d), (inner ℝ (x - m) s) ^ 2 ∂ν
        = ∑ j : Fin d, ∑ k : Fin d, s j * s k * (∫ y : EuclideanSpace ℝ (Fin d), (y j - m j) * (y k - m k) ∂ν) := by
    intro s
    have hcont : ∀ j : Fin d, Continuous fun x : EuclideanSpace ℝ (Fin d) => x.ofLp j - m.ofLp j := by
      intro j
      have h1 : Continuous fun x : EuclideanSpace ℝ (Fin d) => x.ofLp j := by fun_prop
      exact h1.sub continuous_const
    have hpoint : ∀ x : EuclideanSpace ℝ (Fin d), (inner ℝ (x - m) s) ^ 2
        = ∑ j : Fin d, ∑ k : Fin d,
            ((x.ofLp j - m.ofLp j) * s.ofLp j) * ((x.ofLp k - m.ofLp k) * s.ofLp k) := by
      intro x
      have h1 : inner ℝ (x - m) s = ∑ j : Fin d, (x.ofLp j - m.ofLp j) * s.ofLp j := by
        rw [PiLp.inner_apply]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        simp [PiLp.sub_apply, mul_comm]
      rw [h1, sq, Finset.sum_mul_sum]
    have hprod_int : ∀ j k : Fin d, Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
        (x.ofLp j - m.ofLp j) * (x.ofLp k - m.ofLp k)) ν := by
      intro j k
      refine hsq_int.mono' ?_ ?_
      · exact ((hcont j).mul (hcont k)).aestronglyMeasurable
      · filter_upwards with x
        have h2 : |x.ofLp j - m.ofLp j| ≤ ‖x - m‖ := by
          have hj : ‖(x - m).ofLp j‖ ≤ ‖x - m‖ := PiLp.norm_apply_le (x - m) j
          rw [PiLp.sub_apply] at hj
          simpa using hj
        have h4 : (0:ℝ) ≤ ‖x - m‖ := norm_nonneg _
        have h3 : |x.ofLp k - m.ofLp k| ≤ ‖x - m‖ := by
          have hk : ‖(x - m).ofLp k‖ ≤ ‖x - m‖ := PiLp.norm_apply_le (x - m) k
          rw [PiLp.sub_apply] at hk
          simpa using hk
        rw [Real.norm_eq_abs, abs_mul]
        calc |x.ofLp j - m.ofLp j| * |x.ofLp k - m.ofLp k| ≤ ‖x - m‖ * ‖x - m‖ :=
              mul_le_mul h2 h3 (abs_nonneg _) h4
          _ = ‖x - m‖ ^ 2 := by ring
    have hsum_int : ∀ j : Fin d, Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
        ∑ k : Fin d, ((x.ofLp j - m.ofLp j) * s.ofLp j) * ((x.ofLp k - m.ofLp k) * s.ofLp k)) ν := by
      intro j
      refine integrable_finset_sum _ (fun k _ => ?_)
      have h := (hprod_int j k).mul_const (s.ofLp j * s.ofLp k)
      refine h.congr ?_
      filter_upwards with x
      ring
    calc ∫ x : EuclideanSpace ℝ (Fin d), (inner ℝ (x - m) s) ^ 2 ∂ν
        = ∫ x : EuclideanSpace ℝ (Fin d), ∑ j : Fin d, ∑ k : Fin d,
            ((x.ofLp j - m.ofLp j) * s.ofLp j) * ((x.ofLp k - m.ofLp k) * s.ofLp k) ∂ν := by
          apply integral_congr_ae
          filter_upwards with x
          exact hpoint x
      _ = ∑ j : Fin d, ∫ x : EuclideanSpace ℝ (Fin d), ∑ k : Fin d,
            ((x.ofLp j - m.ofLp j) * s.ofLp j) * ((x.ofLp k - m.ofLp k) * s.ofLp k) ∂ν := by
          rw [MeasureTheory.integral_finset_sum]
          exact fun j _ => hsum_int j
      _ = ∑ j : Fin d, ∑ k : Fin d, ∫ x : EuclideanSpace ℝ (Fin d),
            ((x.ofLp j - m.ofLp j) * s.ofLp j) * ((x.ofLp k - m.ofLp k) * s.ofLp k) ∂ν := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [MeasureTheory.integral_finset_sum]
          intro k _
          have h := (hprod_int j k).mul_const (s.ofLp j * s.ofLp k)
          refine h.congr ?_
          filter_upwards with x
          ring
      _ = ∑ j : Fin d, ∑ k : Fin d, s.ofLp j * s.ofLp k *
            (∫ y : EuclideanSpace ℝ (Fin d), (y.ofLp j - m.ofLp j) * (y.ofLp k - m.ofLp k) ∂ν) := by
          refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
          have hpt : ∀ x : EuclideanSpace ℝ (Fin d),
              ((x.ofLp j - m.ofLp j) * s.ofLp j) * ((x.ofLp k - m.ofLp k) * s.ofLp k)
                = ((x.ofLp j - m.ofLp j) * (x.ofLp k - m.ofLp k)) * (s.ofLp j * s.ofLp k) :=
            fun x => by ring
          rw [show (∫ x : EuclideanSpace ℝ (Fin d),
                ((x.ofLp j - m.ofLp j) * s.ofLp j) * ((x.ofLp k - m.ofLp k) * s.ofLp k) ∂ν)
              = ∫ x : EuclideanSpace ℝ (Fin d),
                ((x.ofLp j - m.ofLp j) * (x.ofLp k - m.ofLp k)) * (s.ofLp j * s.ofLp k) ∂ν from by
                apply integral_congr_ae
                filter_upwards with x
                exact hpt x]
          rw [MeasureTheory.integral_mul_const]
          ring
  have htheta_int : ∀ s : EuclideanSpace ℝ (Fin d),
      ∫ x : EuclideanSpace ℝ (Fin d), inner ℝ (x - m) s ∂ν = 0 := by
    intro s
    have h1 : ∫ x : EuclideanSpace ℝ (Fin d), inner ℝ (x - m) s ∂ν
        = inner ℝ (∫ x : EuclideanSpace ℝ (Fin d), (x - m) ∂ν) s := by
      have h := ContinuousLinearMap.integral_comp_comm (innerSL ℝ s) hsub_int
      have h2 : ∫ x : EuclideanSpace ℝ (Fin d), inner ℝ s (x - m) ∂ν
          = inner ℝ s (∫ x : EuclideanSpace ℝ (Fin d), (x - m) ∂ν) := by
        simpa using h
      have h3 : ∫ x : EuclideanSpace ℝ (Fin d), inner ℝ (x - m) s ∂ν
          = ∫ x : EuclideanSpace ℝ (Fin d), inner ℝ s (x - m) ∂ν := by
        apply integral_congr_ae
        filter_upwards with x
        exact real_inner_comm s (x - m)
      rw [h3, h2]
      exact real_inner_comm (∫ x : EuclideanSpace ℝ (Fin d), (x - m) ∂ν) s
    rw [h1, hcent_int, inner_zero_left]
  have hmain : ∀ eta : ℝ, 0 < eta → ∀ᶠ s : EuclideanSpace ℝ (Fin d) in 𝓝 0,
      ‖∫ x : EuclideanSpace ℝ (Fin d), (Complex.exp (((inner ℝ (x - m) s : ℝ) : ℂ) * Complex.I + (1 / 2 : ℂ) * ((∑ j : Fin d, ∑ k : Fin d, s j * s k * (∫ y : EuclideanSpace ℝ (Fin d), (y j - m j) * (y k - m k) ∂ν)) : ℝ)) - 1) ∂ν‖ ≤ eta * ‖s‖ ^ 2 := by
    intro eta heta
    let th : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ :=
      fun s x => inner ℝ (x - m) s
    let c0 : EuclideanSpace ℝ (Fin d) → ℝ :=
      fun s => ∑ j : Fin d, ∑ k : Fin d, s j * s k * (∫ y : EuclideanSpace ℝ (Fin d), (y j - m j) * (y k - m k) ∂ν)
    let Qf : EuclideanSpace ℝ (Fin d) → ℂ := fun s => (1 / 2 : ℂ) * ((c0 s : ℝ) : ℂ)
    let uf : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℂ :=
      fun s x => ((th s x : ℝ) : ℂ) * Complex.I + Qf s
    let Rf : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℂ :=
      fun s x => Complex.exp (uf s x) - 1 - uf s x - (uf s x) ^ 2 / 2
    have hQ_le : ∀ s : EuclideanSpace ℝ (Fin d), ‖Qf s‖ ≤ M * ‖s‖ ^ 2 := by
      intro s
      have hc0 : c0 s = ∫ x : EuclideanSpace ℝ (Fin d), (th s x) ^ 2 ∂ν := by
        show (∑ j : Fin d, ∑ k : Fin d, s j * s k * (∫ y : EuclideanSpace ℝ (Fin d), (y j - m j) * (y k - m k) ∂ν))
            = ∫ x : EuclideanSpace ℝ (Fin d), (inner ℝ (x - m) s) ^ 2 ∂ν
        exact (hquad_form s).symm
      have hpt : ∀ x : EuclideanSpace ℝ (Fin d), (th s x) ^ 2 ≤ ‖x - m‖ ^ 2 * ‖s‖ ^ 2 := by
        intro x
        have h1 : |inner ℝ (x - m) s| ≤ ‖x - m‖ * ‖s‖ := abs_real_inner_le_norm (x - m) s
        have h3 : (0:ℝ) ≤ ‖x - m‖ * ‖s‖ := by positivity
        have h4 : |inner ℝ (x - m) s| * |inner ℝ (x - m) s| ≤ (‖x - m‖ * ‖s‖) * (‖x - m‖ * ‖s‖) :=
          mul_le_mul h1 h1 (abs_nonneg _) h3
        nlinarith [h4, sq_abs (inner ℝ (x - m) s)]
      have hbig : Integrable (fun x : EuclideanSpace ℝ (Fin d) => ‖x - m‖ ^ 2 * ‖s‖ ^ 2) ν :=
        hsq_int.mul_const _
      have hth2_int : Integrable (fun x : EuclideanSpace ℝ (Fin d) => (th s x) ^ 2) ν := by
        refine hbig.mono' ?_ ?_
        · exact (by fun_prop : Continuous fun x : EuclideanSpace ℝ (Fin d) => (inner ℝ (x - m) s) ^ 2).aestronglyMeasurable
        · filter_upwards with x
          have h9 := hpt x
          have h10 : (0:ℝ) ≤ (th s x) ^ 2 := by positivity
          rw [Real.norm_eq_abs, abs_of_nonneg h10]
          exact h9
      have hnn : (0:ℝ) ≤ c0 s := by
        rw [hc0]
        exact integral_nonneg (fun x => by positivity)
      have hup : c0 s ≤ M * ‖s‖ ^ 2 := by
        rw [hc0]
        have hpt2 : ∀ x : EuclideanSpace ℝ (Fin d),
            (0:ℝ) ≤ ‖x - m‖ ^ 2 * ‖s‖ ^ 2 - (th s x) ^ 2 := by
          intro x
          have h9 := hpt x
          linarith
        have hdiff : (0:ℝ) ≤
            ∫ x : EuclideanSpace ℝ (Fin d), (‖x - m‖ ^ 2 * ‖s‖ ^ 2 - (th s x) ^ 2) ∂ν :=
          integral_nonneg hpt2
        have hsub_eq : (∫ x : EuclideanSpace ℝ (Fin d), (‖x - m‖ ^ 2 * ‖s‖ ^ 2 - (th s x) ^ 2) ∂ν)
            = (∫ x : EuclideanSpace ℝ (Fin d), ‖x - m‖ ^ 2 * ‖s‖ ^ 2 ∂ν)
              - ∫ x : EuclideanSpace ℝ (Fin d), (th s x) ^ 2 ∂ν :=
          integral_sub hbig hth2_int
        have hval : (∫ x : EuclideanSpace ℝ (Fin d), ‖x - m‖ ^ 2 * ‖s‖ ^ 2 ∂ν)
            = (∫ x : EuclideanSpace ℝ (Fin d), ‖x - m‖ ^ 2 ∂ν) * ‖s‖ ^ 2 := by
          rw [MeasureTheory.integral_mul_const]
        have h4 : (0:ℝ) ≤ ‖s‖ ^ 2 := by positivity
        have hprod : (∫ x : EuclideanSpace ℝ (Fin d), ‖x - m‖ ^ 2 ∂ν) * ‖s‖ ^ 2 ≤ M * ‖s‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hKle h4
        rw [hsub_eq, hval] at hdiff
        linarith
      have hofReal_norm : ∀ r : ℝ, ‖((r : ℝ) : ℂ)‖ = |r| := by
        intro r
        have hI : ‖Complex.I‖ = 1 := by
          have h := Statlib.StatFoundation.Convergence.BerryEsseen.norm_ofReal_mul_I 1
          simpa using h
        have h := Statlib.StatFoundation.Convergence.BerryEsseen.norm_ofReal_mul_I r
        calc ‖((r : ℝ) : ℂ)‖ = ‖((r : ℝ) : ℂ)‖ * 1 := by ring
          _ = ‖((r : ℝ) : ℂ)‖ * ‖Complex.I‖ := by rw [hI]
          _ = ‖((r : ℝ) : ℂ) * Complex.I‖ := by rw [norm_mul]
          _ = |r| := h
      have hQval : Qf s = ((c0 s / 2 : ℝ) : ℂ) := by
        show (1 / 2 : ℂ) * ((c0 s : ℝ) : ℂ) = ((c0 s / 2 : ℝ) : ℂ)
        push_cast
        ring
      have hMnn : (0:ℝ) ≤ M := le_trans zero_le_one hM1
      have hsqnn : (0:ℝ) ≤ ‖s‖ ^ 2 := by positivity
      have habs : |c0 s| ≤ M * ‖s‖ ^ 2 := by
        rw [abs_of_nonneg hnn]
        exact hup
      have hM2 : (0:ℝ) ≤ M * ‖s‖ ^ 2 := mul_nonneg hMnn hsqnn
      rw [hQval, hofReal_norm (c0 s / 2), abs_div,
        abs_of_pos (by norm_num : (0:ℝ) < 2)]
      linarith [habs, hM2]
    have hdecomp : ∀ s : EuclideanSpace ℝ (Fin d),
        ∫ x : EuclideanSpace ℝ (Fin d), (Complex.exp (uf s x) - 1) ∂ν
          = (∫ x : EuclideanSpace ℝ (Fin d), Rf s x ∂ν) + Qf s ^ 2 / 2 := by
      intro s
      have hofReal_norm : ∀ r : ℝ, ‖((r : ℝ) : ℂ)‖ = |r| := by
        intro r
        have hI : ‖Complex.I‖ = 1 := by
          have h := Statlib.StatFoundation.Convergence.BerryEsseen.norm_ofReal_mul_I 1
          simpa using h
        have h := Statlib.StatFoundation.Convergence.BerryEsseen.norm_ofReal_mul_I r
        calc ‖((r : ℝ) : ℂ)‖ = ‖((r : ℝ) : ℂ)‖ * 1 := by ring
          _ = ‖((r : ℝ) : ℂ)‖ * ‖Complex.I‖ := by rw [hI]
          _ = ‖((r : ℝ) : ℂ) * Complex.I‖ := by rw [norm_mul]
          _ = |r| := h
      have hc0eq : c0 s = ∫ x : EuclideanSpace ℝ (Fin d), (th s x) ^ 2 ∂ν := by
        show (∑ j : Fin d, ∑ k : Fin d, s j * s k * (∫ y : EuclideanSpace ℝ (Fin d), (y j - m j) * (y k - m k) ∂ν))
            = ∫ x : EuclideanSpace ℝ (Fin d), (inner ℝ (x - m) s) ^ 2 ∂ν
        exact (hquad_form s).symm
      have hpt : ∀ x : EuclideanSpace ℝ (Fin d), (th s x) ^ 2 ≤ ‖x - m‖ ^ 2 * ‖s‖ ^ 2 := by
        intro x
        have h1 : |inner ℝ (x - m) s| ≤ ‖x - m‖ * ‖s‖ := abs_real_inner_le_norm (x - m) s
        have h3 : (0:ℝ) ≤ ‖x - m‖ * ‖s‖ := by positivity
        have h4 : |inner ℝ (x - m) s| * |inner ℝ (x - m) s| ≤ (‖x - m‖ * ‖s‖) * (‖x - m‖ * ‖s‖) :=
          mul_le_mul h1 h1 (abs_nonneg _) h3
        nlinarith [h4, sq_abs (inner ℝ (x - m) s)]
      have hbig : Integrable (fun x : EuclideanSpace ℝ (Fin d) => ‖x - m‖ ^ 2 * ‖s‖ ^ 2) ν :=
        hsq_int.mul_const _
      have hth2_int : Integrable (fun x : EuclideanSpace ℝ (Fin d) => (th s x) ^ 2) ν := by
        refine hbig.mono' ?_ ?_
        · exact (by fun_prop : Continuous fun x : EuclideanSpace ℝ (Fin d) => (inner ℝ (x - m) s) ^ 2).aestronglyMeasurable
        · filter_upwards with x
          have h9 := hpt x
          have h10 : (0:ℝ) ≤ (th s x) ^ 2 := by positivity
          rw [Real.norm_eq_abs, abs_of_nonneg h10]
          exact h9
      have hb0 : Integrable (fun x : EuclideanSpace ℝ (Fin d) => (‖x - m‖ ^ 2 + 1) * (1 + ‖s‖ ^ 2)) ν :=
        (hsq_int.add (integrable_const 1)).mul_const (1 + ‖s‖ ^ 2)
      have htb : ∀ x : EuclideanSpace ℝ (Fin d), |th s x| ≤ (‖x - m‖ ^ 2 + 1) * (1 + ‖s‖ ^ 2) := by
        intro x
        have h1 : |inner ℝ (x - m) s| ≤ ‖x - m‖ * ‖s‖ := abs_real_inner_le_norm (x - m) s
        have h2 : ‖x - m‖ ≤ ‖x - m‖ ^ 2 + 1 := by nlinarith [norm_nonneg (x - m)]
        have h3 : ‖s‖ ≤ 1 + ‖s‖ ^ 2 := by nlinarith [norm_nonneg s]
        have h4 : (0:ℝ) ≤ ‖x - m‖ := norm_nonneg _
        have h5 : (0:ℝ) ≤ ‖s‖ := norm_nonneg _
        have h6 : (0:ℝ) ≤ ‖x - m‖ ^ 2 + 1 := by positivity
        have h7 : (0:ℝ) ≤ 1 + ‖s‖ ^ 2 := by positivity
        nlinarith [mul_nonneg h4 h5, mul_nonneg h6 h7]
      have hthI_int : Integrable (fun x : EuclideanSpace ℝ (Fin d) => ((th s x : ℝ) : ℂ) * Complex.I) ν := by
        refine hb0.mono' ?_ ?_
        · exact (by fun_prop : Continuous fun x : EuclideanSpace ℝ (Fin d) => ((inner ℝ (x - m) s : ℝ) : ℂ) * Complex.I).aestronglyMeasurable
        · filter_upwards with x
          rw [Statlib.StatFoundation.Convergence.BerryEsseen.norm_ofReal_mul_I (th s x)]
          exact htb x
      have hth2c_int : Integrable (fun x : EuclideanSpace ℝ (Fin d) => (((th s x) ^ 2 : ℝ) : ℂ)) ν := by
        refine hth2_int.mono' ?_ ?_
        · exact (by fun_prop : Continuous fun x : EuclideanSpace ℝ (Fin d) => (((inner ℝ (x - m) s) ^ 2 : ℝ) : ℂ)).aestronglyMeasurable
        · filter_upwards with x
          have h10 : (0:ℝ) ≤ (th s x) ^ 2 := by positivity
          rw [hofReal_norm, abs_of_nonneg h10]
      have hI0 : ∫ x : EuclideanSpace ℝ (Fin d), ((th s x : ℝ) : ℂ) * Complex.I ∂ν = 0 := by
        have h1 : ∫ x : EuclideanSpace ℝ (Fin d), ((th s x : ℝ) : ℂ) * Complex.I ∂ν
            = (∫ x : EuclideanSpace ℝ (Fin d), ((th s x : ℝ) : ℂ) ∂ν) * Complex.I := by
          rw [MeasureTheory.integral_mul_const]
        rw [h1, integral_complex_ofReal, htheta_int s]
        simp
      have hu_int : Integrable (fun x : EuclideanSpace ℝ (Fin d) => uf s x) ν :=
        hthI_int.add (integrable_const (Qf s))
      have hU : ∫ x : EuclideanSpace ℝ (Fin d), uf s x ∂ν = Qf s := by
        have h1 : ∫ x : EuclideanSpace ℝ (Fin d), uf s x ∂ν
            = (∫ x : EuclideanSpace ℝ (Fin d), ((th s x : ℝ) : ℂ) * Complex.I ∂ν)
              + ∫ x : EuclideanSpace ℝ (Fin d), Qf s ∂ν :=
          integral_add hthI_int (integrable_const (Qf s))
        rw [h1, hI0]
        simp
      have hpt2 : ∀ x : EuclideanSpace ℝ (Fin d), (uf s x) ^ 2
          = -((((th s x) ^ 2 : ℝ)) : ℂ) + (((th s x : ℝ) : ℂ) * Complex.I) * (2 * Qf s) + Qf s ^ 2 := by
        intro x
        have hcast : (((th s x : ℝ) : ℂ)) ^ 2 = (((th s x) ^ 2 : ℝ) : ℂ) := by
          push_cast
          ring
        show ((((th s x : ℝ) : ℂ) * Complex.I + Qf s) ^ 2) = _
        calc ((((th s x : ℝ) : ℂ) * Complex.I + Qf s) ^ 2)
            = (((th s x : ℝ) : ℂ)) ^ 2 * (Complex.I * Complex.I)
              + (((th s x : ℝ) : ℂ) * Complex.I) * (2 * Qf s) + Qf s ^ 2 := by
              ring
          _ = -((((th s x) ^ 2 : ℝ)) : ℂ) + (((th s x : ℝ) : ℂ) * Complex.I) * (2 * Qf s) + Qf s ^ 2 := by
              rw [Complex.I_mul_I, hcast]
              ring
      have hI1 : Integrable (fun x : EuclideanSpace ℝ (Fin d) => -((((th s x) ^ 2 : ℝ)) : ℂ)) ν :=
        hth2c_int.neg
      have hI2 : Integrable (fun x : EuclideanSpace ℝ (Fin d) => (((th s x : ℝ) : ℂ) * Complex.I) * (2 * Qf s)) ν :=
        hthI_int.mul_const (2 * Qf s)
      have hI3 : Integrable (fun x : EuclideanSpace ℝ (Fin d) => Qf s ^ 2) ν := integrable_const _
      have hu2_int : Integrable (fun x : EuclideanSpace ℝ (Fin d) => (uf s x) ^ 2) ν := by
        refine ((hI1.add hI2).add hI3).congr ?_
        filter_upwards with x
        exact (hpt2 x).symm
      have hU2 : ∫ x : EuclideanSpace ℝ (Fin d), (uf s x) ^ 2 ∂ν = -((c0 s : ℝ) : ℂ) + Qf s ^ 2 := by
        have h1 : ∫ x : EuclideanSpace ℝ (Fin d), (uf s x) ^ 2 ∂ν
            = ∫ x : EuclideanSpace ℝ (Fin d),
                (-((((th s x) ^ 2 : ℝ)) : ℂ) + (((th s x : ℝ) : ℂ) * Complex.I) * (2 * Qf s) + Qf s ^ 2) ∂ν := by
          apply integral_congr_ae
          filter_upwards with x
          exact hpt2 x
        have hA : ∫ x : EuclideanSpace ℝ (Fin d), -((((th s x) ^ 2 : ℝ)) : ℂ) ∂ν = -((c0 s : ℝ) : ℂ) := by
          rw [MeasureTheory.integral_neg, integral_complex_ofReal, ← hc0eq]
        have hB : ∫ x : EuclideanSpace ℝ (Fin d), (((th s x : ℝ) : ℂ) * Complex.I) * (2 * Qf s) ∂ν = 0 := by
          rw [MeasureTheory.integral_mul_const, hI0]
          ring
        have hC : ∫ x : EuclideanSpace ℝ (Fin d), Qf s ^ 2 ∂ν = Qf s ^ 2 := by
          simp
        have hsp3 : ∫ x : EuclideanSpace ℝ (Fin d),
              (-((((th s x) ^ 2 : ℝ)) : ℂ) + (((th s x : ℝ) : ℂ) * Complex.I) * (2 * Qf s)) ∂ν
            = (∫ x : EuclideanSpace ℝ (Fin d), -((((th s x) ^ 2 : ℝ)) : ℂ) ∂ν)
              + ∫ x : EuclideanSpace ℝ (Fin d), (((th s x : ℝ) : ℂ) * Complex.I) * (2 * Qf s) ∂ν :=
          integral_add hI1 hI2
        have hsp2 : ∫ x : EuclideanSpace ℝ (Fin d),
              (-((((th s x) ^ 2 : ℝ)) : ℂ) + (((th s x : ℝ) : ℂ) * Complex.I) * (2 * Qf s) + Qf s ^ 2) ∂ν
            = (∫ x : EuclideanSpace ℝ (Fin d),
                (-((((th s x) ^ 2 : ℝ)) : ℂ) + (((th s x : ℝ) : ℂ) * Complex.I) * (2 * Qf s)) ∂ν)
              + ∫ x : EuclideanSpace ℝ (Fin d), Qf s ^ 2 ∂ν :=
          integral_add (hI1.add hI2) hI3
        rw [h1, hsp2, hsp3, hA, hB, hC]
        ring
      have hQv : Qf s = ((c0 s / 2 : ℝ) : ℂ) := by
        show (1 / 2 : ℂ) * ((c0 s : ℝ) : ℂ) = ((c0 s / 2 : ℝ) : ℂ)
        push_cast
        ring
      have hexp_norm : ∀ x : EuclideanSpace ℝ (Fin d),
          ‖Complex.exp (uf s x)‖ = Real.exp (c0 s / 2) := by
        intro x
        show ‖Complex.exp (((th s x : ℝ) : ℂ) * Complex.I + Qf s)‖ = Real.exp (c0 s / 2)
        rw [Complex.exp_add, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, hQv,
          Complex.norm_exp_ofReal]
      have hexp_int : Integrable (fun x : EuclideanSpace ℝ (Fin d) => Complex.exp (uf s x)) ν := by
        refine (integrable_const (Real.exp (c0 s / 2))).mono' ?_ ?_
        · exact (by fun_prop : Continuous fun x : EuclideanSpace ℝ (Fin d) => Complex.exp (uf s x)).aestronglyMeasurable
        · filter_upwards with x
          rw [hexp_norm x]
      have hRf_int : Integrable (fun x : EuclideanSpace ℝ (Fin d) => Rf s x) ν := by
        refine (((hexp_int.sub (integrable_const 1)).sub hu_int).sub (hu2_int.mul_const ((2:ℂ)⁻¹))).congr ?_
        filter_upwards with x
        show Complex.exp (uf s x) - 1 - uf s x - (uf s x) ^ 2 * (2:ℂ)⁻¹
            = Complex.exp (uf s x) - 1 - uf s x - (uf s x) ^ 2 / 2
        rw [div_eq_mul_inv]
      have hsum_int : Integrable (fun x : EuclideanSpace ℝ (Fin d) => uf s x + (uf s x) ^ 2 / 2) ν :=
        hu_int.add (hu2_int.mul_const ((2:ℂ)⁻¹))
      have hkey : ∫ x : EuclideanSpace ℝ (Fin d), (uf s x + (uf s x) ^ 2 / 2) ∂ν = Qf s ^ 2 / 2 := by
        have h1 : ∫ x : EuclideanSpace ℝ (Fin d), (uf s x + (uf s x) ^ 2 / 2) ∂ν
            = (∫ x : EuclideanSpace ℝ (Fin d), uf s x ∂ν)
              + ∫ x : EuclideanSpace ℝ (Fin d), (uf s x) ^ 2 / 2 ∂ν :=
          integral_add hu_int (hu2_int.mul_const ((2:ℂ)⁻¹))
        have h2 : ∫ x : EuclideanSpace ℝ (Fin d), (uf s x) ^ 2 / 2 ∂ν
            = (∫ x : EuclideanSpace ℝ (Fin d), (uf s x) ^ 2 ∂ν) / 2 := by
          rw [show (∫ x : EuclideanSpace ℝ (Fin d), (uf s x) ^ 2 / 2 ∂ν)
              = ∫ x : EuclideanSpace ℝ (Fin d), (uf s x) ^ 2 * (2:ℂ)⁻¹ ∂ν from by
                apply integral_congr_ae
                filter_upwards with x
                rw [div_eq_mul_inv]]
          rw [MeasureTheory.integral_mul_const, div_eq_mul_inv]
        rw [h1, h2, hU, hU2, hQv]
        push_cast
        ring
      have hsplit : ∫ x : EuclideanSpace ℝ (Fin d), (Complex.exp (uf s x) - 1) ∂ν
          = ∫ x : EuclideanSpace ℝ (Fin d), (Rf s x + (uf s x + (uf s x) ^ 2 / 2)) ∂ν := by
        apply integral_congr_ae
        filter_upwards with x
        show Complex.exp (uf s x) - 1
            = (Complex.exp (uf s x) - 1 - uf s x - (uf s x) ^ 2 / 2) + (uf s x + (uf s x) ^ 2 / 2)
        ring
      rw [hsplit, integral_add hRf_int hsum_int, hkey]
    have hrem : ∀ᶠ s : EuclideanSpace ℝ (Fin d) in 𝓝 0,
        ∫ x : EuclideanSpace ℝ (Fin d), ‖Rf s x‖ ∂ν ≤ eta * ‖s‖ ^ 2 / 2 :=
      statopia_math_node_1864527449_b0cc0f87 d ν hsecond m c0 M hM1 hQ_le eta heta
    have hsmallQ : ∀ᶠ s : EuclideanSpace ℝ (Fin d) in 𝓝 0, ‖Qf s‖ ^ 2 / 2 ≤ eta * ‖s‖ ^ 2 / 2 := by
      have hcont : Tendsto (fun s : EuclideanSpace ℝ (Fin d) => M ^ 2 * ‖s‖ ^ 2) (𝓝 0) (𝓝 0) := by
        have h1 : Tendsto (fun s : EuclideanSpace ℝ (Fin d) => ‖s‖) (𝓝 0) (𝓝 0) := by
          simpa using (continuous_norm.tendsto (0 : EuclideanSpace ℝ (Fin d)))
        have h2 : Tendsto (fun s : EuclideanSpace ℝ (Fin d) => ‖s‖ ^ 2) (𝓝 0) (𝓝 0) := by
          simpa using h1.pow 2
        simpa using h2.const_mul (M ^ 2)
      have h1 : ∀ᶠ s : EuclideanSpace ℝ (Fin d) in 𝓝 0, M ^ 2 * ‖s‖ ^ 2 < eta :=
        (tendsto_order.1 hcont).2 eta heta
      filter_upwards [h1] with s hs
      have h4 : (0:ℝ) ≤ ‖s‖ ^ 2 := by positivity
      have h2 : ‖Qf s‖ ≤ M * ‖s‖ ^ 2 := hQ_le s
      have h5 : (0:ℝ) ≤ ‖Qf s‖ := norm_nonneg _
      have h6 : (0:ℝ) ≤ M := le_trans zero_le_one hM1
      have hb : (0:ℝ) ≤ M * ‖s‖ ^ 2 := mul_nonneg h6 h4
      have hstep1 : ‖Qf s‖ ^ 2 ≤ (M * ‖s‖ ^ 2) ^ 2 := by
        have h7 : ‖Qf s‖ * ‖Qf s‖ ≤ (M * ‖s‖ ^ 2) * (M * ‖s‖ ^ 2) :=
          mul_le_mul h2 h2 h5 hb
        calc ‖Qf s‖ ^ 2 = ‖Qf s‖ * ‖Qf s‖ := by ring
          _ ≤ (M * ‖s‖ ^ 2) * (M * ‖s‖ ^ 2) := h7
          _ = (M * ‖s‖ ^ 2) ^ 2 := by ring
      have hstep2 : (M * ‖s‖ ^ 2) ^ 2 = (M ^ 2 * ‖s‖ ^ 2) * ‖s‖ ^ 2 := by ring
      have h8 : (M ^ 2 * ‖s‖ ^ 2) * ‖s‖ ^ 2 ≤ eta * ‖s‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (le_of_lt hs) h4
      rw [← hstep2] at h8
      have h10 : ‖Qf s‖ ^ 2 ≤ eta * ‖s‖ ^ 2 := le_trans hstep1 h8
      linarith [h10]
    filter_upwards [hrem, hsmallQ] with s hrm hsm
    calc ‖∫ x : EuclideanSpace ℝ (Fin d), (Complex.exp (uf s x) - 1) ∂ν‖
        = ‖(∫ x : EuclideanSpace ℝ (Fin d), Rf s x ∂ν) + Qf s ^ 2 / 2‖ := by rw [hdecomp s]
      _ ≤ ‖∫ x : EuclideanSpace ℝ (Fin d), Rf s x ∂ν‖ + ‖Qf s ^ 2 / 2‖ := norm_add_le _ _
      _ ≤ (∫ x : EuclideanSpace ℝ (Fin d), ‖Rf s x‖ ∂ν) + ‖Qf s‖ ^ 2 / 2 := by
          have h1 : ‖∫ x : EuclideanSpace ℝ (Fin d), Rf s x ∂ν‖
              ≤ ∫ x : EuclideanSpace ℝ (Fin d), ‖Rf s x‖ ∂ν :=
            MeasureTheory.norm_integral_le_integral_norm _
          have h2 : ‖Qf s ^ 2 / 2‖ = ‖Qf s‖ ^ 2 / 2 := by
            rw [norm_div, norm_pow]
            norm_num
          rw [h2]
          linarith
      _ ≤ eta * ‖s‖ ^ 2 / 2 + eta * ‖s‖ ^ 2 / 2 := by linarith
      _ = eta * ‖s‖ ^ 2 := by ring
  exact hmain eta heta
  /- @proof-region region.target-node.session.9ab3de3792b561de end -/
