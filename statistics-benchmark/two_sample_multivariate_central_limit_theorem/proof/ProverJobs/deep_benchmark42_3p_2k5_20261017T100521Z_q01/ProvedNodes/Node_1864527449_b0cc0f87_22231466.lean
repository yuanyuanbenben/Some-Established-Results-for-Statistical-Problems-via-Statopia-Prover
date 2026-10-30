import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q01.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q01.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q01.ProvedNodes.Node_3980798612_87c1b9de_8c55c5f3

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

set_option autoImplicit false in
theorem statopia_math_node_1864527449_b0cc0f87 : ∀ (d : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure ν]
    (hsecond : Integrable (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖ ^ 2) ν)
    (m : EuclideanSpace ℝ (Fin d)) (c0 : EuclideanSpace ℝ (Fin d) → ℝ) (M : ℝ)
    (hM : 1 ≤ M)
    (hQ : ∀ s : EuclideanSpace ℝ (Fin d),
      ‖(1 / 2 : ℂ) * ((c0 s : ℝ) : ℂ)‖ ≤ M * ‖s‖ ^ 2)
    (eta : ℝ) (heta : 0 < eta),
    ∀ᶠ s : EuclideanSpace ℝ (Fin d) in 𝓝 (0 : EuclideanSpace ℝ (Fin d)),
      ∫ x : EuclideanSpace ℝ (Fin d),
          ‖Complex.exp (((inner ℝ (x - m) s : ℝ) : ℂ) * Complex.I + (1 / 2 : ℂ) * ((c0 s : ℝ) : ℂ))
            - 1
            - (((inner ℝ (x - m) s : ℝ) : ℂ) * Complex.I + (1 / 2 : ℂ) * ((c0 s : ℝ) : ℂ))
            - (((inner ℝ (x - m) s : ℝ) : ℂ) * Complex.I + (1 / 2 : ℂ) * ((c0 s : ℝ) : ℂ)) ^ 2 / 2‖ ∂ν
        ≤ eta * ‖s‖ ^ 2 / 2 := by
  /- @proof-region region.target-node.session.17b3add3738552bf begin -/
  intro d ν hν hsecond m c0 M hM hQ eta heta
  set Q : EuclideanSpace ℝ (Fin d) → ℂ := fun s => (1 / 2 : ℂ) * ((c0 s : ℝ) : ℂ) with hQdef
  set u : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℂ :=
    fun s x => ((inner ℝ (x - m) s : ℝ) : ℂ) * Complex.I + Q s with hudef
  set R : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℂ :=
    fun s x => Complex.exp (u s x) - 1 - u s x - (u s x) ^ 2 / 2 with hRdef
  set Kc : ℝ := 4 * (Real.exp 1 + 4) with hKcdef
  set bd : EuclideanSpace ℝ (Fin d) → ℝ := fun x => 2 * Kc * (‖x - m‖ ^ 2 + M ^ 2) with hbddef
  have hKc1 : (1 : ℝ) ≤ Kc := by
    rw [hKcdef]; nlinarith [Real.exp_pos 1]
  have hexpKc : Real.exp 1 ≤ Kc := by
    rw [hKcdef]; nlinarith [Real.exp_pos 1]
  have hKcpos : (0 : ℝ) < Kc := lt_of_lt_of_le one_pos hKc1
  have hQre : ∀ s, (Q s).re = c0 s / 2 := by
    intro s
    show ((1 / 2 : ℂ) * ((c0 s : ℝ) : ℂ)).re = c0 s / 2
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_mul,
      Complex.ofReal_re]
    ring
  have hQrele : ∀ s, (Q s).re ≤ M * ‖s‖ ^ 2 := fun s =>
    le_trans (Complex.re_le_norm (Q s)) (hQ s)
  have hure : ∀ s x, (u s x).re = (Q s).re := by
    intro s x
    show (((inner ℝ (x - m) s : ℝ) : ℂ) * Complex.I + Q s).re = (Q s).re
    rw [Complex.add_re, Complex.mul_re]
    simp
  have hunorm : ∀ s x, ‖s‖ ≤ 1 → ‖u s x‖ ≤ ‖s‖ * (‖x - m‖ + M) := by
    intro s x hs1
    show ‖((inner ℝ (x - m) s : ℝ) : ℂ) * Complex.I + Q s‖ ≤ ‖s‖ * (‖x - m‖ + M)
    have h1 : ‖((inner ℝ (x - m) s : ℝ) : ℂ) * Complex.I‖ = |inner ℝ (x - m) s| :=
      Statlib.StatFoundation.Convergence.BerryEsseen.norm_ofReal_mul_I _
    have hs2 : ‖s‖ ^ 2 ≤ ‖s‖ := by
      have h0 : (0 : ℝ) ≤ ‖s‖ := norm_nonneg s
      calc ‖s‖ ^ 2 = ‖s‖ * ‖s‖ := by ring
        _ ≤ ‖s‖ * 1 := by exact mul_le_mul_of_nonneg_left hs1 h0
        _ = ‖s‖ := by ring
    have hMQ : ‖Q s‖ ≤ M * ‖s‖ := by
      have h := hQ s
      have h2 : M * ‖s‖ ^ 2 ≤ M * ‖s‖ :=
        mul_le_mul_of_nonneg_left hs2 (by linarith)
      linarith
    calc ‖((inner ℝ (x - m) s : ℝ) : ℂ) * Complex.I + Q s‖
        ≤ ‖((inner ℝ (x - m) s : ℝ) : ℂ) * Complex.I‖ + ‖Q s‖ := norm_add_le _ _
      _ ≤ ‖x - m‖ * ‖s‖ + M * ‖s‖ :=
          add_le_add (by rw [h1]; exact abs_real_inner_le_norm _ _) hMQ
      _ = ‖s‖ * (‖x - m‖ + M) := by ring
  have h2norm : ‖(2 : ℂ)‖ = 2 := by simp
  have hexpnorm : ∀ s x, ‖Complex.exp (u s x)‖ = Real.exp (c0 s / 2) := by
    intro s x
    rw [Complex.norm_exp, hure s x, hQre s]
  have hRbound : ∀ s x, ‖s‖ ≤ 1 → M * ‖s‖ ^ 2 ≤ 1 → ‖R s x‖ ≤ Kc * ‖u s x‖ ^ 2 := by
    intro s x hs1 hMs
    have hc0le : c0 s / 2 ≤ 1 := by
      rw [← hQre s]
      exact le_trans (hQrele s) hMs
    have hupper : ‖Complex.exp (u s x)‖ ≤ Real.exp 1 := by
      rw [hexpnorm s x]
      exact Real.exp_le_exp.2 hc0le
    show ‖Complex.exp (u s x) - 1 - u s x - (u s x) ^ 2 / 2‖ ≤ Kc * ‖u s x‖ ^ 2
    by_cases hu : ‖u s x‖ ≤ 1
    · have h3 := statopia_math_node_3980798612_87c1b9de (u s x) hu
      have hcube : ‖u s x‖ ^ 3 ≤ ‖u s x‖ ^ 2 := by
        have hm := mul_le_mul_of_nonneg_left hu (sq_nonneg ‖u s x‖)
        nlinarith
      have hKmul : ‖u s x‖ ^ 2 ≤ Kc * ‖u s x‖ ^ 2 := by
        simpa using mul_le_mul_of_nonneg_right hKc1 (sq_nonneg ‖u s x‖)
      linarith
    · push_neg at hu
      have hu1 : (1 : ℝ) ≤ ‖u s x‖ := le_of_lt hu
      have hu2 : (1 : ℝ) ≤ ‖u s x‖ ^ 2 := by nlinarith
      have hul : ‖u s x‖ ≤ ‖u s x‖ ^ 2 := by nlinarith
      have hD : ‖(u s x) ^ 2 / 2‖ ≤ ‖u s x‖ ^ 2 := by
        rw [norm_div, norm_pow, h2norm]
        nlinarith [sq_nonneg ‖u s x‖]
      have hA : ‖Complex.exp (u s x) - 1 - u s x - (u s x) ^ 2 / 2‖
          ≤ ‖Complex.exp (u s x) - 1 - u s x‖ + ‖(u s x) ^ 2 / 2‖ := norm_sub_le _ _
      have hB : ‖Complex.exp (u s x) - 1 - u s x‖ ≤ ‖Complex.exp (u s x) - 1‖ + ‖u s x‖ :=
        norm_sub_le _ _
      have hC : ‖Complex.exp (u s x) - 1‖ ≤ ‖Complex.exp (u s x)‖ + 1 := by
        simpa using norm_sub_le (Complex.exp (u s x)) (1 : ℂ)
      have hexp2 : Real.exp 1 ≤ Real.exp 1 * ‖u s x‖ ^ 2 := by
        have hp := mul_le_mul_of_nonneg_left hu2 (le_of_lt (Real.exp_pos 1))
        simpa using hp
      have hKle : Real.exp 1 + 3 ≤ Kc := by
        rw [hKcdef]; nlinarith [Real.exp_pos 1]
      have hsum : Real.exp 1 + 1 + ‖u s x‖ + ‖u s x‖ ^ 2 ≤ (Real.exp 1 + 3) * ‖u s x‖ ^ 2 := by
        nlinarith [hul, hu2, hexp2]
      have hfin : (Real.exp 1 + 3) * ‖u s x‖ ^ 2 ≤ Kc * ‖u s x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hKle (sq_nonneg _)
      linarith
  have huSq : ∀ s x, ‖s‖ ≤ 1 → ‖u s x‖ ^ 2 ≤ ‖s‖ ^ 2 * (‖x - m‖ + M) ^ 2 := by
    intro s x hs1
    have h := hunorm s x hs1
    calc ‖u s x‖ ^ 2 = ‖u s x‖ * ‖u s x‖ := by ring
      _ ≤ (‖s‖ * (‖x - m‖ + M)) * (‖s‖ * (‖x - m‖ + M)) :=
          mul_self_le_mul_self (norm_nonneg _) h
      _ = ‖s‖ ^ 2 * (‖x - m‖ + M) ^ 2 := by ring
  have hcu : ∀ s x, ‖s‖ ≤ 1 → ‖u s x‖ ^ 3 ≤ ‖s‖ ^ 3 * (‖x - m‖ + M) ^ 3 := by
    intro s x hs1
    have h2 := huSq s x hs1
    have h1 := hunorm s x hs1
    have hb2 : (0 : ℝ) ≤ ‖s‖ ^ 2 * (‖x - m‖ + M) ^ 2 := by positivity
    calc ‖u s x‖ ^ 3 = ‖u s x‖ ^ 2 * ‖u s x‖ := by ring
      _ ≤ (‖s‖ ^ 2 * (‖x - m‖ + M) ^ 2) * (‖s‖ * (‖x - m‖ + M)) :=
          mul_le_mul h2 h1 (norm_nonneg _) hb2
      _ = ‖s‖ ^ 3 * (‖x - m‖ + M) ^ 3 := by ring
  have hFcont : ∀ s : EuclideanSpace ℝ (Fin d), Continuous fun x : EuclideanSpace ℝ (Fin d) =>
      ‖R s x‖ * (‖s‖ ^ 2)⁻¹ := by
    intro s
    have hin : Continuous fun x : EuclideanSpace ℝ (Fin d) => inner ℝ (x - m) s := by
      fun_prop
    have hu : Continuous fun x : EuclideanSpace ℝ (Fin d) =>
        ((inner ℝ (x - m) s : ℝ) : ℂ) * Complex.I + Q s :=
      ((Complex.continuous_ofReal.comp hin).mul continuous_const).add continuous_const
    have hRc : Continuous fun x : EuclideanSpace ℝ (Fin d) =>
        Complex.exp (u s x) - 1 - u s x - (u s x) ^ 2 / 2 :=
      (((Complex.continuous_exp.comp hu).sub continuous_const).sub hu).sub
        ((hu.pow 2).div_const 2)
    exact hRc.norm.mul continuous_const
  have hm2int : Integrable (fun x : EuclideanSpace ℝ (Fin d) => ‖x - m‖ ^ 2) ν := by
    have hb : Integrable (fun x : EuclideanSpace ℝ (Fin d) => 2 * ‖x‖ ^ 2 + 2 * ‖m‖ ^ 2) ν :=
      (hsecond.const_mul 2).add (integrable_const (2 * ‖m‖ ^ 2))
    refine hb.mono' ?_ ?_
    · exact ((continuous_id.sub continuous_const).norm.pow 2).aestronglyMeasurable
    · filter_upwards with x
      have h1 := norm_sub_le x m
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      nlinarith [sq_nonneg (‖x‖ - ‖m‖), norm_nonneg x, norm_nonneg m, norm_nonneg (x - m)]
  have hbdint : Integrable bd ν := by
    have h1 : Integrable (fun x : EuclideanSpace ℝ (Fin d) => (2 * Kc) * ‖x - m‖ ^ 2) ν := by
      simpa using hm2int.const_mul (2 * Kc)
    have h2 : Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
        (2 * Kc) * ‖x - m‖ ^ 2 + (2 * Kc) * M ^ 2) ν :=
      h1.add (integrable_const ((2 * Kc) * M ^ 2))
    show Integrable (fun x : EuclideanSpace ℝ (Fin d) => 2 * Kc * (‖x - m‖ ^ 2 + M ^ 2)) ν
    simpa [mul_add] using h2
  have hnorm : Tendsto (fun s : EuclideanSpace ℝ (Fin d) => ‖s‖) (𝓝 0) (𝓝 0) := by
    simpa using continuous_norm.tendsto (0 : EuclideanSpace ℝ (Fin d))
  have hsmall : ∀ᶠ s : EuclideanSpace ℝ (Fin d) in 𝓝 (0 : EuclideanSpace ℝ (Fin d)),
      ‖s‖ ≤ 1 ∧ M * ‖s‖ ^ 2 ≤ 1 := by
    have h1 : ∀ᶠ s : EuclideanSpace ℝ (Fin d) in 𝓝 0, ‖s‖ ≤ 1 := by
      simpa using hnorm.eventually (Iic_mem_nhds (by norm_num : (0:ℝ) < 1))
    have h2 : ∀ᶠ s : EuclideanSpace ℝ (Fin d) in 𝓝 0, M * ‖s‖ ^ 2 ≤ 1 := by
      have hsq : Tendsto (fun s : EuclideanSpace ℝ (Fin d) => ‖s‖ ^ 2) (𝓝 0) (𝓝 0) := by
        simpa using hnorm.pow 2
      have hM2 : Tendsto (fun s : EuclideanSpace ℝ (Fin d) => M * ‖s‖ ^ 2) (𝓝 0) (𝓝 0) := by
        simpa using hsq.const_mul M
      simpa using hM2.eventually (Iic_mem_nhds (by norm_num : (0:ℝ) < 1))
    exact h1.and h2
  have ht_inv : ∀ t : ℝ, 0 ≤ t → t * t⁻¹ ≤ 1 := by
    intro t ht
    rcases eq_or_lt_of_le ht with h | h
    · have hz : t = 0 := h.symm
      rw [hz]
      simp
    · exact le_of_eq (mul_inv_cancel₀ (ne_of_gt h))
  have hdom : ∀ᶠ s : EuclideanSpace ℝ (Fin d) in 𝓝 (0 : EuclideanSpace ℝ (Fin d)),
      ∀ x : EuclideanSpace ℝ (Fin d), ‖R s x‖ * (‖s‖ ^ 2)⁻¹ ≤ bd x := by
    filter_upwards [hsmall] with s hs
    intro x
    show ‖R s x‖ * (‖s‖ ^ 2)⁻¹ ≤ 2 * Kc * (‖x - m‖ ^ 2 + M ^ 2)
    have hinv : (0 : ℝ) ≤ (‖s‖ ^ 2)⁻¹ := inv_nonneg.2 (sq_nonneg _)
    have hsq2 : (‖x - m‖ + M) ^ 2 ≤ 2 * (‖x - m‖ ^ 2 + M ^ 2) := by
      nlinarith [sq_nonneg (‖x - m‖ - M), norm_nonneg (x - m), norm_nonneg m]
    have hstep : ‖R s x‖ * (‖s‖ ^ 2)⁻¹ ≤ Kc * (‖x - m‖ + M) ^ 2 := by
      calc ‖R s x‖ * (‖s‖ ^ 2)⁻¹
          ≤ (Kc * (‖s‖ ^ 2 * (‖x - m‖ + M) ^ 2)) * (‖s‖ ^ 2)⁻¹ := by
            apply mul_le_mul_of_nonneg_right _ hinv
            calc ‖R s x‖ ≤ Kc * ‖u s x‖ ^ 2 := hRbound s x hs.1 hs.2
              _ ≤ Kc * (‖s‖ ^ 2 * (‖x - m‖ + M) ^ 2) :=
                  mul_le_mul_of_nonneg_left (huSq s x hs.1) (le_of_lt hKcpos)
        _ = Kc * (‖s‖ ^ 2 * (‖s‖ ^ 2)⁻¹) * (‖x - m‖ + M) ^ 2 := by ring
        _ ≤ Kc * 1 * (‖x - m‖ + M) ^ 2 := by
            apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
            exact mul_le_mul_of_nonneg_left (ht_inv _ (sq_nonneg _)) (le_of_lt hKcpos)
        _ = Kc * (‖x - m‖ + M) ^ 2 := by ring
    calc ‖R s x‖ * (‖s‖ ^ 2)⁻¹ ≤ Kc * (‖x - m‖ + M) ^ 2 := hstep
      _ ≤ Kc * (2 * (‖x - m‖ ^ 2 + M ^ 2)) := mul_le_mul_of_nonneg_left hsq2 (le_of_lt hKcpos)
      _ = 2 * Kc * (‖x - m‖ ^ 2 + M ^ 2) := by ring
  have hconv : ∀ x : EuclideanSpace ℝ (Fin d),
      Tendsto (fun s : EuclideanSpace ℝ (Fin d) => ‖R s x‖ * (‖s‖ ^ 2)⁻¹) (𝓝 0) (𝓝 0) := by
    intro x
    have hg : Tendsto (fun s : EuclideanSpace ℝ (Fin d) => ‖s‖ * (‖x - m‖ + M) ^ 3)
        (𝓝 0) (𝓝 0) := by
      simpa using hnorm.mul_const ((‖x - m‖ + M) ^ 3)
    refine squeeze_zero' ?_ ?_ hg
    · filter_upwards with s
      exact mul_nonneg (norm_nonneg _) (by positivity)
    · have hu1ev : ∀ᶠ s : EuclideanSpace ℝ (Fin d) in 𝓝 0, ‖u s x‖ ≤ 1 := by
        have ht : Tendsto (fun s : EuclideanSpace ℝ (Fin d) => ‖s‖ * (‖x - m‖ + M))
            (𝓝 0) (𝓝 0) := by
          simpa using hnorm.mul_const (‖x - m‖ + M)
        have hev : ∀ᶠ s : EuclideanSpace ℝ (Fin d) in 𝓝 0, ‖s‖ * (‖x - m‖ + M) ≤ 1 := by
          simpa using ht.eventually (Iic_mem_nhds (by norm_num : (0:ℝ) < 1))
        filter_upwards [hev, hsmall] with s hs1 hs
        exact le_trans (hunorm s x hs.1) hs1
      filter_upwards [hsmall, hu1ev] with s hs hu1
      have hR3 : ‖R s x‖ ≤ ‖u s x‖ ^ 3 := statopia_math_node_3980798612_87c1b9de (u s x) hu1
      have ht3 : ‖s‖ ^ 3 * (‖s‖ ^ 2)⁻¹ ≤ ‖s‖ := by
        have hle := mul_le_mul_of_nonneg_left (ht_inv (‖s‖ ^ 2) (sq_nonneg ‖s‖)) (norm_nonneg s)
        calc ‖s‖ ^ 3 * (‖s‖ ^ 2)⁻¹ = ‖s‖ * (‖s‖ ^ 2 * (‖s‖ ^ 2)⁻¹) := by ring
          _ ≤ ‖s‖ * 1 := hle
          _ = ‖s‖ := by ring
      calc ‖R s x‖ * (‖s‖ ^ 2)⁻¹
          ≤ ‖u s x‖ ^ 3 * (‖s‖ ^ 2)⁻¹ := by
            apply mul_le_mul_of_nonneg_right hR3 (inv_nonneg.2 (sq_nonneg _))
        _ ≤ (‖s‖ ^ 3 * (‖x - m‖ + M) ^ 3) * (‖s‖ ^ 2)⁻¹ := by
            apply mul_le_mul_of_nonneg_right (hcu s x hs.1) (inv_nonneg.2 (sq_nonneg _))
        _ = (‖s‖ ^ 3 * (‖s‖ ^ 2)⁻¹) * (‖x - m‖ + M) ^ 3 := by ring
        _ ≤ ‖s‖ * (‖x - m‖ + M) ^ 3 :=
            mul_le_mul_of_nonneg_right ht3 (by positivity)
  have hDCT : Tendsto (fun s : EuclideanSpace ℝ (Fin d) =>
      ∫ x, ‖R s x‖ * (‖s‖ ^ 2)⁻¹ ∂ν) (𝓝 0) (𝓝 0) := by
    have hm1 : ∀ᶠ s : EuclideanSpace ℝ (Fin d) in 𝓝 0,
        AEStronglyMeasurable (fun x => ‖R s x‖ * (‖s‖ ^ 2)⁻¹) ν := by
      filter_upwards with s
      exact (hFcont s).aestronglyMeasurable
    have hm2 : ∀ᶠ s : EuclideanSpace ℝ (Fin d) in 𝓝 0,
        ∀ᵐ x ∂ν, ‖‖R s x‖ * (‖s‖ ^ 2)⁻¹‖ ≤ bd x := by
      filter_upwards [hdom] with s hs
      filter_upwards with x
      rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (inv_nonneg.2 (sq_nonneg _)))]
      exact hs x
    have hm3 : ∀ᵐ x ∂ν, Tendsto (fun s : EuclideanSpace ℝ (Fin d) => ‖R s x‖ * (‖s‖ ^ 2)⁻¹)
        (𝓝 0) (𝓝 ((fun _ => (0:ℝ)) x)) := by
      filter_upwards with x
      simpa using hconv x
    have key := MeasureTheory.tendsto_integral_filter_of_dominated_convergence (μ := ν)
      (l := 𝓝 (0 : EuclideanSpace ℝ (Fin d)))
      (F := fun s x => ‖R s x‖ * (‖s‖ ^ 2)⁻¹) (f := fun _ => (0:ℝ)) bd hm1 hm2 hbdint hm3
    simpa using key
  have hlim : ∀ᶠ s : EuclideanSpace ℝ (Fin d) in 𝓝 0,
      ∫ x, ‖R s x‖ * (‖s‖ ^ 2)⁻¹ ∂ν < eta / 2 := by
    have hev := hDCT.eventually (Iio_mem_nhds (show (0:ℝ) < eta / 2 by linarith))
    simpa using hev
  filter_upwards [hsmall, hlim] with s hs hlt
  have hint : ∫ x, ‖R s x‖ * (‖s‖ ^ 2)⁻¹ ∂ν = (∫ x, ‖R s x‖ ∂ν) * (‖s‖ ^ 2)⁻¹ :=
    MeasureTheory.integral_mul_const ((‖s‖ ^ 2)⁻¹) (fun x => ‖R s x‖)
  rw [hint] at hlt
  show ∫ x, ‖R s x‖ ∂ν ≤ eta * ‖s‖ ^ 2 / 2
  by_cases h0 : ‖s‖ ^ 2 = 0
  · have hs0 : ‖s‖ = 0 := by
      have hmul : ‖s‖ * ‖s‖ = 0 := by
        rw [← pow_two]
        exact h0
      rcases mul_eq_zero.mp hmul with h | h
      exacts [h, h]
    have hz : ∀ x, ‖R s x‖ = 0 := by
      intro x
      have hu0 : ‖u s x‖ = 0 := by
        have h1 := hunorm s x hs.1
        rw [hs0, zero_mul] at h1
        exact le_antisymm h1 (norm_nonneg _)
      have hb := hRbound s x hs.1 hs.2
      rw [hu0] at hb
      have hb0 : ‖R s x‖ ≤ 0 := by simpa using hb
      exact le_antisymm hb0 (norm_nonneg _)
    have hzint : ∫ x, ‖R s x‖ ∂ν = 0 := by
      rw [show (fun x => ‖R s x‖) = fun _ => (0:ℝ) from funext hz]
      simp
    rw [hzint, h0]
    simp
  · have hstep : (∫ x, ‖R s x‖ ∂ν) * (‖s‖ ^ 2)⁻¹ * ‖s‖ ^ 2 ≤ eta / 2 * ‖s‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (le_of_lt hlt) (sq_nonneg ‖s‖)
    rw [mul_assoc, inv_mul_cancel₀ h0, mul_one] at hstep
    have heq : eta / 2 * ‖s‖ ^ 2 = eta * ‖s‖ ^ 2 / 2 := by ring
    linarith
  /- @proof-region region.target-node.session.17b3add3738552bf end -/
