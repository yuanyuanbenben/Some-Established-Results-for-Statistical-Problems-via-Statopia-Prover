import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q01.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q01.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q01.ProvedNodes.Node_182460122_95784152_af93ace5
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

set_option autoImplicit false in
theorem statopia_math_node_3456905758_2fd530dc : ∀ (d : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure ν]
    (hsecond : Integrable (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖ ^ 2) ν),
      ∃ delta : ℝ, 0 < delta ∧
        ∃ eps : EuclideanSpace ℝ (Fin d) → ℂ, eps 0 = 0 ∧
          (∀ eta : ℝ, 0 < eta →
            ∃ rho : ℝ, 0 < rho ∧ rho ≤ delta ∧
              ∀ s : EuclideanSpace ℝ (Fin d), ‖s‖ < rho → ‖eps s‖ ≤ eta * ‖s‖ ^ 2) ∧
          (∀ s : EuclideanSpace ℝ (Fin d), ‖s‖ < delta →
            charFun ν s =
              Complex.exp
                (Complex.I * (↑(inner ℝ s (∫ x : EuclideanSpace ℝ (Fin d), x ∂ν)) : ℂ) -
                  (1 / 2 : ℂ) *
                    ((∑ j : Fin d, ∑ k : Fin d, s j * s k *
                        (∫ x : EuclideanSpace ℝ (Fin d),
                          (x j - (∫ y : EuclideanSpace ℝ (Fin d), y ∂ν) j) *
                            (x k - (∫ y : EuclideanSpace ℝ (Fin d), y ∂ν) k) ∂ν)) : ℂ) +
                  eps s)) := by
  /- @proof-region region.target-node.session.fb7f890103486b1d begin -/
  intro d ν _ hsecond
  have hb : Integrable (fun x : EuclideanSpace ℝ (Fin d) => (1 : ℝ) + ‖x‖ ^ 2) ν :=
    (integrable_const (1 : ℝ)).add hsecond
  have hnorm : Integrable (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖) ν := by
    refine hb.mono (by measurability) ?_
    filter_upwards with x
    have h1 : ‖(1 : ℝ) + ‖x‖ ^ 2‖ = 1 + ‖x‖ ^ 2 := by
      rw [Real.norm_eq_abs]
      exact abs_of_nonneg (by linarith [sq_nonneg ‖x‖])
    have h2 : ‖‖x‖‖ = ‖x‖ := by
      rw [Real.norm_eq_abs]
      exact abs_of_nonneg (norm_nonneg x)
    rw [h1, h2] at *
    nlinarith [sq_nonneg (‖x‖ - 1), norm_nonneg x]
  have hid : Integrable (fun x : EuclideanSpace ℝ (Fin d) => x) ν :=
    hnorm.mono' (by measurability) (by filter_upwards with x; exact le_rfl)
  set m : EuclideanSpace ℝ (Fin d) := ∫ x : EuclideanSpace ℝ (Fin d), x ∂ν with hm
  have hcent : Integrable (fun x : EuclideanSpace ℝ (Fin d) => x - m) ν :=
    hid.sub (integrable_const m)
  have hexp_norm : ∀ a : ℝ, ‖Complex.exp (↑a * Complex.I)‖ = 1 := by
    intro a
    rw [Complex.norm_exp]
    simp [Complex.mul_re]
  have hchar : ∀ s : EuclideanSpace ℝ (Fin d),
      charFun ν s = ∫ x : EuclideanSpace ℝ (Fin d),
        Complex.exp (↑(inner ℝ x s) * Complex.I) ∂ν := by
    intro s
    rw [MeasureTheory.charFun_eq_integral_probChar]
    simp [Real.probChar]
  have hchar0 : charFun ν 0 = 1 := by
    rw [hchar 0]
    have h1 : (fun x : EuclideanSpace ℝ (Fin d) =>
        Complex.exp (↑(inner ℝ x (0 : EuclideanSpace ℝ (Fin d))) * Complex.I)) =
        fun _ => (1 : ℂ) := by
      funext x
      simp
    rw [h1]
    simp
  let g : EuclideanSpace ℝ (Fin d) → ℂ :=
    fun s => charFun ν s * Complex.exp (-(Complex.I * ↑(inner ℝ s m)))
  have hg0 : g 0 = 1 := by
    show charFun ν 0 *
      Complex.exp (-(Complex.I * ↑(inner ℝ (0 : EuclideanSpace ℝ (Fin d)) m))) = 1
    rw [hchar0]
    simp
  have hg_int : ∀ s : EuclideanSpace ℝ (Fin d),
      g s = ∫ x : EuclideanSpace ℝ (Fin d),
        Complex.exp (↑(inner ℝ (x - m) s) * Complex.I) ∂ν := by
    intro s
    have hc : g s = (∫ x : EuclideanSpace ℝ (Fin d),
        Complex.exp (↑(inner ℝ x s) * Complex.I) ∂ν) *
        Complex.exp (-(Complex.I * ↑(inner ℝ s m))) := by
      show charFun ν s * Complex.exp (-(Complex.I * ↑(inner ℝ s m))) =
        (∫ x : EuclideanSpace ℝ (Fin d), Complex.exp (↑(inner ℝ x s) * Complex.I) ∂ν) *
          Complex.exp (-(Complex.I * ↑(inner ℝ s m)))
      rw [hchar s]
    have hFc : (∫ x : EuclideanSpace ℝ (Fin d),
          Complex.exp (↑(inner ℝ x s) * Complex.I) ∂ν) *
        Complex.exp (-(Complex.I * ↑(inner ℝ s m))) =
        ∫ x : EuclideanSpace ℝ (Fin d),
          Complex.exp (-(Complex.I * ↑(inner ℝ s m))) *
            Complex.exp (↑(inner ℝ x s) * Complex.I) ∂ν := by
      rw [mul_comm (∫ x : EuclideanSpace ℝ (Fin d),
          Complex.exp (↑(inner ℝ x s) * Complex.I) ∂ν), MeasureTheory.integral_const_mul]
    rw [hc, hFc]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show Complex.exp (-(Complex.I * ↑(inner ℝ s m))) *
        Complex.exp (↑(inner ℝ x s) * Complex.I) =
      Complex.exp (↑(inner ℝ (x - m) s) * Complex.I)
    rw [← Complex.exp_add]
    congr 1
    rw [inner_sub_left, real_inner_comm m s]
    push_cast
    ring
  have hsig0 : (∑ j : Fin d, ∑ k : Fin d, (0 : EuclideanSpace ℝ (Fin d)) j *
      (0 : EuclideanSpace ℝ (Fin d)) k *
        (∫ x : EuclideanSpace ℝ (Fin d), (x j - m j) * (x k - m k) ∂ν)) = 0 := by
    simp
  let h : EuclideanSpace ℝ (Fin d) → ℂ := fun s =>
    g s * Complex.exp ((1 / 2 : ℂ) * ↑(∑ j : Fin d, ∑ k : Fin d, s j * s k *
      (∫ x : EuclideanSpace ℝ (Fin d), (x j - m j) * (x k - m k) ∂ν)))
  have hZ_int : ∀ s : EuclideanSpace ℝ (Fin d), h s - 1 =
      ∫ x : EuclideanSpace ℝ (Fin d),
        (Complex.exp (↑(inner ℝ (x - m) s) * Complex.I +
          (1 / 2 : ℂ) * ↑(∑ j : Fin d, ∑ k : Fin d, s j * s k *
            (∫ y : EuclideanSpace ℝ (Fin d), (y j - m j) * (y k - m k) ∂ν))) - 1) ∂ν := by
    intro s
    let QQ : ℂ := (1 / 2 : ℂ) * ↑(∑ j : Fin d, ∑ k : Fin d, s j * s k *
      (∫ y : EuclideanSpace ℝ (Fin d), (y j - m j) * (y k - m k) ∂ν))
    have hstep1 : h s = ∫ x : EuclideanSpace ℝ (Fin d),
        Complex.exp (↑(inner ℝ (x - m) s) * Complex.I + QQ) ∂ν := by
      have h1 : h s = (∫ x : EuclideanSpace ℝ (Fin d),
          Complex.exp (↑(inner ℝ (x - m) s) * Complex.I) ∂ν) * Complex.exp QQ := by
        show g s * Complex.exp QQ =
          (∫ x : EuclideanSpace ℝ (Fin d),
            Complex.exp (↑(inner ℝ (x - m) s) * Complex.I) ∂ν) * Complex.exp QQ
        rw [hg_int s]
      rw [h1, mul_comm (∫ x : EuclideanSpace ℝ (Fin d),
          Complex.exp (↑(inner ℝ (x - m) s) * Complex.I) ∂ν) (Complex.exp QQ),
        ← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show Complex.exp QQ * Complex.exp (↑(inner ℝ (x - m) s) * Complex.I) =
        Complex.exp (↑(inner ℝ (x - m) s) * Complex.I + QQ)
      rw [← Complex.exp_add, add_comm]
    have hint : Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
        Complex.exp (↑(inner ℝ (x - m) s) * Complex.I + QQ)) ν := by
      refine (integrable_const ‖Complex.exp QQ‖).mono' ?_ ?_
      · exact (by fun_prop : Continuous fun x : EuclideanSpace ℝ (Fin d) =>
          Complex.exp (↑(inner ℝ (x - m) s) * Complex.I + QQ)).aestronglyMeasurable
      · filter_upwards with x
        rw [Complex.exp_add, norm_mul, hexp_norm]
        simp
    have hconst : Integrable (fun _ : EuclideanSpace ℝ (Fin d) => (1 : ℂ)) ν :=
      integrable_const 1
    have hsub : (∫ x : EuclideanSpace ℝ (Fin d),
        Complex.exp (↑(inner ℝ (x - m) s) * Complex.I + QQ) ∂ν) - 1 =
        ∫ x : EuclideanSpace ℝ (Fin d),
          (Complex.exp (↑(inner ℝ (x - m) s) * Complex.I + QQ) - 1) ∂ν := by
      rw [MeasureTheory.integral_sub hint hconst]
      simp
    calc h s - 1 = (∫ x : EuclideanSpace ℝ (Fin d),
          Complex.exp (↑(inner ℝ (x - m) s) * Complex.I + QQ) ∂ν) - 1 := by rw [hstep1]
      _ = ∫ x : EuclideanSpace ℝ (Fin d),
          (Complex.exp (↑(inner ℝ (x - m) s) * Complex.I + QQ) - 1) ∂ν := hsub
  have hZ' : ∀ eta : ℝ, 0 < eta → ∀ᶠ s : EuclideanSpace ℝ (Fin d) in 𝓝 0,
      ‖∫ x : EuclideanSpace ℝ (Fin d),
        (Complex.exp (↑(inner ℝ (x - m) s) * Complex.I +
          (1 / 2 : ℂ) * ↑(∑ j : Fin d, ∑ k : Fin d, s j * s k *
            (∫ y : EuclideanSpace ℝ (Fin d), (y j - m j) * (y k - m k) ∂ν))) - 1) ∂ν‖
        ≤ eta * ‖s‖ ^ 2 := by
    intro eta heta
    exact statopia_math_node_182460122_95784152 d ν hsecond eta heta
  have hZ : ∀ eta : ℝ, 0 < eta → ∀ᶠ s : EuclideanSpace ℝ (Fin d) in 𝓝 0,
      ‖h s - 1‖ ≤ eta * ‖s‖ ^ 2 := by
    intro eta heta
    filter_upwards [hZ' eta heta] with s hs
    rwa [hZ_int s]
  have hh0 : h 0 = 1 := by
    show g 0 * Complex.exp ((1 / 2 : ℂ) * ↑(∑ j : Fin d, ∑ k : Fin d,
      (0 : EuclideanSpace ℝ (Fin d)) j * (0 : EuclideanSpace ℝ (Fin d)) k *
        (∫ x : EuclideanSpace ℝ (Fin d), (x j - m j) * (x k - m k) ∂ν))) = 1
    rw [hg0, hsig0]
    simp
  have hh_ne : ∀ᶠ s : EuclideanSpace ℝ (Fin d) in 𝓝 0, h s ≠ 0 := by
    obtain ⟨dd, hddpos, hdd⟩ := Metric.eventually_nhds_iff.mp (hZ (1 / 2) (by norm_num))
    have hball : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) dd ∈ 𝓝 0 :=
      Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hddpos)
    have h1ball : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1 ∈ 𝓝 0 :=
      Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self one_pos)
    filter_upwards [hball, h1ball] with s hs hs1
    have hle : ‖h s - 1‖ ≤ (1 / 2) * ‖s‖ ^ 2 := hdd hs
    have hs1' : ‖s‖ < 1 := by simpa using hs1
    intro hzero
    rw [hzero] at hle
    have hone : ‖((0 : ℂ) - 1)‖ = 1 := by simp
    rw [hone] at hle
    nlinarith [hs1', norm_nonneg s, sq_nonneg ‖s‖]
  have hexp_mul_neg : ∀ w : ℂ, Complex.exp (-w) * Complex.exp w = 1 := by
    intro w
    rw [← Complex.exp_add]
    simp
  have hpsib2 : ∀ eta : ℝ, 0 < eta → ∀ᶠ s : EuclideanSpace ℝ (Fin d) in 𝓝 0,
      ‖Complex.log (h s)‖ ≤ eta * ‖s‖ ^ 2 := by
    intro eta heta
    have hA : ∀ᶠ s : EuclideanSpace ℝ (Fin d) in 𝓝 0,
        ‖h s - 1‖ ≤ (eta / 8) * ‖s‖ ^ 2 := hZ (eta / 8) (by linarith)
    have hB : ∀ᶠ s : EuclideanSpace ℝ (Fin d) in 𝓝 0,
        ‖h s - 1‖ ≤ (1 / 2) * ‖s‖ ^ 2 := hZ (1 / 2) (by norm_num)
    have hC : ∀ᶠ s : EuclideanSpace ℝ (Fin d) in 𝓝 0, ‖s‖ ^ 2 ≤ 1 := by
      have hball : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1 ∈ 𝓝 0 :=
        Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self one_pos)
      filter_upwards [hball] with s hs
      have hs1 : ‖s‖ < 1 := by simpa using hs
      nlinarith [norm_nonneg s]
    filter_upwards [hA, hB, hC] with s hAle hBle hCs
    have hz0 : (0 : ℝ) ≤ ‖h s - 1‖ := norm_nonneg _
    have hz : ‖h s - 1‖ ≤ 1 / 2 := by
      have h2 : (1 / 2) * ‖s‖ ^ 2 ≤ 1 / 2 := by linarith
      linarith
    have hlt : ‖h s - 1‖ < 1 := by linarith
    have hinv : (1 - ‖h s - 1‖)⁻¹ ≤ 2 := by
      have hpos : (0 : ℝ) < 1 - ‖h s - 1‖ := by linarith
      have hge : (1 : ℝ) / 2 ≤ 1 - ‖h s - 1‖ := by linarith
      have hmul : (1 - ‖h s - 1‖) * (1 - ‖h s - 1‖)⁻¹ = 1 :=
        mul_inv_cancel₀ (ne_of_gt hpos)
      nlinarith [hpos, hge, hmul]
    have hterm : ‖h s - 1‖ ^ 2 * (1 - ‖h s - 1‖)⁻¹ / 2 ≤ ‖h s - 1‖ ^ 2 := by
      have h2 : (0 : ℝ) ≤ ‖h s - 1‖ ^ 2 := sq_nonneg _
      have h3 : ‖h s - 1‖ ^ 2 * (1 - ‖h s - 1‖)⁻¹ ≤ ‖h s - 1‖ ^ 2 * 2 :=
        mul_le_mul_of_nonneg_left hinv h2
      linarith
    have hlog := Complex.norm_log_one_add_le (z := h s - 1) hlt
    have harg : (1 : ℂ) + (h s - 1) = h s := by ring
    rw [harg] at hlog
    have hb1 : ‖Complex.log (h s)‖ ≤ ‖h s - 1‖ ^ 2 + ‖h s - 1‖ := by linarith
    have hsqq : ‖h s - 1‖ ^ 2 ≤ (eta / 16) * ‖s‖ ^ 2 := by
      have hstep : ‖h s - 1‖ ^ 2 ≤ ‖h s - 1‖ * (1 / 2) := by
        rw [pow_two]
        exact mul_le_mul_of_nonneg_left hz hz0
      have hstep2 : ‖h s - 1‖ * (1 / 2) ≤ ((eta / 8) * ‖s‖ ^ 2) * (1 / 2) :=
        mul_le_mul_of_nonneg_right hAle (by norm_num)
      have hrw : ((eta / 8) * ‖s‖ ^ 2) * (1 / 2) = (eta / 16) * ‖s‖ ^ 2 := by ring
      linarith
    have hfin : ‖h s - 1‖ ^ 2 + ‖h s - 1‖ ≤ (eta / 16 + eta / 8) * ‖s‖ ^ 2 := by
      have hrw : (eta / 16 + eta / 8) * ‖s‖ ^ 2 =
          (eta / 16) * ‖s‖ ^ 2 + (eta / 8) * ‖s‖ ^ 2 := by ring
      linarith
    calc ‖Complex.log (h s)‖ ≤ ‖h s - 1‖ ^ 2 + ‖h s - 1‖ := hb1
      _ ≤ (eta / 16 + eta / 8) * ‖s‖ ^ 2 := hfin
      _ ≤ eta * ‖s‖ ^ 2 := by
          have hnn : (0 : ℝ) ≤ ‖s‖ ^ 2 := sq_nonneg _
          nlinarith [hnn, heta]
  have hkey : ∀ s : EuclideanSpace ℝ (Fin d), h s ≠ 0 → charFun ν s =
      Complex.exp (Complex.I * ↑(inner ℝ s m) - (1 / 2 : ℂ) *
        ↑(∑ j : Fin d, ∑ k : Fin d, s j * s k *
          (∫ x : EuclideanSpace ℝ (Fin d), (x j - m j) * (x k - m k) ∂ν)) +
        Complex.log (h s)) := by
    intro s hs
    let QQ : ℂ := (1 / 2 : ℂ) * ↑(∑ j : Fin d, ∑ k : Fin d, s j * s k *
      (∫ x : EuclideanSpace ℝ (Fin d), (x j - m j) * (x k - m k) ∂ν))
    let AA : ℂ := Complex.I * ↑(inner ℝ s m)
    have hcs : charFun ν s = g s * Complex.exp AA := by
      have hneg : Complex.exp AA * Complex.exp (-AA) = 1 := by
        have h := hexp_mul_neg AA
        rwa [mul_comm] at h
      calc charFun ν s = charFun ν s * 1 := by ring
        _ = charFun ν s * (Complex.exp AA * Complex.exp (-AA)) := by rw [hneg]
        _ = (charFun ν s * Complex.exp (-AA)) * Complex.exp AA := by ring
        _ = g s * Complex.exp AA := by
              rw [show g s = charFun ν s * Complex.exp (-AA) from rfl]
    have hcalc : Complex.exp (AA - QQ + Complex.log (h s)) = g s * Complex.exp AA := by
      have h1 : AA - QQ + Complex.log (h s) = AA + (-QQ + Complex.log (h s)) := by ring
      rw [h1, Complex.exp_add, Complex.exp_add, Complex.exp_log hs]
      rw [show h s = g s * Complex.exp QQ from rfl]
      calc Complex.exp AA * (Complex.exp (-QQ) * (g s * Complex.exp QQ))
          = (Complex.exp AA * g s) * (Complex.exp (-QQ) * Complex.exp QQ) := by ring
        _ = Complex.exp AA * g s := by rw [hexp_mul_neg QQ]; ring
        _ = g s * Complex.exp AA := by ring
    show charFun ν s = Complex.exp (AA - QQ + Complex.log (h s))
    rw [hcs, hcalc]
  obtain ⟨d0, hd0pos, hd0⟩ := Metric.eventually_nhds_iff.mp hh_ne
  refine ⟨d0, hd0pos, fun s => Complex.log (h s), ?_, ?_, ?_⟩
  · show Complex.log (h 0) = 0
    rw [hh0, Complex.log_one]
  · intro eta heta
    obtain ⟨r, hrpos, hr⟩ := Metric.eventually_nhds_iff.mp (hpsib2 eta heta)
    exact ⟨min r d0, lt_min hrpos hd0pos, min_le_right r d0, fun s hs => by
      refine hr ?_
      have h1 : ‖s‖ < r := lt_of_lt_of_le hs (min_le_left _ _)
      simpa using h1⟩
  · intro s hs
    have hne : h s ≠ 0 := hd0 (by simpa using hs)
    have h := hkey s hne
    simp only [hm] at h ⊢
    push_cast at h ⊢
    exact h
  /- @proof-region region.target-node.session.fb7f890103486b1d end -/
