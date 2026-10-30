import ProverJobs.real_main_theorem_e7f39350f194.Vocabulary
import ProverJobs.real_main_theorem_e7f39350f194.Base
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_3431605529_2a745110_37ebd9aa
open EuclideanGeometry

open EuclideanGeometry

set_option autoImplicit false in
theorem statopia_math_node_3895931102_11f4646c : ∀ (b c k u : Plane) (α γ : ℝ)
    (halpha : 0 < α) (hgamma : 0 < γ)
    (hk : k = α • b + γ • c)
    (hcu : inner ℝ c u = ‖c‖ ^ 2 / 2)
    (hku : inner ℝ k u = ‖k‖ ^ 2 / 2)
    (hangle : InnerProductGeometry.angle (-c) (k - c) = InnerProductGeometry.angle b k),
    inner ℝ b u = 0 := by
  /- @proof-region region.target-node.session.07c0687ff923ccb3 begin -/
  intro b c k u α γ halpha hgamma hk hcu hku hangle
  have hcos : inner ℝ (-c) (k - c) / (‖c‖ * ‖k - c‖) =
      inner ℝ b k / (‖b‖ * ‖k‖) := by
    have h := congrArg Real.cos hangle
    simpa only [InnerProductGeometry.cos_angle, norm_neg] using h
  have hsymm : ∀ x y : Plane, inner ℝ x y = inner ℝ y x := by
    intro x y
    rw [Statlib.HighDim.Vocabulary.inner_eq_sum, Statlib.HighDim.Vocabulary.inner_eq_sum]
    simp only [Fin.sum_univ_two]
    ring
  have hbk : inner ℝ b k = α * inner ℝ b b + γ * inner ℝ b c := by
    rw [hk]
    simp only [inner_add_right, inner_smul_right]
  have hck : inner ℝ c k = α * inner ℝ b c + γ * inner ℝ c c := by
    rw [hk]
    simp only [inner_add_right, inner_smul_right]
    rw [hsymm c b]
  have hkk : inner ℝ k k =
      α ^ 2 * inner ℝ b b + 2 * α * γ * inner ℝ b c + γ ^ 2 * inner ℝ c c := by
    rw [hk]
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]
    rw [hsymm c b]
    simp
    try ring
  have hkmc : inner ℝ (k - c) (k - c) = inner ℝ k k - 2 * inner ℝ k c + inner ℝ c c := by
    simp only [inner_sub_left, inner_sub_right]
    rw [hsymm c k]
    ring
  have hLagrange : ∀ x y : Plane,
      (inner ℝ x y) ^ 2 + (x.ofLp 0 * y.ofLp 1 - x.ofLp 1 * y.ofLp 0) ^ 2 = ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
    intro x y
    rw [Statlib.HighDim.Vocabulary.inner_eq_sum x y, ← real_inner_self_eq_norm_sq x,
      ← real_inner_self_eq_norm_sq y, Statlib.HighDim.Vocabulary.inner_eq_sum x x,
      Statlib.HighDim.Vocabulary.inner_eq_sum y y]
    simp only [Fin.sum_univ_two]
    ring
  have hDadd : ∀ (x y : Plane) (i : Fin 2), (x + y).ofLp i = x.ofLp i + y.ofLp i := by
    intro x y i; rfl
  have hDneg : ∀ (x : Plane) (i : Fin 2), (-x).ofLp i = -(x.ofLp i) := by
    intro x i; rfl
  have hDsub : ∀ (x y : Plane) (i : Fin 2), (x - y).ofLp i = x.ofLp i - y.ofLp i := by
    intro x y i; rfl
  have hDsmul : ∀ (a : ℝ) (x : Plane) (i : Fin 2), (a • x).ofLp i = a * x.ofLp i := by
    intro a x i; rfl
  by_cases hb : b = 0
  · rw [hb]; simp
  by_cases hc : c = 0
  · exfalso
    have hk' : k = α • b := by rw [hk, hc]; simp
    have hbpos : (0 : ℝ) < ‖b‖ := norm_pos_iff.mpr hb
    have hnum : inner ℝ b k = α * ‖b‖ ^ 2 := by
      rw [hk', inner_smul_right, real_inner_self_eq_norm_sq]
    have hden2 : ‖b‖ * ‖k‖ = α * ‖b‖ ^ 2 := by
      rw [hk', norm_smul, Real.norm_of_nonneg (le_of_lt halpha)]
      ring
    have hrhs : inner ℝ b k / (‖b‖ * ‖k‖) = 1 := by
      rw [hnum, hden2]
      exact div_self (ne_of_gt (mul_pos halpha (pow_pos hbpos 2)))
    have h := hcos
    rw [hc] at h
    simp only [neg_zero, sub_zero, inner_zero_left, norm_zero, zero_mul, zero_div] at h
    rw [hrhs] at h
    exact absurd h (by norm_num)
  by_cases hkc : k = c
  · exfalso
    have h := hcos
    rw [hkc] at h
    simp only [sub_self, norm_zero, mul_zero, zero_div, inner_zero_right] at h
    have hden : ‖b‖ * ‖c‖ ≠ 0 :=
      mul_ne_zero (norm_ne_zero_iff.mpr hb) (norm_ne_zero_iff.mpr hc)
    have hbc0 : inner ℝ b c = 0 :=
      (div_eq_zero_iff.mp h.symm).resolve_right hden
    have hrel : α • b = (1 - γ) • c := by
      have h2 : c = α • b + γ • c := by simpa only [hkc] using hk
      calc α • b = (α • b + γ • c) - γ • c := by rw [add_sub_cancel_right]
        _ = c - γ • c := by rw [← h2]
        _ = (1 - γ) • c := by rw [sub_smul, one_smul]
    have hinner : inner ℝ b (α • b) = inner ℝ b ((1 - γ) • c) := by rw [hrel]
    simp only [inner_smul_right, hbc0, mul_zero, real_inner_self_eq_norm_sq] at hinner
    exact absurd hinner (ne_of_gt (mul_pos halpha (pow_pos (norm_pos_iff.mpr hb) 2)))
  by_cases hk0 : k = 0
  · exfalso
    have h := hcos
    rw [hk0] at h
    simp only [zero_sub, norm_neg, real_inner_self_eq_norm_sq, norm_zero, mul_zero, zero_div,
      inner_zero_right] at h
    have hcpos : (0 : ℝ) < ‖c‖ := norm_pos_iff.mpr hc
    have h1 : ‖c‖ ^ 2 / (‖c‖ * ‖c‖) = 1 := by
      rw [sq]
      exact div_self (mul_ne_zero (ne_of_gt hcpos) (ne_of_gt hcpos))
    rw [h1] at h
    exact absurd h (by norm_num)
  have hCD : ‖c‖ * ‖k-c‖ ≠ 0 :=
    mul_ne_zero (norm_ne_zero_iff.mpr hc) (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hkc))
  have hBK : ‖b‖ * ‖k‖ ≠ 0 :=
    mul_ne_zero (norm_ne_zero_iff.mpr hb) (norm_ne_zero_iff.mpr hk0)
  have hcross : inner ℝ (-c) (k-c) * (‖b‖ * ‖k‖) = inner ℝ b k * (‖c‖ * ‖k-c‖) := by
    have h := hcos
    rw [div_eq_div_iff hCD hBK] at h
    exact h
  have hdetbc : b.ofLp 0 * c.ofLp 1 - b.ofLp 1 * c.ofLp 0 ≠ 0 := by
    intro hD0
    have hbc : ∃ lam : ℝ, b = lam • c := by
      by_cases h1 : c.ofLp 1 = 0
      · have hc0 : c.ofLp 0 ≠ 0 := by
          intro h0
          exact hc (WithLp.ofLp_injective 2 (by
            funext i
            fin_cases i
            · simpa using h0
            · simpa using h1))
        have hx1 : b.ofLp 1 = 0 := by
          have hmul : b.ofLp 1 * c.ofLp 0 = 0 := by
            have h := hD0
            rw [h1, mul_zero, zero_sub, neg_eq_zero] at h
            exact h
          exact (mul_eq_zero.mp hmul).resolve_right hc0
        refine ⟨b.ofLp 0 / c.ofLp 0, ?_⟩
        apply WithLp.ofLp_injective 2
        funext i
        fin_cases i
        · rw [hDsmul]
          show b.ofLp 0 = (b.ofLp 0 / c.ofLp 0) * c.ofLp 0
          rw [div_mul_cancel₀ (b.ofLp 0) hc0]
        · rw [hDsmul]
          show b.ofLp 1 = (b.ofLp 0 / c.ofLp 0) * c.ofLp 1
          rw [h1, hx1]
          ring
      · have hx0 : b.ofLp 0 = (b.ofLp 1 * c.ofLp 0) / c.ofLp 1 :=
          (eq_div_iff h1).mpr (by linarith [hD0])
        refine ⟨b.ofLp 1 / c.ofLp 1, ?_⟩
        apply WithLp.ofLp_injective 2
        funext i
        fin_cases i
        · rw [hDsmul]
          show b.ofLp 0 = (b.ofLp 1 / c.ofLp 1) * c.ofLp 0
          rw [hx0]
          ring
        · rw [hDsmul]
          show b.ofLp 1 = (b.ofLp 1 / c.ofLp 1) * c.ofLp 1
          rw [div_mul_cancel₀ (b.ofLp 1) h1]
    obtain ⟨lam, hbc⟩ := hbc
    have hmu : k = (α * lam + γ) • c := by
      rw [hk, hbc]
      module
    have hinner_kk : inner ℝ k k = (α * lam + γ) ^ 2 * inner ℝ c c := by
      rw [hmu, real_inner_smul_left, real_inner_smul_right]
      ring
    have hinner_ku : inner ℝ k u = (α * lam + γ) * inner ℝ c u := by
      rw [hmu, real_inner_smul_left]
    have hkk' : inner ℝ k k = ‖k‖ ^ 2 := real_inner_self_eq_norm_sq k
    have hcc' : inner ℝ c c = ‖c‖ ^ 2 := real_inner_self_eq_norm_sq c
    have hku2 : 2 * inner ℝ k u = inner ℝ k k := by rw [hku, hkk']; ring
    have hcu2 : 2 * inner ℝ c u = inner ℝ c c := by rw [hcu, hcc']; ring
    have hikAC : inner ℝ k k = (α * lam + γ) * inner ℝ c c := by
      rw [← hku2, hinner_ku, ← hcu2]
      ring
    have key : (α * lam + γ) * inner ℝ c c = (α * lam + γ) ^ 2 * inner ℝ c c := by
      rw [← hikAC, hinner_kk]
    have hccne : inner ℝ c c ≠ 0 := by
      rw [hcc']; exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hc)
    have hmu_eq : (α * lam + γ) = (α * lam + γ) ^ 2 := by
      have h : inner ℝ c c * ((α * lam + γ) - (α * lam + γ) ^ 2) = 0 := by
        linear_combination key
      have h' := (mul_eq_zero.mp h).resolve_left hccne
      linarith
    have hcases : (α * lam + γ) = 0 ∨ (α * lam + γ) = 1 := by
      have h : (α * lam + γ) * (1 - (α * lam + γ)) = 0 := by linear_combination hmu_eq
      rcases mul_eq_zero.mp h with h0 | h1
      · exact Or.inl h0
      · exact Or.inr (by linarith)
    rcases hcases with h0 | h1
    · exact hk0 (by rw [hmu, h0, zero_smul])
    · exact hkc (by rw [hmu, h1, one_smul])
  have hkey : ‖k‖ ^ 2 = γ * ‖c‖ ^ 2 := by
    set DBC := b.ofLp 0 * c.ofLp 1 - b.ofLp 1 * c.ofLp 0 with hDBCd
    set A := inner ℝ (-c) (k - c) with hAdef
    set B := inner ℝ b k with hBdef
    set X := ‖b‖ * ‖k‖ with hX
    set Y := ‖c‖ * ‖k - c‖ with hY
    set D1 := (-c).ofLp 0 * (k - c).ofLp 1 - (-c).ofLp 1 * (k - c).ofLp 0 with hD1def
    set D2 := b.ofLp 0 * k.ofLp 1 - b.ofLp 1 * k.ofLp 0 with hD2def
    have hD1 : D1 = α * DBC := by
      rw [hD1def, hDBCd, hk]
      simp only [hDadd, hDsub, hDneg, hDsmul]
      ring
    have hD2 : D2 = γ * DBC := by
      rw [hD2def, hDBCd, hk]
      simp only [hDadd, hDsmul]
      ring
    have hcrossX : A * X = B * Y := by
      rw [hAdef, hBdef, hX, hY]; exact hcross
    have hX2 : X ^ 2 = ‖b‖ ^ 2 * ‖k‖ ^ 2 := by rw [hX, mul_pow]
    have hY2 : Y ^ 2 = ‖c‖ ^ 2 * ‖k - c‖ ^ 2 := by rw [hY, mul_pow]
    have hl1 := hLagrange (-c) (k - c)
    have hl2 := hLagrange b k
    rw [norm_neg] at hl1
    have hl1Y : A ^ 2 + D1 ^ 2 = Y ^ 2 := by
      rw [hAdef, hD1def, hY2]; exact hl1
    have hl2X : B ^ 2 + D2 ^ 2 = X ^ 2 := by
      rw [hBdef, hD2def, hX2]; exact hl2
    have hXpos : 0 < X := by
      rw [hX]
      exact mul_pos (norm_pos_iff.mpr hb) (norm_pos_iff.mpr hk0)
    have hAS : A ^ 2 * X ^ 2 = B ^ 2 * Y ^ 2 := by
      linear_combination (A * X + B * Y) * hcrossX
    have hD1X : D1 ^ 2 * X ^ 2 = D2 ^ 2 * Y ^ 2 := by
      linear_combination (X ^ 2) * hl1Y - (Y ^ 2) * hl2X - hAS
    have hrel : (α ^ 2 * X ^ 2 - γ ^ 2 * Y ^ 2) * DBC ^ 2 = 0 := by
      have h := hD1X
      rw [hD1, hD2] at h
      linear_combination h
    have hne : DBC ≠ 0 := by rw [hDBCd]; exact hdetbc
    have hsq : α ^ 2 * X ^ 2 = γ ^ 2 * Y ^ 2 :=
      sub_eq_zero.mp ((mul_eq_zero.mp hrel).resolve_right (pow_ne_zero 2 hne))
    have hYpos : 0 < Y := by
      rw [hY]
      exact mul_pos (norm_pos_iff.mpr hc) (norm_pos_iff.mpr (sub_ne_zero.mpr hkc))
    have hXY : α * X = γ * Y := by
      have hprod : (α * X - γ * Y) * (α * X + γ * Y) = 0 := by
        linear_combination hsq
      have hsum : α * X + γ * Y ≠ 0 := by
        have h1 : 0 < α * X := mul_pos halpha hXpos
        have h2 : 0 < γ * Y := mul_pos hgamma hYpos
        exact ne_of_gt (by linarith)
      exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hsum)
    have hgammaA : γ * A = α * B := by
      have h1 : (γ * A - α * B) * X = 0 := by
        linear_combination γ * hcrossX - B * hXY
      exact sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right (ne_of_gt hXpos))
    have hmain : inner ℝ k k = γ * inner ℝ c c := by
      rw [hAdef, hBdef] at hgammaA
      have hA : inner ℝ (-c) (k - c) = -(inner ℝ c k) + inner ℝ c c := by
        rw [inner_neg_left, inner_sub_right]; ring
      rw [hA] at hgammaA
      linear_combination hkk - hgammaA - γ * hck - α * hbk
    rw [← real_inner_self_eq_norm_sq k, ← real_inner_self_eq_norm_sq c]
    exact hmain
  have hbuk : inner ℝ k u = α * inner ℝ b u + γ * inner ℝ c u := by
    rw [hk]
    simp only [inner_add_left, inner_smul_left]
    simp
  have hb : inner ℝ b u = 0 := by
    nlinarith [hbuk, hku, hcu, hkey, halpha]
  exact hb
  /- @proof-region region.target-node.session.07c0687ff923ccb3 end -/
