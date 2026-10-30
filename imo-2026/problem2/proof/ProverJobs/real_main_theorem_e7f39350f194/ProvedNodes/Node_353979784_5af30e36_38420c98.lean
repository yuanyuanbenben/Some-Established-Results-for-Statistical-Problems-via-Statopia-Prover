import ProverJobs.real_main_theorem_e7f39350f194.Vocabulary
import ProverJobs.real_main_theorem_e7f39350f194.Base
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_3431605529_2a745110_37ebd9aa
import ProverJobs.real_main_theorem_e7f39350f194.ProvedNodes.Node_981975689_c1054012_46ac252e
open EuclideanGeometry

open EuclideanGeometry

set_option autoImplicit false in
theorem statopia_math_node_353979784_5af30e36 : ∀ (P Q R S : Plane)
    (hPQR : ¬ Collinear ℝ ({P, Q, R} : Set Plane))
    (hAngle :
      (0 < ((Q - P) 0 * (R - P) 1 - (Q - P) 1 * (R - P) 0) *
              ((Q - P) 0 * (S - P) 1 - (Q - P) 1 * (S - P) 0) ∧
          ∠ P R Q = ∠ P S Q) ∨
        (((Q - P) 0 * (R - P) 1 - (Q - P) 1 * (R - P) 0) *
            ((Q - P) 0 * (S - P) 1 - (Q - P) 1 * (S - P) 0) < 0 ∧
          ∠ P R Q + ∠ P S Q = (Real.pi : Real.Angle))),

    ∃ (U : Plane) (r2 : ℝ),
      ‖P - U‖ ^ 2 - r2 = 0 ∧ ‖Q - U‖ ^ 2 - r2 = 0 ∧
        ‖R - U‖ ^ 2 - r2 = 0 ∧ ‖S - U‖ ^ 2 - r2 = 0 := by
  /- @proof-region region.target-node.session.525e239c6e58d611 begin -/
  intro P Q R S hPQR hAngle
  have key_lemma : ∀ (K1 K2 L1 L2 c1 c2 d1 d2 : ℝ),
      0 < L1 → 0 < L2 → K1 ^ 2 + c1 ^ 2 = L1 ^ 2 → K2 ^ 2 + c2 ^ 2 = L2 ^ 2 →
      c1 = L1 * d1 → c2 = L2 * d2 →
      ((d2 = d1 ∧ 0 < K1 * K2) ∨ (d2 = -d1 ∧ K1 * K2 < 0)) →
      K1 * c2 - K2 * c1 = 0 := by
    intro K1 K2 L1 L2 c1 c2 d1 d2 hK1 hK2 hsq1 hsq2 hc1 hc2 hcc
    have hsq : (K1 * L2) ^ 2 = (K2 * L1) ^ 2 := by
      have e1 : K1 ^ 2 = L1 ^ 2 - c1 ^ 2 := by linarith
      have e2 : K2 ^ 2 = L2 ^ 2 - c2 ^ 2 := by linarith
      rw [mul_pow, mul_pow, e1, e2, hc1, hc2]
      rcases hcc with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> ring
    have hpr : (K1 * L2) * (K2 * L1) = (K1 * K2) * (L1 * L2) := by ring
    have hLL : 0 < L1 * L2 := mul_pos hK1 hK2
    rcases hcc with ⟨h, hsg⟩ | ⟨h, hsg⟩
    · rw [hc1, hc2]
      have hpos : 0 < (K1 * L2) * (K2 * L1) := by
        rw [hpr]; exact mul_pos hsg hLL
      have heq : K1 * L2 = K2 * L1 := by
        rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hsq with hh | hh
        · exact hh
        · exfalso
          rw [hh] at hpos
          nlinarith [sq_nonneg (K2 * L1)]
      have hfin : K1 * (L2 * d1) - K2 * (L1 * d1) = (K1 * L2 - K2 * L1) * d1 := by ring
      rw [h, hfin, heq]
      ring
    · rw [hc1, hc2]
      have hneg : (K1 * L2) * (K2 * L1) < 0 := by
        rw [hpr]; exact mul_neg_of_neg_of_pos hsg hLL
      have heq : K1 * L2 = -(K2 * L1) := by
        rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hsq with hh | hh
        · exfalso
          rw [hh] at hneg
          nlinarith [sq_nonneg (K2 * L1)]
        · exact hh
      have hfin : K1 * (L2 * -d1) - K2 * (L1 * d1) = (K1 * L2 + K2 * L1) * -d1 := by ring
      rw [h, hfin, heq]
      ring
  have key2 : ∀ (s1 s2 T2 A B C P1 Pb Q1 Aw Bw : ℝ),
      s1 ≠ 0 → 2 * Aw = A → 2 * Bw = B →
      T2 * Aw + s2 * Bw = s1 * Q1 → T2 * A + s2 * Pb = s1 * P1 →
      s1 * (C - P1) - s2 * (B - Pb) = 0 →
      C - 2 * Q1 = 0 := by
    intro s1 s2 T2 A B C P1 Pb Q1 Aw Bw hs hAw hBw h1 h2 h3
    have e1a : T2 * A = 2 * (T2 * Aw) := by rw [← hAw]; ring
    have e1b : s2 * B = 2 * (s2 * Bw) := by rw [← hBw]; ring
    have e1 : T2 * A + s2 * B = 2 * (s1 * Q1) := by linarith
    have e2 : s1 * C = 2 * (s1 * Q1) := by linarith
    have hmain : s1 * (C - 2 * Q1) = 0 := by linarith
    rcases mul_eq_zero.mp hmain with h | h
    · exact absurd h hs
    · exact h
  obtain ⟨U, r, hUP, hUQ, hUR⟩ := statopia_math_node_981975689_c1054012 P Q R hPQR 0 0
  refine ⟨U, r, hUP, hUQ, hUR, ?_⟩
  have hr : r = ‖U - P‖ ^ 2 := by
    have h := hUP
    rw [show P - U = -(U - P) by abel, norm_neg] at h
    linarith
  have hcosR : Real.cos (∠ P R Q) = inner ℝ (P - R) (Q - R) / (‖P - R‖ * ‖Q - R‖) := by
    rw [EuclideanGeometry.angle, InnerProductGeometry.cos_angle]
    simp
  have hcosS : Real.cos (∠ P S Q) = inner ℝ (P - S) (Q - S) / (‖P - S‖ * ‖Q - S‖) := by
    rw [EuclideanGeometry.angle, InnerProductGeometry.cos_angle]
    simp
  have hE1 : (P - R) 0 * (Q - R) 1 - (P - R) 1 * (Q - R) 0
      = (Q - P) 0 * (R - P) 1 - (Q - P) 1 * (R - P) 0 := by
    simp only [WithLp.ofLp_sub, Pi.sub_apply]
    ring
  have hE2 : (P - S) 0 * (Q - S) 1 - (P - S) 1 * (Q - S) 0
      = (Q - P) 0 * (S - P) 1 - (Q - P) 1 * (S - P) 0 := by
    simp only [WithLp.ofLp_sub, Pi.sub_apply]
    ring
  have hLag1 : ((P - R) 0 * (Q - R) 1 - (P - R) 1 * (Q - R) 0) ^ 2
      + (inner ℝ (P - R) (Q - R)) ^ 2 = ‖P - R‖ ^ 2 * ‖Q - R‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq (P - R), ← real_inner_self_eq_norm_sq (Q - R)]
    simp only [Statlib.HighDim.Vocabulary.inner_eq_sum, Fin.sum_univ_two, WithLp.ofLp_sub,
      Pi.sub_apply]
    ring
  have hLag2 : ((P - S) 0 * (Q - S) 1 - (P - S) 1 * (Q - S) 0) ^ 2
      + (inner ℝ (P - S) (Q - S)) ^ 2 = ‖P - S‖ ^ 2 * ‖Q - S‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq (P - S), ← real_inner_self_eq_norm_sq (Q - S)]
    simp only [Statlib.HighDim.Vocabulary.inner_eq_sum, Fin.sum_univ_two, WithLp.ofLp_sub,
      Pi.sub_apply]
    ring
  have hCr1 : ((S - P) 0 * (R - P) 1 - (S - P) 1 * (R - P) 0) * inner ℝ (Q - P) (U - P)
      + ((Q - P) 0 * (S - P) 1 - (Q - P) 1 * (S - P) 0) * inner ℝ (R - P) (U - P)
      = ((Q - P) 0 * (R - P) 1 - (Q - P) 1 * (R - P) 0) * inner ℝ (S - P) (U - P) := by
    simp only [Statlib.HighDim.Vocabulary.inner_eq_sum, Fin.sum_univ_two, WithLp.ofLp_sub,
      Pi.sub_apply]
    ring
  have hCr2 : ((S - P) 0 * (R - P) 1 - (S - P) 1 * (R - P) 0) * inner ℝ (Q - P) (Q - P)
      + ((Q - P) 0 * (S - P) 1 - (Q - P) 1 * (S - P) 0) * inner ℝ (R - P) (Q - P)
      = ((Q - P) 0 * (R - P) 1 - (Q - P) 1 * (R - P) 0) * inner ℝ (S - P) (Q - P) := by
    simp only [Statlib.HighDim.Vocabulary.inner_eq_sum, Fin.sum_univ_two, WithLp.ofLp_sub,
      Pi.sub_apply]
    ring
  have hwa : 2 * inner ℝ (Q - P) (U - P) = ‖Q - P‖ ^ 2 := by
    have h := hUQ
    rw [show Q - U = (Q - P) - (U - P) by abel, norm_sub_sq_real, hr] at h
    linarith
  have hwb : 2 * inner ℝ (R - P) (U - P) = ‖R - P‖ ^ 2 := by
    have h := hUR
    rw [show R - U = (R - P) - (U - P) by abel, norm_sub_sq_real, hr] at h
    linarith
  have hQ0 : ∀ Z : Plane, ‖Z - U‖ ^ 2 - r = ‖Z - P‖ ^ 2 - 2 * inner ℝ (Z - P) (U - P) := by
    intro Z
    rw [show Z - U = (Z - P) - (U - P) by abel, norm_sub_sq_real, hr]
    ring
  have hsgnne : ((Q - P) 0 * (R - P) 1 - (Q - P) 1 * (R - P) 0) *
      ((Q - P) 0 * (S - P) 1 - (Q - P) 1 * (S - P) 0) ≠ 0 := by
    rcases hAngle with ⟨h, _⟩ | ⟨h, _⟩
    · exact ne_of_gt h
    · exact ne_of_lt h
  have hsgnR : (Q - P) 0 * (R - P) 1 - (Q - P) 1 * (R - P) 0 ≠ 0 :=
    fun h0 => hsgnne (by rw [h0, zero_mul])
  have hsgnS : (Q - P) 0 * (S - P) 1 - (Q - P) 1 * (S - P) 0 ≠ 0 :=
    fun h0 => hsgnne (by rw [h0, mul_zero])
  have hKRne : (P - R) 0 * (Q - R) 1 - (P - R) 1 * (Q - R) 0 ≠ 0 := by
    rw [hE1]; exact hsgnR
  have hKSne : (P - S) 0 * (Q - S) 1 - (P - S) 1 * (Q - S) 0 ≠ 0 := by
    rw [hE2]; exact hsgnS
  have hnormR2 : ‖P - R‖ ^ 2 * ‖Q - R‖ ^ 2 ≠ 0 := by
    have hle : ((P - R) 0 * (Q - R) 1 - (P - R) 1 * (Q - R) 0) ^ 2
        ≤ ‖P - R‖ ^ 2 * ‖Q - R‖ ^ 2 := by
      rw [← hLag1]
      exact le_add_of_nonneg_right (sq_nonneg _)
    exact ne_of_gt (lt_of_lt_of_le (sq_pos_of_ne_zero hKRne) hle)
  have hnormS2 : ‖P - S‖ ^ 2 * ‖Q - S‖ ^ 2 ≠ 0 := by
    have hle : ((P - S) 0 * (Q - S) 1 - (P - S) 1 * (Q - S) 0) ^ 2
        ≤ ‖P - S‖ ^ 2 * ‖Q - S‖ ^ 2 := by
      rw [← hLag2]
      exact le_add_of_nonneg_right (sq_nonneg _)
    exact ne_of_gt (lt_of_lt_of_le (sq_pos_of_ne_zero hKSne) hle)
  have hunR : ‖P - R‖ ≠ 0 := fun h0 => hnormR2 (by rw [h0]; ring)
  have hunQR : ‖Q - R‖ ≠ 0 := fun h0 => hnormR2 (by rw [h0]; ring)
  have hunS : ‖P - S‖ ≠ 0 := fun h0 => hnormS2 (by rw [h0]; ring)
  have hunQS : ‖Q - S‖ ≠ 0 := fun h0 => hnormS2 (by rw [h0]; ring)
  have hL1 : 0 < ‖P - R‖ * ‖Q - R‖ :=
    mul_pos (lt_of_le_of_ne (norm_nonneg _) hunR.symm)
      (lt_of_le_of_ne (norm_nonneg _) hunQR.symm)
  have hL2 : 0 < ‖P - S‖ * ‖Q - S‖ :=
    mul_pos (lt_of_le_of_ne (norm_nonneg _) hunS.symm)
      (lt_of_le_of_ne (norm_nonneg _) hunQS.symm)
  have hLRne : ‖P - R‖ * ‖Q - R‖ ≠ 0 := mul_ne_zero hunR hunQR
  have hLSne : ‖P - S‖ * ‖Q - S‖ ≠ 0 := mul_ne_zero hunS hunQS
  have hsgnRK : (Q - P) 0 * (R - P) 1 - (Q - P) 1 * (R - P) 0
      = (P - R) 0 * (Q - R) 1 - (P - R) 1 * (Q - R) 0 := hE1.symm
  have hsgnSK : (Q - P) 0 * (S - P) 1 - (Q - P) 1 * (S - P) 0
      = (P - S) 0 * (Q - S) 1 - (P - S) 1 * (Q - S) 0 := hE2.symm
  have hbS : ‖S - P‖ ^ 2 - inner ℝ (Q - P) (S - P) = inner ℝ (P - S) (Q - S) := by
    rw [← real_inner_self_eq_norm_sq (S - P)]
    simp only [Statlib.HighDim.Vocabulary.inner_eq_sum, Fin.sum_univ_two, WithLp.ofLp_sub,
      Pi.sub_apply]
    ring
  have hbR : ‖R - P‖ ^ 2 - inner ℝ (Q - P) (R - P) = inner ℝ (P - R) (Q - R) := by
    rw [← real_inner_self_eq_norm_sq (R - P)]
    simp only [Statlib.HighDim.Vocabulary.inner_eq_sum, Fin.sum_univ_two, WithLp.ofLp_sub,
      Pi.sub_apply]
    ring
  have hs1 : ((P - R) 0 * (Q - R) 1 - (P - R) 1 * (Q - R) 0) ^ 2
      + (inner ℝ (P - R) (Q - R)) ^ 2 = (‖P - R‖ * ‖Q - R‖) ^ 2 := by
    rw [mul_pow]; exact hLag1
  have hs2 : ((P - S) 0 * (Q - S) 1 - (P - S) 1 * (Q - S) 0) ^ 2
      + (inner ℝ (P - S) (Q - S)) ^ 2 = (‖P - S‖ * ‖Q - S‖) ^ 2 := by
    rw [mul_pow]; exact hLag2
  have hcdR : inner ℝ (P - R) (Q - R) = (‖P - R‖ * ‖Q - R‖) * Real.cos (∠ P R Q) := by
    rw [← (eq_div_iff hLRne).mp hcosR]
    ring
  have hcdS : inner ℝ (P - S) (Q - S) = (‖P - S‖ * ‖Q - S‖) * Real.cos (∠ P S Q) := by
    rw [← (eq_div_iff hLSne).mp hcosS]
    ring
  have auxcos : ∀ a : ℝ, (↑a : Real.Angle).cos = Real.cos a := fun a =>
    Real.Angle.cos_eq_real_cos_iff_eq_or_eq_neg.mpr (Or.inl rfl)
  have auxnegcos : ∀ a : ℝ, (-(↑a : Real.Angle)).cos = Real.cos a := fun a =>
    Real.Angle.cos_eq_real_cos_iff_eq_or_eq_neg.mpr (Or.inr rfl)
  have hcase : (Real.cos (∠ P S Q) = Real.cos (∠ P R Q) ∧
        0 < ((P - R) 0 * (Q - R) 1 - (P - R) 1 * (Q - R) 0) *
          ((P - S) 0 * (Q - S) 1 - (P - S) 1 * (Q - S) 0)) ∨
      (Real.cos (∠ P S Q) = -Real.cos (∠ P R Q) ∧
        ((P - R) 0 * (Q - R) 1 - (P - R) 1 * (Q - R) 0) *
          ((P - S) 0 * (Q - S) 1 - (P - S) 1 * (Q - S) 0) < 0) := by
    have hprod : ((P - R) 0 * (Q - R) 1 - (P - R) 1 * (Q - R) 0) *
        ((P - S) 0 * (Q - S) 1 - (P - S) 1 * (Q - S) 0)
        = ((Q - P) 0 * (R - P) 1 - (Q - P) 1 * (R - P) 0) *
          ((Q - P) 0 * (S - P) 1 - (Q - P) 1 * (S - P) 0) := by
      rw [← hsgnRK, ← hsgnSK]
    rcases hAngle with ⟨hsg, hang⟩ | ⟨hsg, hang⟩
    · refine Or.inl ⟨?_, ?_⟩
      · exact congrArg Real.cos hang.symm
      · rw [hprod]; exact hsg
    · refine Or.inr ⟨?_, ?_⟩
      · have h2 : (↑(∠ P S Q) : Real.Angle) = ↑Real.pi - ↑(∠ P R Q) := by
          rw [eq_sub_iff_add_eq, add_comm]
          exact hang
        have h3 : (↑(∠ P R Q) : Real.Angle) - ↑Real.pi = -(↑(∠ P S Q) : Real.Angle) := by
          rw [h2]
          abel
        have h4 : ((↑(∠ P R Q) : Real.Angle) - ↑Real.pi).cos = -Real.cos (∠ P R Q) := by
          rw [Real.Angle.cos_sub_pi (↑(∠ P R Q) : Real.Angle), auxcos (∠ P R Q)]
        rw [h3, auxnegcos (∠ P S Q)] at h4
        exact h4
      · rw [hprod]; exact hsg
  have hDab : ((Q - P) 0 * (R - P) 1 - (Q - P) 1 * (R - P) 0) *
        (‖S - P‖ ^ 2 - inner ℝ (Q - P) (S - P))
      - ((Q - P) 0 * (S - P) 1 - (Q - P) 1 * (S - P) 0) *
        (‖R - P‖ ^ 2 - inner ℝ (Q - P) (R - P)) = 0 := by
    rw [hsgnRK, hbS, hsgnSK, hbR]
    exact key_lemma ((P - R) 0 * (Q - R) 1 - (P - R) 1 * (Q - R) 0)
      ((P - S) 0 * (Q - S) 1 - (P - S) 1 * (Q - S) 0)
      (‖P - R‖ * ‖Q - R‖) (‖P - S‖ * ‖Q - S‖)
      (inner ℝ (P - R) (Q - R)) (inner ℝ (P - S) (Q - S))
      (Real.cos (∠ P R Q)) (Real.cos (∠ P S Q)) hL1 hL2 hs1 hs2 hcdR hcdS hcase
  have hfinal : ‖S - P‖ ^ 2 - 2 * inner ℝ (S - P) (U - P) = 0 := by
    have hCr2' : ((S - P) 0 * (R - P) 1 - (S - P) 1 * (R - P) 0) * ‖Q - P‖ ^ 2
        + ((Q - P) 0 * (S - P) 1 - (Q - P) 1 * (S - P) 0) * inner ℝ (Q - P) (R - P)
        = ((Q - P) 0 * (R - P) 1 - (Q - P) 1 * (R - P) 0) * inner ℝ (Q - P) (S - P) := by
      rw [← real_inner_self_eq_norm_sq (Q - P)]
      simp only [Statlib.HighDim.Vocabulary.inner_eq_sum, Fin.sum_univ_two, WithLp.ofLp_sub,
        Pi.sub_apply]
      ring
    exact key2 ((Q - P) 0 * (R - P) 1 - (Q - P) 1 * (R - P) 0)
      ((Q - P) 0 * (S - P) 1 - (Q - P) 1 * (S - P) 0)
      ((S - P) 0 * (R - P) 1 - (S - P) 1 * (R - P) 0)
      (‖Q - P‖ ^ 2) (‖R - P‖ ^ 2) (‖S - P‖ ^ 2)
      (inner ℝ (Q - P) (S - P)) (inner ℝ (Q - P) (R - P)) (inner ℝ (S - P) (U - P))
      (inner ℝ (Q - P) (U - P)) (inner ℝ (R - P) (U - P)) hsgnR hwa hwb hCr1 hCr2' hDab
  rw [hQ0 S]
  exact hfinal
  /- @proof-region region.target-node.session.525e239c6e58d611 end -/
