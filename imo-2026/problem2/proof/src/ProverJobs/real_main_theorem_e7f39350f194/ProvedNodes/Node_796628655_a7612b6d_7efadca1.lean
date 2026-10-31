import ProverJobs.real_main_theorem_e7f39350f194.Vocabulary
import ProverJobs.real_main_theorem_e7f39350f194.Base

open EuclideanGeometry

open EuclideanGeometry

set_option autoImplicit false in
theorem statopia_math_node_796628655_a7612b6d : ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (U V : E) (s t : ℝ)
    (hs : 0 < s) (ht : 0 < t)
    (hG : ‖U‖ ^ 2 * ‖V‖ ^ 2 - (inner ℝ U V) ^ 2 ≠ 0)
    (hangle : Real.arccos (inner ℝ (-U) (s • V - U) / (‖-U‖ * ‖s • V - U‖))
      = Real.arccos (inner ℝ (t • U - V) (-V) / (‖t • U - V‖ * ‖-V‖))),
    s * ‖V‖ ^ 2 = t * ‖U‖ ^ 2 := by
  /- @proof-region region.target-node.session.af2c5472e5573d3f begin -/
  intro E iN iI U V s t hs ht hG hangle
  have hbound : ∀ (x y : E), |inner ℝ x y / (‖x‖ * ‖y‖)| ≤ 1 := by
    intro x y
    have hle : |inner ℝ x y| ≤ ‖x‖ * ‖y‖ := abs_real_inner_le_norm x y
    have hn : (0 : ℝ) ≤ ‖x‖ * ‖y‖ := mul_nonneg (norm_nonneg x) (norm_nonneg y)
    rcases eq_or_lt_of_le hn with h0 | hpos
    · rw [← h0, div_zero, abs_zero]
      norm_num
    · rw [abs_div, abs_of_nonneg hn, div_eq_mul_inv]
      have h2 : |inner ℝ x y| * (‖x‖ * ‖y‖)⁻¹ ≤ (‖x‖ * ‖y‖) * (‖x‖ * ‖y‖)⁻¹ :=
        mul_le_mul_of_nonneg_right hle (inv_nonneg.mpr hn)
      have h3 : (‖x‖ * ‖y‖) * (‖x‖ * ‖y‖)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hpos)
      linarith
  have hcos := congrArg Real.cos hangle
  rw [Real.cos_arccos (abs_le.mp (hbound (-U) (s • V - U))).1
        (abs_le.mp (hbound (-U) (s • V - U))).2,
      Real.cos_arccos (abs_le.mp (hbound (t • U - V) (-V))).1
        (abs_le.mp (hbound (t • U - V) (-V))).2] at hcos
  simp only [norm_neg] at hcos
  set c2 : ℝ := ‖U‖ ^ 2 with hc2
  set b2 : ℝ := ‖V‖ ^ 2 with hb2
  set dd : ℝ := inner ℝ U V with hdd
  set A1 : ℝ := inner ℝ (-U) (s • V - U) with hA1def
  set N1 : ℝ := ‖s • V - U‖ with hN1def
  set B1 : ℝ := inner ℝ (t • U - V) (-V) with hB1def
  set N2 : ℝ := ‖t • U - V‖ with hN2def
  set G : ℝ := c2 * b2 - dd ^ 2 with hGdef
  have hN1nn : 0 ≤ N1 := by rw [hN1def]; exact norm_nonneg _
  have hN2nn : 0 ≤ N2 := by rw [hN2def]; exact norm_nonneg _
  have hA1e : A1 = c2 - s * dd := by
    rw [hA1def, hc2, hdd, inner_neg_left, inner_sub_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    ring
  have hB1e : B1 = b2 - t * dd := by
    rw [hB1def, hb2, hdd, inner_neg_right, inner_sub_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
    ring
  have hN1e : N1 ^ 2 = c2 - 2 * s * dd + s ^ 2 * b2 := by
    rw [hN1def, hc2, hb2, hdd, norm_sub_sq_real]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hs), mul_pow]
    rw [real_inner_smul_left, real_inner_comm V U]
    ring
  have hN2e : N2 ^ 2 = b2 - 2 * t * dd + t ^ 2 * c2 := by
    rw [hN2def, hc2, hb2, hdd, norm_sub_sq_real]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt ht), mul_pow]
    rw [real_inner_smul_left]
    ring
  have hUne : U ≠ 0 := by
    intro hUz
    exact hG (by rw [hGdef, hc2, hb2, hdd, hUz]; simp)
  have hVne : V ≠ 0 := by
    intro hVz
    exact hG (by rw [hGdef, hc2, hb2, hdd, hVz]; simp)
  have hsU : ‖U‖ ≠ 0 := norm_ne_zero_iff.mpr hUne
  have hsV : ‖V‖ ≠ 0 := norm_ne_zero_iff.mpr hVne
  have hN1ne : N1 ≠ 0 := by
    intro h
    rw [hN1def] at h
    have hsVU : s • V = U := sub_eq_zero.mp (norm_eq_zero.mp h)
    exact hG (by
      rw [hGdef, hc2, hb2, hdd, ← hsVU, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (le_of_lt hs), mul_pow, real_inner_smul_left, real_inner_self_eq_norm_sq]
      ring)
  have hN2ne : N2 ≠ 0 := by
    intro h
    rw [hN2def] at h
    have htUV : t • U = V := sub_eq_zero.mp (norm_eq_zero.mp h)
    exact hG (by
      rw [hGdef, hc2, hb2, hdd, ← htUV, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (le_of_lt ht), mul_pow, real_inner_smul_right, real_inner_self_eq_norm_sq]
      ring)
  have hN1pos : 0 < N1 := lt_of_le_of_ne hN1nn (Ne.symm hN1ne)
  have hN2pos : 0 < N2 := lt_of_le_of_ne hN2nn (Ne.symm hN2ne)
  have hu : ‖U‖ * N1 ≠ 0 := mul_ne_zero hsU hN1ne
  have hv : ‖V‖ * N2 ≠ 0 := mul_ne_zero hsV hN2ne
  have hcross : ‖V‖ * A1 * N2 = ‖U‖ * B1 * N1 := by
    have hkey := hcos
    have hv2 : N2 * ‖V‖ ≠ 0 := by rw [mul_comm]; exact hv
    field_simp [hu, hv2] at hkey
    linear_combination hkey
  have hcrossSq : (‖V‖ * A1 * N2) ^ 2 = (‖U‖ * B1 * N1) ^ 2 := by rw [hcross]
  have e1 : A1 ^ 2 + s ^ 2 * G = c2 * N1 ^ 2 := by
    rw [hA1e, hGdef, hN1e]; ring
  have e2 : B1 ^ 2 + t ^ 2 * G = b2 * N2 ^ 2 := by
    rw [hB1e, hGdef, hN2e]; ring
  have hGeq : t ^ 2 * A1 ^ 2 - s ^ 2 * B1 ^ 2 = 0 := by
    have hmul : G * (t ^ 2 * A1 ^ 2 - s ^ 2 * B1 ^ 2) = 0 := by
      nlinarith [hcrossSq, e1, e2, hc2, hb2]
    rcases mul_eq_zero.mp hmul with h | h
    · exact absurd h hG
    · exact h
  have hsq : (t * A1) ^ 2 = (s * B1) ^ 2 := by
    have e3 : t ^ 2 * A1 ^ 2 = (t * A1) ^ 2 := by ring
    have e4 : s ^ 2 * B1 ^ 2 = (s * B1) ^ 2 := by ring
    linarith [hGeq, e3, e4]
  have htA1 : t * A1 = s * B1 := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact h
    · have hAB0 : 0 ≤ A1 * B1 := by
        have hPpos : 0 < ‖V‖ * N2 * ‖U‖ * N1 :=
          mul_pos (mul_pos (mul_pos (norm_pos_iff.mpr hVne) hN2pos) (norm_pos_iff.mpr hUne)) hN1pos
        have hprod : (A1 * B1) * (‖V‖ * N2 * ‖U‖ * N1) = (‖U‖ * B1 * N1) ^ 2 := by
          linear_combination (‖U‖ * B1 * N1) * hcross
        have hnum : 0 ≤ ‖V‖ * N2 * ‖U‖ * N1 * (A1 * B1) := by
          rw [mul_comm (‖V‖ * N2 * ‖U‖ * N1) (A1 * B1), hprod]
          exact sq_nonneg _
        exact nonneg_of_mul_nonneg_right hnum hPpos
      have hAB0' : A1 * B1 ≤ 0 := by
        have h1 : t * (A1 * B1) = -(s * B1 ^ 2) := by linear_combination B1 * h
        have h1le : t * (A1 * B1) ≤ 0 := by
          rw [h1]; exact neg_nonpos.mpr (mul_nonneg (le_of_lt hs) (sq_nonneg B1))
        have hrew : (t * (A1 * B1)) * t⁻¹ = A1 * B1 := by field_simp
        rw [← hrew]
        simpa using mul_le_mul_of_nonneg_right h1le (inv_nonneg.mpr (le_of_lt ht))
      have hABz : A1 * B1 = 0 := le_antisymm hAB0' hAB0
      have h2 : t * (A1 * B1) = -(s * B1 ^ 2) := by linear_combination B1 * h
      have h3 : s * B1 ^ 2 = 0 := by
        rw [hABz, mul_zero] at h2
        linarith [h2]
      have h4 : B1 ^ 2 = 0 := by
        rcases mul_eq_zero.mp h3 with h' | h'
        · exact absurd h' (ne_of_gt hs)
        · exact h'
      have hB1z : B1 = 0 := sq_eq_zero_iff.mp h4
      rw [hB1z] at h
      rw [hB1z]
      simpa using h
  have hfin : t * c2 = s * b2 := by
    rw [hA1e, hB1e] at htA1
    linear_combination htA1
  exact hfin.symm
  /- @proof-region region.target-node.session.af2c5472e5573d3f end -/
