import ProverJobs.real_main_theorem_e7f39350f194.Vocabulary
import ProverJobs.real_main_theorem_e7f39350f194.Base

open EuclideanGeometry

open EuclideanGeometry

set_option autoImplicit false in
theorem statopia_math_node_358362470_f6dd73c9 : ∀ (A B C L N Y : Plane) (a c s : ℝ)
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set Plane))
    (hL_eq : L = A + a • (B - A) + c • (C - A))
    (hN_eq : N = A + (1 / 2 : ℝ) • (C - A))
    (hY : Y = A + s • (C - A))
    (hInside : InsideTriangle B N C L)
    (ha : 0 < a) (ha1 : a < 1) (hc : 0 < c) (hc1 : c < 1) (hs : 0 < s) (hs1 : s < 1)
    (hbranch : c - (1 - a) * s > 0)
    (hangle : ∠ L B Y = ∠ L N C),
    0 < a + 2 * c - 1 ∧
      s * ‖C - A‖ ^ 2 * (a + 2 * c - 1)
        = 2 * inner ℝ (B - A) (B - A) * (a ^ 2 - a)
          + 4 * a * c * inner ℝ (B - A) (C - A)
          + ‖C - A‖ ^ 2 * c * (2 * c - 1) := by
  /- @proof-region region.target-node.session.3944afadd528f8b3 begin -/
  intro A B C L N Y a c s hABC hL_eq hN_eq hY hInside ha ha1 hc hc1 hs hs1 hbranch hangle
  have key : ∀ (X Y : Plane) (r t : ℝ), r • X + t • Y = 0 → r ≠ 0 → X = (-(t / r)) • Y := by
    intro X Y r t h h0
    have h1 : r • X = -(t • Y) := eq_neg_of_add_eq_zero_left h
    calc X = r⁻¹ • (r • X) := (inv_smul_smul₀ h0 X).symm
      _ = r⁻¹ • (-(t • Y)) := by rw [h1]
      _ = -(r⁻¹ • (t • Y)) := by rw [smul_neg]
      _ = -((r⁻¹ * t) • Y) := by rw [← mul_smul]
      _ = (-(t / r)) • Y := by rw [neg_smul, div_eq_mul_inv, mul_comm t r⁻¹]
  have coll2 : ∀ k : ℝ, B - A = k • (C - A) → Collinear ℝ ({A, B, C} : Set Plane) := by
    intro k hk
    refine (collinear_iff_of_mem (show A ∈ ({A, B, C} : Set Plane) by simp)).mpr ?_
    refine ⟨C - A, ?_⟩
    intro Pt hPt
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hPt
    rcases hPt with hPt | hPt | hPt
    · exact ⟨0, by rw [hPt, zero_smul, zero_vadd]⟩
    · exact ⟨k, by rw [hPt, ← hk]; exact (vsub_vadd B A).symm⟩
    · exact ⟨1, by rw [hPt, one_smul]; exact (vsub_vadd C A).symm⟩
  have coll3 : ∀ k : ℝ, C - A = k • (B - A) → Collinear ℝ ({A, B, C} : Set Plane) := by
    intro k hk
    refine (collinear_iff_of_mem (show A ∈ ({A, B, C} : Set Plane) by simp)).mpr ?_
    refine ⟨B - A, ?_⟩
    intro Pt hPt
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hPt
    rcases hPt with hPt | hPt | hPt
    · exact ⟨0, by rw [hPt, zero_smul, zero_vadd]⟩
    · exact ⟨1, by rw [hPt, one_smul]; exact (vsub_vadd B A).symm⟩
    · exact ⟨k, by rw [hPt, ← hk]; exact (vsub_vadd C A).symm⟩
  have hpair : ∀ r t : ℝ, r • (B - A) + t • (C - A) = 0 → r = 0 ∧ t = 0 := by
    intro r t h
    by_cases hr : r = 0
    · by_cases ht : t = 0
      · exact ⟨hr, ht⟩
      · exfalso
        have h1 : t • (C - A) = 0 := by simpa [hr] using h
        have h2 : C - A = 0 := (smul_eq_zero.mp h1).resolve_left ht
        exact hABC (coll3 0 (by rw [h2, zero_smul]))
    · have hb : B - A = (-(t / r)) • (C - A) := key (B - A) (C - A) r t h hr
      exact absurd (coll2 (-(t / r)) hb) hABC
  have hPne : B - A ≠ 0 := by
    intro h0
    exact one_ne_zero (hpair 1 0 (by simp [h0])).1
  have hQne : C - A ≠ 0 := by
    intro h0
    exact one_ne_zero (hpair 0 1 (by simp [h0])).2
  have bil : ∀ (α β γ δ : ℝ),
      inner ℝ (α • (B - A) + β • (C - A)) (γ • (B - A) + δ • (C - A))
        = α * γ * inner ℝ (B - A) (B - A)
          + (α * δ + β * γ) * inner ℝ (B - A) (C - A)
          + β * δ * inner ℝ (C - A) (C - A) := by
    intro α β γ δ
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      RCLike.conj_to_real, real_inner_comm (B - A) (C - A)]
    ring
  have nrm2 : ∀ (α β : ℝ),
      ‖α • (B - A) + β • (C - A)‖ ^ 2
        = α * α * inner ℝ (B - A) (B - A)
          + 2 * (α * β) * inner ℝ (B - A) (C - A)
          + β * β * inner ℝ (C - A) (C - A) := by
    intro α β
    rw [← real_inner_self_eq_norm_sq (α • (B - A) + β • (C - A)), bil α β α β]
    ring
  have lag : ∀ (α β γ δ : ℝ),
      ‖α • (B - A) + β • (C - A)‖ ^ 2 * ‖γ • (B - A) + δ • (C - A)‖ ^ 2
        - inner ℝ (α • (B - A) + β • (C - A)) (γ • (B - A) + δ • (C - A)) ^ 2
        = (α * δ - β * γ) ^ 2
          * (inner ℝ (B - A) (B - A) * inner ℝ (C - A) (C - A)
              - inner ℝ (B - A) (C - A) ^ 2) := by
    intro α β γ δ
    rw [nrm2 α β, nrm2 γ δ, bil α β γ δ]
    ring
  have hDpos : 0 < inner ℝ (B - A) (B - A) * inner ℝ (C - A) (C - A)
      - inner ℝ (B - A) (C - A) ^ 2 := by
    have hgpos : 0 < inner ℝ (B - A) (B - A) := by
      rw [real_inner_self_eq_norm_sq]
      exact pow_pos (norm_pos_iff.mpr hPne) 2
    have hgne : inner ℝ (B - A) (B - A) ≠ 0 := ne_of_gt hgpos
    have hw : (-(inner ℝ (B - A) (C - A) / inner ℝ (B - A) (B - A))) • (B - A)
        + (1 : ℝ) • (C - A) ≠ 0 := by
      intro h0
      exact one_ne_zero (hpair _ _ h0).2
    have hww : 0 < inner ℝ
        ((-(inner ℝ (B - A) (C - A) / inner ℝ (B - A) (B - A))) • (B - A) + (1 : ℝ) • (C - A))
        ((-(inner ℝ (B - A) (C - A) / inner ℝ (B - A) (B - A))) • (B - A) + (1 : ℝ) • (C - A)) := by
      rw [real_inner_self_eq_norm_sq]
      exact pow_pos (norm_pos_iff.mpr hw) 2
    have hexp : inner ℝ (B - A) (B - A) * inner ℝ
        ((-(inner ℝ (B - A) (C - A) / inner ℝ (B - A) (B - A))) • (B - A) + (1 : ℝ) • (C - A))
        ((-(inner ℝ (B - A) (C - A) / inner ℝ (B - A) (B - A))) • (B - A) + (1 : ℝ) • (C - A))
        = inner ℝ (B - A) (B - A) * inner ℝ (C - A) (C - A)
          - inner ℝ (B - A) (C - A) ^ 2 := by
      rw [bil (-(inner ℝ (B - A) (C - A) / inner ℝ (B - A) (B - A))) 1
        (-(inner ℝ (B - A) (C - A) / inner ℝ (B - A) (B - A))) 1]
      field_simp
      ring
    rw [← hexp]
    exact mul_pos hgpos hww
  obtain ⟨α, β, γ, hα0, hβ0, hγ0, hsum, hP⟩ := hInside
  have hpt : α • B + β • N + γ • C = A + a • (B - A) + c • (C - A) := by
    rw [← hL_eq, ← hP]
  have hNA : N - A = (1 / 2 : ℝ) • (C - A) := by
    rw [hN_eq]
    abel
  have hAeq : A = (α + β + γ) • A := by
    rw [hsum]
    simp
  have hLv : (α • B + β • N + γ • C) - A
      = α • (B - A) + β • (N - A) + γ • (C - A) := by
    conv_lhs => rw [hAeq, add_smul, add_smul]
    simp only [smul_sub]
    abel
  have hRv : (A + a • (B - A) + c • (C - A)) - A = a • (B - A) + c • (C - A) := by
    simp only [smul_sub]
    abel
  have hptm : (α • B + β • N + γ • C) - A = (A + a • (B - A) + c • (C - A)) - A := by
    rw [hpt]
  have hvec : α • (B - A) + β • (N - A) + γ • (C - A) = a • (B - A) + c • (C - A) := by
    rw [← hLv, hptm, hRv]
  have hb2 : β • (N - A) = (β * (1 / 2)) • (C - A) := by
    rw [hNA, ← mul_smul]
  have hdiff : (α - a) • (B - A) + (β * (1 / 2) + γ - c) • (C - A)
      = (α • (B - A) + β • (N - A) + γ • (C - A)) - (a • (B - A) + c • (C - A)) := by
    rw [sub_smul, sub_smul, add_smul, ← hb2]
    abel
  have hkey : (α - a) • (B - A) + (β * (1 / 2) + γ - c) • (C - A) = 0 := by
    rw [hdiff, hvec]
    abel
  have hcomp1 : α - a = 0 := (hpair (α - a) (β * (1 / 2) + γ - c) hkey).1
  have hcomp2 : β * (1 / 2) + γ - c = 0 := (hpair (α - a) (β * (1 / 2) + γ - c) hkey).2
  have hαa : α = a := by linarith [hcomp1]
  have hβγc : β * (1 / 2) + γ = c := by linarith [hcomp2]
  have hga : 0 < a + 2 * c - 1 := by
    have hres : a + 2 * c - 1 = γ := by
      rw [← hαa, ← hβγc]
      linarith [hsum]
    rw [hres]
    exact hγ0
  refine ⟨hga, ?_⟩
  have hBv : B = A + (B - A) := by abel
  have hCv : C = A + (C - A) := by abel
  have hu1 : L - B = (a - 1) • (B - A) + c • (C - A) := by
    have e : (A + a • (B - A) + c • (C - A)) - (A + (B - A))
        = (a - 1) • (B - A) + c • (C - A) := by
      rw [sub_smul, one_smul]
      abel
    rw [← hL_eq, ← hBv] at e
    exact e
  have hv1 : Y - B = (-1 : ℝ) • (B - A) + s • (C - A) := by
    have e : (A + s • (C - A)) - (A + (B - A))
        = (-1 : ℝ) • (B - A) + s • (C - A) := by
      rw [neg_smul, one_smul]
      abel
    rw [← hY, ← hBv] at e
    exact e
  have hu2 : L - N = a • (B - A) + (c - 1 / 2) • (C - A) := by
    have e : (A + a • (B - A) + c • (C - A)) - (A + (1 / 2 : ℝ) • (C - A))
        = a • (B - A) + (c - 1 / 2) • (C - A) := by
      rw [sub_smul]
      abel
    rw [← hL_eq, ← hN_eq] at e
    exact e
  have hqq : (C - A) - (1 / 2 : ℝ) • (C - A) = (1 / 2 : ℝ) • (C - A) := by
    calc (C - A) - (1 / 2 : ℝ) • (C - A)
        = (1 : ℝ) • (C - A) - (1 / 2 : ℝ) • (C - A) := by rw [one_smul]
      _ = (1 - 1 / 2 : ℝ) • (C - A) := (sub_smul 1 (1 / 2) (C - A)).symm
      _ = (1 / 2 : ℝ) • (C - A) := by rw [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num]
  have hv2 : C - N = (1 / 2 : ℝ) • (C - A) := by
    have hstep : (A + (C - A)) - (A + (1 / 2 : ℝ) • (C - A))
        = (C - A) - (1 / 2 : ℝ) • (C - A) := by abel
    have e : (A + (C - A)) - (A + (1 / 2 : ℝ) • (C - A)) = (1 / 2 : ℝ) • (C - A) :=
      hstep.trans hqq
    rw [← hCv, ← hN_eq] at e
    exact e
  have hv2' : C - N = (0 : ℝ) • (B - A) + (1 / 2 : ℝ) • (C - A) := by
    simpa using hv2
  have hu1ne : L - B ≠ 0 := by
    intro h0
    have h1 : (a - 1) • (B - A) + c • (C - A) = 0 := by
      rw [← hu1]
      exact h0
    have h2 : a - 1 = 0 := (hpair (a - 1) c h1).1
    linarith
  have hv1ne : Y - B ≠ 0 := by
    intro h0
    have h1 : (-1 : ℝ) • (B - A) + s • (C - A) = 0 := by
      rw [← hv1]
      exact h0
    have h2 : s = 0 := (hpair (-1) s h1).2
    linarith
  have hu2ne : L - N ≠ 0 := by
    intro h0
    have h1 : a • (B - A) + (c - 1 / 2) • (C - A) = 0 := by
      rw [← hu2]
      exact h0
    have h2 : a = 0 := (hpair a (c - 1 / 2) h1).1
    linarith
  have hv2ne : C - N ≠ 0 := by
    intro h0
    have h1 : (0 : ℝ) • (B - A) + (1 / 2 : ℝ) • (C - A) = 0 := hv2'.symm.trans h0
    have h2 : (1 / 2 : ℝ) = 0 := (hpair 0 (1 / 2) h1).2
    linarith
  have hbnd : ∀ x y : Plane, x ≠ 0 → y ≠ 0 →
      -1 ≤ inner ℝ x y / (‖x‖ * ‖y‖) ∧ inner ℝ x y / (‖x‖ * ‖y‖) ≤ 1 := by
    intro x y hx hy
    have hp : 0 < ‖x‖ * ‖y‖ := mul_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hy)
    have hb : |inner ℝ x y / (‖x‖ * ‖y‖)| ≤ 1 := by
      rw [abs_div, abs_of_pos hp, div_le_one hp]
      exact abs_real_inner_le_norm x y
    exact abs_le.mp hb
  have hb1 := hbnd (L - B) (Y - B) hu1ne hv1ne
  have hb2 := hbnd (L - N) (C - N) hu2ne hv2ne
  have hcos : Real.cos (∠ L B Y) = Real.cos (∠ L N C) := by rw [hangle]
  have hcosX : Real.cos (∠ L B Y)
      = inner ℝ (L - B) (Y - B) / (‖L - B‖ * ‖Y - B‖) := by
    simp only [EuclideanGeometry.angle, InnerProductGeometry.angle]
    exact Real.cos_arccos hb1.1 hb1.2
  have hcosY : Real.cos (∠ L N C)
      = inner ℝ (L - N) (C - N) / (‖L - N‖ * ‖C - N‖) := by
    simp only [EuclideanGeometry.angle, InnerProductGeometry.angle]
    exact Real.cos_arccos hb2.1 hb2.2
  have hcos2 : inner ℝ (L - B) (Y - B) / (‖L - B‖ * ‖Y - B‖)
      = inner ℝ (L - N) (C - N) / (‖L - N‖ * ‖C - N‖) := by
    rw [← hcosX, ← hcosY, hcos]
  have hXeq : inner ℝ (L - B) (Y - B)
      = ((1 - a) * inner ℝ (B - A) (B - A) - c * inner ℝ (B - A) (C - A))
        + ((a - 1) * inner ℝ (B - A) (C - A) + c * inner ℝ (C - A) (C - A)) * s := by
    rw [hu1, hv1, bil (a - 1) c (-1) s]
    ring
  have hY2eq : inner ℝ (L - N) (C - N)
      = (a * inner ℝ (B - A) (C - A) + (c - 1 / 2) * inner ℝ (C - A) (C - A)) / 2 := by
    rw [hu2, hv2', bil a (c - 1 / 2) 0 (1 / 2)]
    ring
  have hn1pos : 0 < ‖L - B‖ * ‖Y - B‖ :=
    mul_pos (norm_pos_iff.mpr hu1ne) (norm_pos_iff.mpr hv1ne)
  have hn2pos : 0 < ‖L - N‖ * ‖C - N‖ :=
    mul_pos (norm_pos_iff.mpr hu2ne) (norm_pos_iff.mpr hv2ne)
  have hcross : inner ℝ (L - B) (Y - B) * (‖L - N‖ * ‖C - N‖)
      = inner ℝ (L - N) (C - N) * (‖L - B‖ * ‖Y - B‖) :=
    (div_eq_div_iff (ne_of_gt hn1pos) (ne_of_gt hn2pos)).mp hcos2
  have hnorm1 : (‖L - B‖ * ‖Y - B‖) ^ 2
      = (inner ℝ (L - B) (Y - B)) ^ 2
        + ((a - 1) * s + c) ^ 2
          * (inner ℝ (B - A) (B - A) * inner ℝ (C - A) (C - A)
              - inner ℝ (B - A) (C - A) ^ 2) := by
    rw [mul_pow, hu1, hv1]
    have hl := lag (a - 1) c (-1) s
    have hl2 : ((a - 1) * s - c * (-1)) ^ 2
        * (inner ℝ (B - A) (B - A) * inner ℝ (C - A) (C - A)
            - inner ℝ (B - A) (C - A) ^ 2)
        = ((a - 1) * s + c) ^ 2
          * (inner ℝ (B - A) (B - A) * inner ℝ (C - A) (C - A)
              - inner ℝ (B - A) (C - A) ^ 2) := by ring
    linear_combination hl + hl2
  have hnorm2 : (‖L - N‖ * ‖C - N‖) ^ 2
      = (inner ℝ (L - N) (C - N)) ^ 2
        + (a / 2) ^ 2
          * (inner ℝ (B - A) (B - A) * inner ℝ (C - A) (C - A)
              - inner ℝ (B - A) (C - A) ^ 2) := by
    rw [mul_pow, hu2, hv2']
    have hl := lag a (c - 1 / 2) 0 (1 / 2)
    have hl2 : (a * (1 / 2) - (c - 1 / 2) * 0) ^ 2
        * (inner ℝ (B - A) (B - A) * inner ℝ (C - A) (C - A)
            - inner ℝ (B - A) (C - A) ^ 2)
        = (a / 2) ^ 2
          * (inner ℝ (B - A) (B - A) * inner ℝ (C - A) (C - A)
              - inner ℝ (B - A) (C - A) ^ 2) := by ring
    linear_combination hl + hl2
  have hsq : (inner ℝ (L - B) (Y - B)) ^ 2 * (‖L - N‖ * ‖C - N‖) ^ 2
      = (inner ℝ (L - N) (C - N)) ^ 2 * (‖L - B‖ * ‖Y - B‖) ^ 2 := by
    have h := congrArg (fun t : ℝ => t ^ 2) hcross
    simpa only [mul_pow] using h
  have hmid : (inner ℝ (L - B) (Y - B)) ^ 2 * (a / 2) ^ 2
      = ((a - 1) * s + c) ^ 2 * (inner ℝ (L - N) (C - N)) ^ 2 := by
    have h1 := hsq
    rw [hnorm1, hnorm2] at h1
    have h2 : (inner ℝ (L - B) (Y - B)) ^ 2 * (a / 2) ^ 2
        * (inner ℝ (B - A) (B - A) * inner ℝ (C - A) (C - A)
            - inner ℝ (B - A) (C - A) ^ 2)
        = ((a - 1) * s + c) ^ 2 * (inner ℝ (L - N) (C - N)) ^ 2
          * (inner ℝ (B - A) (B - A) * inner ℝ (C - A) (C - A)
              - inner ℝ (B - A) (C - A) ^ 2) := by
      linear_combination h1
    exact mul_right_cancel₀ (ne_of_gt hDpos) h2
  have hsq3 : (a * inner ℝ (L - B) (Y - B)) ^ 2
      = (2 * ((a - 1) * s + c) * inner ℝ (L - N) (C - N)) ^ 2 := by
    linear_combination 4 * hmid
  have hkpos : 0 < (a - 1) * s + c := by
    have h : (a - 1) * s + c = c - (1 - a) * s := by ring
    linarith [hbranch, h]
  have hXY : 0 ≤ inner ℝ (L - B) (Y - B) * inner ℝ (L - N) (C - N) := by
    have hnn : 0 ≤ (inner ℝ (L - N) (C - N)) ^ 2 * (‖L - B‖ * ‖Y - B‖) :=
      mul_nonneg (sq_nonneg _) (le_of_lt hn1pos)
    have h1 : inner ℝ (L - B) (Y - B) * (‖L - N‖ * ‖C - N‖) * inner ℝ (L - N) (C - N)
        = (inner ℝ (L - N) (C - N)) ^ 2 * (‖L - B‖ * ‖Y - B‖) := by
      rw [hcross]
      ring
    have h3 : 0 ≤ inner ℝ (L - B) (Y - B) * (‖L - N‖ * ‖C - N‖) * inner ℝ (L - N) (C - N) := by
      rw [h1]
      exact hnn
    have h4 : 0 ≤ (‖L - N‖ * ‖C - N‖)
        * (inner ℝ (L - B) (Y - B) * inner ℝ (L - N) (C - N)) := by
      have e : (‖L - N‖ * ‖C - N‖)
          * (inner ℝ (L - B) (Y - B) * inner ℝ (L - N) (C - N))
          = inner ℝ (L - B) (Y - B) * (‖L - N‖ * ‖C - N‖) * inner ℝ (L - N) (C - N) := by
        ring
      rw [e]
      exact h3
    exact nonneg_of_mul_nonneg_right h4 hn2pos
  have hsign : 0 ≤ (a * inner ℝ (L - B) (Y - B))
      * (2 * ((a - 1) * s + c) * inner ℝ (L - N) (C - N)) := by
    have h0 : 0 ≤ (2 * ((a - 1) * s + c) * a)
        * (inner ℝ (L - B) (Y - B) * inner ℝ (L - N) (C - N)) :=
      mul_nonneg (mul_nonneg (by linarith [hkpos]) (le_of_lt ha)) hXY
    have e : (a * inner ℝ (L - B) (Y - B))
        * (2 * ((a - 1) * s + c) * inner ℝ (L - N) (C - N))
        = (2 * ((a - 1) * s + c) * a)
          * (inner ℝ (L - B) (Y - B) * inner ℝ (L - N) (C - N)) := by ring
    rw [e]
    exact h0
  have hsel : a * inner ℝ (L - B) (Y - B)
      = 2 * ((a - 1) * s + c) * inner ℝ (L - N) (C - N) := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq3 with h | h
    · exact h
    · have h1 : 0 ≤ -((2 * ((a - 1) * s + c) * inner ℝ (L - N) (C - N)) ^ 2) := by
        have hh : (-(2 * ((a - 1) * s + c) * inner ℝ (L - N) (C - N)))
            * (2 * ((a - 1) * s + c) * inner ℝ (L - N) (C - N))
            = -((2 * ((a - 1) * s + c) * inner ℝ (L - N) (C - N)) ^ 2) := by ring
        rw [← hh, ← h]
        exact hsign
      have hz : (2 * ((a - 1) * s + c) * inner ℝ (L - N) (C - N)) ^ 2 = 0 := by
        linarith [h1, sq_nonneg (2 * ((a - 1) * s + c) * inner ℝ (L - N) (C - N))]
      have hz2 : (2 * ((a - 1) * s + c) * inner ℝ (L - N) (C - N))
          * (2 * ((a - 1) * s + c) * inner ℝ (L - N) (C - N)) = 0 := by
        rw [← pow_two]
        exact hz
      have hz' : 2 * ((a - 1) * s + c) * inner ℝ (L - N) (C - N) = 0 :=
        (mul_eq_zero.mp hz2).elim id id
      linarith [h, hz']
  rw [hXeq, hY2eq] at hsel
  rw [← real_inner_self_eq_norm_sq (C - A)]
  linear_combination 2 * hsel
  /- @proof-region region.target-node.session.3944afadd528f8b3 end -/
