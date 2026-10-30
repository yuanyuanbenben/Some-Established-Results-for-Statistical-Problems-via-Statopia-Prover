import ProverJobs.real_main_theorem_e7f39350f194.Vocabulary
import ProverJobs.real_main_theorem_e7f39350f194.Base

open EuclideanGeometry

open EuclideanGeometry

set_option autoImplicit false in
theorem statopia_math_node_1641763193_b67e03b9 : ∀ (A B C N L X : Plane) (t v : ℝ)
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set Plane))
    (hN : N = midpoint ℝ A C)
    (hL : InsideTriangle B N C L)
    (hX : X = A + t • (B - A))
    (hLtrace : L = C + v • (X - C)),
    ∃ U : Plane, ∃ r2 : ℝ,
      (‖B - U‖ ^ 2 - r2 = 0) ∧
        (‖L - U‖ ^ 2 - r2 = 0) ∧
          (‖N - U‖ ^ 2 - r2 = 0) := by
  /- @proof-region region.target-node.session.eadc8d2b929441e5 begin -/
  intro A B C N L X t v hABC hN hL hX hLtrace
  obtain ⟨α, β, γ, hα, hβ, hγ, hsum, hLdef⟩ := hL
  have hrange : Set.range ![A, B, C] = ({A, B, C} : Set Plane) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
  have hAI : AffineIndependent ℝ ![A, B, C] := by
    by_contra h
    exact hABC (hrange ▸ ((show Collinear ℝ (Set.range ![A, B, C]) ↔
      ¬ AffineIndependent ℝ ![A, B, C] from collinear_iff_not_affineIndependent).mpr h))
  have hLI3 : LinearIndependent ℝ
      (fun i : {x : Fin 3 // x ≠ 0} => ![A, B, C] i.1 -ᵥ ![A, B, C] (0 : Fin 3)) :=
    (affineIndependent_iff_linearIndependent_vsub ℝ ![A, B, C] (0 : Fin 3)).mp hAI
  have hLIpq0 : LinearIndependent ℝ ![B - A, C - A] := by
    have h3 : LinearIndependent ℝ (fun i : {x : Fin 3 // x ≠ 0} => ![A, B, C] i.1 - A) := by
      simpa [vsub_eq_sub] using hLI3
    have hf : Function.Injective
        (fun i : Fin 2 =>
          (⟨![(1 : Fin 3), 2] i, by fin_cases i <;> decide⟩ : {x : Fin 3 // x ≠ 0})) := by
      intro a b hab
      have h : ![(1 : Fin 3), 2] a = ![(1 : Fin 3), 2] b := congrArg Subtype.val hab
      fin_cases a <;> fin_cases b <;> simp_all
    have h2 := h3.comp
      (fun i : Fin 2 =>
        (⟨![(1 : Fin 3), 2] i, by fin_cases i <;> decide⟩ : {x : Fin 3 // x ≠ 0})) hf
    have h2' : LinearIndependent ℝ (fun i : Fin 2 => ![A, B, C] (![(1 : Fin 3), 2] i) - A) := by
      simpa [Function.comp] using h2
    have hfun : (fun i : Fin 2 => ![A, B, C] (![(1 : Fin 3), 2] i) - A) = ![B - A, C - A] := by
      funext i
      fin_cases i <;> simp
    rw [hfun] at h2'
    exact h2'
  set p : Plane := B - A with hp
  set q : Plane := C - A with hq
  have hLIpq : LinearIndependent ℝ ![p, q] := by
    rw [hp, hq]
    exact hLIpq0
  have hpq : ∀ a b : ℝ, a • p + b • q = 0 → a = 0 ∧ b = 0 :=
    (show LinearIndependent ℝ ![p, q] ↔ ∀ s t : ℝ, s • p + t • q = 0 → s = 0 ∧ t = 0 from
      LinearIndependent.pair_iff).mp hLIpq
  have gram_ne : ∀ x y : Plane, LinearIndependent ℝ ![x, y] →
      inner ℝ x x * inner ℝ y y - inner ℝ x y * inner ℝ x y ≠ 0 := by
    intro x y hxy hzero
    have hcrit : ∀ s t : ℝ, s • x + t • y = 0 → s = 0 ∧ t = 0 :=
      (show LinearIndependent ℝ ![x, y] ↔ ∀ s t : ℝ, s • x + t • y = 0 → s = 0 ∧ t = 0 from
        LinearIndependent.pair_iff).mp hxy
    by_cases hxx : inner ℝ x x = 0
    · have hx0 : x = 0 := by
        have h1 : ‖x‖ ^ 2 = 0 := by
          rw [← real_inner_self_eq_norm_sq]
          exact hxx
        exact norm_eq_zero.mp (sq_eq_zero_iff.mp h1)
      exact one_ne_zero (hcrit 1 0 (by rw [hx0]; simp)).1
    · set r : ℝ := inner ℝ x y / inner ℝ x x with hr
      set z : Plane := y - r • x with hz
      have hz0 : z = 0 := by
        have hgoal : inner ℝ z z
            = (inner ℝ x x * inner ℝ y y - inner ℝ x y * inner ℝ x y) / inner ℝ x x := by
          have hyx : inner ℝ y x = inner ℝ x y := real_inner_comm x y
          rw [hz, hr]
          simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
            real_inner_smul_right, hyx]
          field_simp
          ring
        have hzz : inner ℝ z z = 0 := by
          rw [hgoal, hzero]
          simp
        have h1 : ‖z‖ ^ 2 = 0 := by
          rw [← real_inner_self_eq_norm_sq]
          exact hzz
        exact norm_eq_zero.mp (sq_eq_zero_iff.mp h1)
      have hy : y = r • x := by
        have h := hz0
        rw [hz] at h
        exact sub_eq_zero.mp h
      exact one_ne_zero (hcrit (-r) 1
        (by rw [hy, one_smul, ← add_smul, neg_add_cancel, zero_smul])).2
  have hA : A = B - p := by rw [hp]; abel
  have hB0 : B = A + p := by rw [hp]; abel
  have hC0 : C = A + q := by rw [hq]; abel
  have hC' : C = B - p + q := by rw [hC0, hA]
  have h2inv : (2 : ℝ) * ⅟(2 : ℝ) = 1 := by simp
  have h2inv' : (2 : ℝ) * ⅟(2 : ℝ) = 1 := Invertible.mul_invOf_self
  have h2inv'' : (⅟(2 : ℝ) : ℝ) = (2 : ℝ)⁻¹ := invOf_eq_inv (2 : ℝ)
  have hmid2 : (2 : ℝ) • N = A + C := by
    rw [hN, midpoint_eq_smul_add ℝ A C, smul_smul, h2inv, one_smul]
  have hXp : X = A + t • p := by rw [hX, hp]
  have hXC : X - C = t • p - q := by
    rw [hXp, hC0]
    abel
  have hL1 : L = A + (v * t) • p + (1 - v) • q := by
    rw [hLtrace, hXC, hC0]
    simp only [smul_sub, smul_smul, sub_smul, one_smul]
    abel
  set u : Plane := L - B with hu_def
  set W : Plane := (2 : ℝ) • (N - B) with hW_def
  have hu : u = (v * t - 1) • p + (1 - v) • q := by
    rw [hu_def, hL1, hB0]
    simp only [sub_smul, one_smul]
    abel
  have hW : W = (-2 : ℝ) • p + q := by
    rw [hW_def, smul_sub, hmid2, hA, hC']
    simp only [two_smul, neg_smul]
    abel
  have hu2 : u = β • (N - B) + γ • (C - B) := by
    have hB1 : B = (α + β + γ) • B := by rw [hsum, one_smul]
    rw [hu_def, hLdef]
    exact (congrArg (fun z => α • B + β • N + γ • C - z) hB1).trans (by
      simp only [smul_sub, add_smul]
      abel)
  have h2Nc : (2 : ℝ) • (N - C) = -q := by
    rw [smul_sub, hmid2]
    rw [show (A + C) - (2 : ℝ) • C = A - C from by rw [two_smul]; abel]
    rw [show A - C = -q from by rw [hq]; abel]
  have hBC : B - C = p - q := by rw [hB0, hC0]; abel
  have hLCa : (2 : ℝ) • (L - C) = (2 * v * t) • p - (2 * v) • q := by
    have hLC'' : L - C = v • (X - C) := by rw [hLtrace]; abel
    calc (2 : ℝ) • (L - C)
        = (2 : ℝ) • (v • (X - C)) := by rw [hLC'']
      _ = (2 * v) • (X - C) := by rw [smul_smul]
      _ = (2 * v) • (t • p - q) := by rw [hXC]
      _ = (2 * v * t) • p - (2 * v) • q := by simp only [smul_sub, smul_smul]
  have hLCb : (2 : ℝ) • (L - C) = (2 * α) • p - (2 * α + β) • q := by
    have hLC' : L - C = α • (B - C) + β • (N - C) := by
      have hC1 : C = (α + β + γ) • C := by rw [hsum, one_smul]
      rw [hLdef]
      exact (congrArg (fun z => α • B + β • N + γ • C - z) hC1).trans (by
        simp only [smul_sub, add_smul]
        abel)
    calc (2 : ℝ) • (L - C)
        = (2 : ℝ) • (α • (B - C) + β • (N - C)) := by rw [hLC']
      _ = (2 * α) • (B - C) + (2 * β) • (N - C) := by simp only [smul_add, smul_smul]
      _ = (2 * α) • (B - C) + β • ((2 : ℝ) • (N - C)) := by
            rw [show (2 : ℝ) * β = β * 2 from by ring]
            rw [smul_smul]
      _ = (2 * α) • (B - C) + β • (-q) := by rw [h2Nc]
      _ = (2 * α) • p - (2 * α + β) • q := by
            rw [hBC]
            simp only [smul_sub, sub_smul, smul_neg, neg_smul, smul_add, add_smul, one_smul]
            abel
  have hz : (2 * v * t - 2 * α) • p + (-(2 * v) + (2 * α + β)) • q = 0 := by
    have hEq : (2 * v * t) • p - (2 * v) • q = (2 * α) • p - (2 * α + β) • q :=
      hLCa.symm.trans hLCb
    have hsub : ((2 * v * t) • p - (2 * v) • q) - ((2 * α) • p - (2 * α + β) • q) = 0 :=
      sub_eq_zero.mpr hEq
    rw [← hsub]
    simp only [sub_smul, neg_smul, add_smul, smul_sub]
    abel
  have h1 : 2 * v * t - 2 * α = 0 := (hpq _ _ hz).1
  have h2 : -(2 * v) + (2 * α + β) = 0 := (hpq _ _ hz).2
  have hdet : v * t + 1 - 2 * v = γ := by linarith
  have hLIuW : LinearIndependent ℝ ![u, W] := by
    rw [show LinearIndependent ℝ ![u, W] ↔
      ∀ s b : ℝ, s • u + b • W = 0 → s = 0 ∧ b = 0 from LinearIndependent.pair_iff]
    intro s b hst
    have hvec : s • u + b • W
        = (s * (v * t - 1) + b * (-2)) • p + (s * (1 - v) + b) • q := by
      calc s • u + b • W
          = (s * (v * t - 1)) • p + (s * (1 - v)) • q + ((b * (-2)) • p + b • q) := by
              rw [hu, hW]
              simp only [smul_add, smul_smul]
        _ = ((s * (v * t - 1)) • p + (b * (-2)) • p) + ((s * (1 - v)) • q + b • q) := by
              abel
        _ = (s * (v * t - 1) + b * (-2)) • p + (s * (1 - v) + b) • q := by
              rw [← add_smul, ← add_smul]
    rw [hvec] at hst
    have h1' : s * (v * t - 1) + b * (-2) = 0 := (hpq _ _ hst).1
    have h2' : s * (1 - v) + b = 0 := (hpq _ _ hst).2
    have hs : s * (v * t + 1 - 2 * v) = 0 := by linear_combination h1' + 2 * h2'
    have hdetne : v * t + 1 - 2 * v ≠ 0 := by rw [hdet]; exact ne_of_gt hγ
    have hs0 : s = 0 := (mul_eq_zero.mp hs).resolve_right hdetne
    refine ⟨hs0, ?_⟩
    rw [hs0] at h2'
    simpa using h2'
  have hgram : inner ℝ u u * inner ℝ W W - inner ℝ u W * inner ℝ u W ≠ 0 :=
    gram_ne u W hLIuW
  set c1 : ℝ := (‖L‖ ^ 2 - ‖B‖ ^ 2) / 2 with hc1
  set cW : ℝ := ‖N‖ ^ 2 - ‖B‖ ^ 2 with hcW
  set Δ : ℝ := inner ℝ u u * inner ℝ W W - inner ℝ u W * inner ℝ u W with hΔ
  have hΔne : Δ ≠ 0 := by rw [hΔ]; exact hgram
  set U : Plane := ((c1 * inner ℝ W W - cW * inner ℝ u W) / Δ) • u
    + ((cW * inner ℝ u u - c1 * inner ℝ u W) / Δ) • W with hU
  have hUu : inner ℝ u U = c1 := by
    rw [hU]
    simp only [inner_add_right, real_inner_smul_right]
    field_simp [hΔne]
    rw [hΔ]
    ring
  have hUW : inner ℝ W U = cW := by
    have hwu : inner ℝ W u = inner ℝ u W := (real_inner_comm W u).symm
    rw [hU]
    simp only [inner_add_right, real_inner_smul_right, hwu]
    field_simp [hΔne]
    rw [hΔ]
    ring
  refine ⟨U, ‖B - U‖ ^ 2, ?_, ?_, ?_⟩
  · ring
  · have hLU := norm_sub_sq_real L U
    have hBU := norm_sub_sq_real B U
    have hiu : inner ℝ L U - inner ℝ B U = c1 := by
      rw [← inner_sub_left, ← hu_def]
      exact hUu
    linarith [hLU, hBU, hiu, hc1]
  · have hNU := norm_sub_sq_real N U
    have hBU := norm_sub_sq_real B U
    have h2m : (2 : ℝ) * (inner ℝ N U - inner ℝ B U) = cW := by
      rw [← inner_sub_left]
      rw [← real_inner_smul_left, ← hW_def]
      exact hUW
    linarith [hNU, hBU, h2m, hcW]
  /- @proof-region region.target-node.session.eadc8d2b929441e5 end -/
